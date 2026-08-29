signature LSPServer =
sig
  val start : {diag: string -> unit, dbg: bool} -> unit
end;

(* load "JSONDecode"; *)

structure LSPServer :> LSPServer =
struct

(* structure Thread = PolyThread; *)
open Thread LSPExtension

fun I x = x
fun leLC (l,c) (l',c') = l <= l' andalso (l <> l' orelse c <= c')

type encode = (string -> unit) -> unit
fun encOut str: encode = fn print => print str
val encNull = encOut "null"
fun encInt x = if x < 0 then encOut ("-" ^ Int.toString (~x)) else encOut (Int.toString x)

local

fun encodeSubstring {str, start, stop} print = let
  fun cleanup start i =
    if start < i then print (String.substring (str, start, i - start)) else ()
  fun hexdigit n = Char.chr (n + (if n < 10 then 48 else 55))
  fun inner start i =
    if i >= stop then cleanup start i
    else
      let val c = String.sub (str, i) in
        if #" " <= c then
          if c = #"\\" then breakStreak start i "\\\\" else
          if c = #"\"" then breakStreak start i "\\\"" else
          inner start (i+1)
        else breakStreak start i (case c of
            #"\b" => "\\b"
          | #"\f" => "\\f"
          | #"\n" => "\\n"
          | #"\r" => "\\r"
          | #"\t" => "\\t"
          | _ => let
            val n = Char.ord c
            in "\\u00" ^ String.implode [hexdigit (n div 16), hexdigit (n mod 16)] end)
      end
  and breakStreak start i next = (cleanup start i; print next; inner (i+1) (i+1))
  in inner start start end

in

(* fun encSubstringContents str = let
  val (str, start, length) = Substring.base str
  in encodeSubstring {str=str, start=start, stop=start+length} end *)

fun encStringContents str =
  encodeSubstring {str=str, start=0, stop=String.size str}

end

fun encString str print = (print "\""; encStringContents str print; print "\"")

(* fun encSubstring str print = (print "\""; encSubstringContents str print; print "\"") *)

fun encOrNull _ NONE = encNull
  | encOrNull encode (SOME a) = encode a

fun encArray encode ls print = case ls of
    [] => print "[]"
  | a :: ls => let
    fun inner [] = print "]"
      | inner (a :: ls) = (print ","; encode a print; inner ls)
    val () = print "["
    val () = encode a print
    in inner ls end

fun encPosition (line, col) print = (
  print "{\"line\":"; encInt line print;
  print ",\"character\":"; encInt col print;
  print "}")

fun encRange encPos (start, stop) print = (
  print "{\"start\":"; encPos start print;
  print ",\"end\":"; encPos stop print;
  print "}")

type location_link = {
  origin: rangeLC option,
  range: rangeLC, selRange: rangeLC, uri: string option}

fun encLocationLink uri0 ({origin, uri, range, selRange}: location_link) print = (
  print "{\"targetUri\":"; encString (Option.getOpt (uri, uri0)) print;
  print ",\"targetRange\":"; encRange encPosition range print;
  print ",\"targetSelectionRange\":"; encRange encPosition selRange print;
  case origin of
    NONE => ()
  | SOME origin => (print ",\"originSelectionRange\":"; encRange encPosition origin print);
  print "}")

fun encHover ({markdown, range}: hover) print = (
  print "{\"contents\":{\"kind\":\"markdown\",\"value\":";
    encString markdown print; print "}";
  case range of
    NONE => ()
  | SOME range => (print ",\"range\":"; encRange encPosition range print);
  print "}")

fun encGoalState ({asms, goal}: goal_state) print = (
  print "{\"asms\":"; encArray encString asms print;
  print ",\"goal\":"; encString goal print;
  print "}")

fun encGoalStateResponse ({theorem, step, goals, pretty, error, failedRange}
                          : goal_state_response) print = (
  print "{\"theorem\":"; encString theorem print;
  print ",\"step\":"; encInt step print;
  print ",\"goals\":"; encArray encGoalState goals print;
  print ",\"pretty\":"; encString pretty print;
  print ",\"error\":"; encOrNull encString error print;
  print "}")

(* Given the buffer text and a cursor byte offset, return the enclosing
   `Theorem NAME[attrs]: … Proof … QED` block (also `Triviality`) as a
   `theorem_context`, or NONE if the cursor isn't inside one.

   Drives HOLSourceParser over the current buffer text — same parser
   the compile uses — so keyword matching, attribute brackets, strings
   and comments are handled correctly.  parseDec streams decs one at a
   time; we bail on the first matching HOLTheoremDecl. *)
fun findEnclosingTheorem text cursor = let
  val consumed = ref false
  fun read _ = if !consumed then "" else (consumed := true; text)
  fun errSink _ _ _ = ()  (* buffer may be mid-edit and mildly invalid *)
  val {parseDec, ...} =
    HOLSourceParser.parseSML "" read errSink HOLSourceParser.initialScope
  fun loop () =
    case parseDec () of
      NONE => NONE
    | SOME (HOLSourceAST.HOLTheoremDecl {
              id = (_, name), colon, tac,
              proof_ = SOME {proof_, ...}, qed_, stop, ...}) =>
        (* An in-progress Proof-QED block has `qed_ = NONE`; treat the
           dec's `stop` as the upper bound so the LSP can drive live
           goal-state while the user is still typing the tactic body
           (Slice G.1). *)
        let val upperBound = case qed_ of SOME q => q | NONE => stop in
        if proof_ <= cursor andalso cursor <= upperBound
        then let val (tacStart, tacEnd) = HOLSourceAST.expSpan tac
        in SOME {name = name,
                 quote = String.substring (text, colon + 1,
                                           Int.max (0, proof_ - colon - 1)),
                 quoteStart = colon + 1,
                 tacText = String.substring (text, tacStart,
                                             Int.max (0, tacEnd - tacStart)),
                 tacStart = tacStart,
                 cursor = cursor}
        end
        else loop ()
        end
    | SOME _ => loop ()
  in loop () end

exception MalformedData

datatype req_id = Id of int | Str of string
datatype 'v result = Ok of 'v | Err of {code: int, message: string, data: 'v option}
datatype 'v message =
  Request of {id: req_id, method: string, params: 'v}
| Response of {id: req_id, result: 'v result}
| Notification of {method: string, params: 'v}

fun mkResponse id r = Response {id = id, result = r}
fun mkNotif method params = Notification {method = method, params = params}
fun mkErr code message = Err {code = code, message = message, data = NONE}

(* val ParseError = ~32700 *)
val InvalidRequest = ~32600
(* val MethodNotFound = ~32601 *)
val InvalidParams = ~32602
val InternalError = ~32603
(* val ServerErrorStart = ~32099 *)
(* val ServerErrorEnd = ~32000 *)
val ServerNotInitialized = ~32002
(* val UnknownErrorCode = ~32001 *)
(* val RequestCanceled = ~32800 *)
(* val ContentModified = ~32801 *)
(* val ServerCancelled = ~32802 *)
(* val RequestFailed = ~32803 *)

val ErrorSeverity = 1
val WarnSeverity = 2
(* val InfoSeverity = 3 *)
(* val HintSeverity = 4 *)

datatype incremental = IncrNone | IncrChunk | IncrStream
datatype holdep_kind = HoldepNone | HoldepQuiet | HoldepList
datatype elab_on = ElabOnNone | ElabOnChange | ElabOnSave

local
  open JSONDecode JSON
  exception Invalid
in

val error = map3 (fn (code, message, data) => {code = code, message = message, data = data})
  (field "code" int, field "message" string, fieldO "data" raw)

val incr = ofRaw (fn jv =>
  case decode int jv of
    0 => IncrNone | 1 => IncrChunk | 2 => IncrStream
  | _ => raise JSONError (Invalid, jv))

val holdepKind = ofRaw (fn jv =>
  case decode int jv of
    0 => HoldepNone | 1 => HoldepQuiet | 2 => HoldepList
  | _ => raise JSONError (Invalid, jv))

val req_id = orElse (map Id int, map Str string)
val decMessage: JSON.value message decoder = ofRaw (fn jv =>
  case decode (fieldO "id" req_id) jv of
    NONE => Notification {
      method = decode (field "method" string) jv,
      params = decode (fieldD "params" raw NULL) jv}
  | SOME id => case decode (fieldO "method" string) jv of
    SOME method => Request {
      id = id, method = method,
      params = decode (fieldD "params" raw NULL) jv}
  | NONE => let
    val result = case decode (fieldO "error" error) jv of
      SOME e => Err e
    | NONE => Ok (decode (field "result" raw) jv )
    in Response {id = id, result = result} end)

val elabOn = ofRaw (fn jv =>
  case decode int jv of
    0 => ElabOnNone | 1 => ElabOnChange | 2 => ElabOnSave
  | _ => raise JSONError (Invalid, jv))

val position = tuple2 (field "line" int, field "character" int)
val range = tuple2 (field "start" position, field "end" position)

val textDocumentPositionParams =
  map2 (fn (uri, pos) => {uri = uri, pos = pos})
    (field "textDocument" (field "uri" string), field "position" position)

val cancelParams = field "id" req_id

val evalParams = map4 (fn (uri, code, incr, holdep) =>
    {uri = uri, code = code, incr = incr, holdep = holdep})
  (field "uri" string, field "code" string, fieldD "incr" incr IncrNone,
    fieldD "holdep" holdepKind HoldepQuiet)

val textDocumentParams = field "textDocument" (
  map3 (fn (uri, version, text) => {uri = uri, version = version, text = text})
    (field "uri" string, field "version" int, field "text" string))

val versionedTextId = tuple2 (field "uri" string, field "version" int)

val changeEvent = map2 (fn (range, text) => {range = range, text = text})
  (fieldO "range" range, field "text" string)

val didChangeParams =
  map2 (fn ((uri, version), changes) => {uri = uri, version = version, changes = changes})
    (field "textDocument" versionedTextId, field "contentChanges" (array changeEvent))

val textDocumentId = field "textDocument" (field "uri" string)

end

fun encReqId (Id id) = encInt id
  | encReqId (Str s) = encString s

fun encMessage (Request {id, method, params: encode}) print = (
    print "{\"jsonrpc\":\"2.0\",\"id\":"; encReqId id print;
    print ",\"method\":"; encString method print;
    print ",\"params\":"; params print; print "}")
  | encMessage (Response {id, result}) print = (
    print "{\"jsonrpc\":\"2.0\",\"id\":"; encReqId id print;
    case result of
      Ok r => (print ",\"result\":"; r print)
    | Err {code, message, data} => (
      print ",\"error\":{\"code\":"; encInt code print;
      print ",\"message\":"; encString message print;
      case data of NONE => () | SOME data => (print ",\"data\":"; data print);
      print "}");
    print "}")
  | encMessage (Notification {method, params}) print = (
    print "{\"jsonrpc\":\"2.0\",\"method\":"; encString method print;
    print ",\"params\":"; params print; print "}")

structure Channel: sig
type 'a sender
type 'a receiver
exception Disconnected
val channel: unit -> 'a sender * 'a receiver
val send: 'a sender -> 'a -> unit
val closeSender: 'a sender -> exn option -> unit
val recv: 'a receiver -> 'a
end = struct

exception Disconnected
datatype 'a slot = Empty | Full of 'a | Disconn of exn option
type 'a sender = ConditionVar.conditionVar * Mutex.mutex * 'a slot ref
type 'a receiver = 'a sender

fun channel () = let
  val x = (ConditionVar.conditionVar (), Mutex.mutex (), ref Empty)
  in (x, x) end

fun send (cvar, mutex, r) v = let
  fun loop () =
    case !r of
      Disconn (SOME e) => PolyML.Exception.reraise e
    | Disconn NONE => raise Disconnected
    | Empty => (r := Full v; Mutex.unlock mutex; ConditionVar.signal cvar)
    | Full _ => (ConditionVar.wait (cvar, mutex); loop ())
  in Mutex.lock mutex; loop () end

fun closeSender (cvar, mutex, r) e = let
  fun loop () =
    case !r of
      Disconn (SOME e) => PolyML.Exception.reraise e
    | Disconn NONE => raise Disconnected
    | Full _ => (ConditionVar.wait (cvar, mutex); loop ())
    | _ => (r := Disconn e; Mutex.unlock mutex; ConditionVar.signal cvar)
  in Mutex.lock mutex; loop () end

fun recv (cvar, mutex, r) = let
  fun loop () =
    case !r of
      Disconn (SOME e) => PolyML.Exception.reraise e
    | Disconn NONE => raise Disconnected
    | Full v => (r := Empty; Mutex.unlock mutex; ConditionVar.signal cvar; v)
    | Empty => (ConditionVar.wait (cvar, mutex); loop ())
  in Mutex.lock mutex; loop () end

end

type connection = {recv: unit -> JSON.value message, send: encode message -> unit}
fun stdioConnection (): connection = let
  val recv = let
    val (send, recv) = Channel.channel ()
    fun readHeaders sz =
      case TextIO.inputLine TextIO.stdIn of
        NONE => NONE
      | SOME line =>
        case String.fields (fn x => x = #":") line of
          ["\r\n"] => (case sz of SOME n => SOME n | NONE => raise MalformedData)
        | ["Content-Length", n] => ((
          if String.sub(n, 0) = #" " andalso String.substring(n, size n - 2, 2) = "\r\n" then
            case Int.fromString (String.substring (n, 1, size n - 3)) of
              SOME n => readHeaders (SOME n)
            | NONE => raise MalformedData
          else raise MalformedData)
          handle Subscript => raise MalformedData)
        | _ => readHeaders sz
    fun loop () =
      case readHeaders NONE of
        NONE => ()
      | SOME size => let
        val inp = TextIO.inputN (TextIO.stdIn, size)
        val msg = JSONDecode.decodeString decMessage inp
        in Channel.send send msg; loop () end
    fun readerThread () =
      (loop (); Channel.closeSender send NONE)
      handle e => (Channel.closeSender send (SOME e); PolyML.Exception.reraise e)
    val _ = Thread.fork (readerThread, [])
    in fn () => Channel.recv recv end

  (* Hijack the real stdOut for our JSON-RPC frames, and re-point
     TextIO.stdOut at TextIO.stdErr so USER code that writes via
     TextIO.stdOut (e.g. `val _ = print "..."` at top level in a HOL
     script) doesn't corrupt the wire. *)
  val lspOut = TextIO.getOutstream TextIO.stdOut
  val () = TextIO.setOutstream (TextIO.stdOut,
                                TextIO.getOutstream TextIO.stdErr)
  val send = let
    val (send, recv) = Channel.channel ()
    fun writerThread () = let
      val msg: encode message = Channel.recv recv
      val buf = ref []
      val () = encMessage msg (fn s => buf := s :: !buf)
      fun write (n, a :: buf, acc) = write (n + size a, buf, a :: acc)
        | write (n, [], acc) =
          TextIO.StreamIO.output (lspOut,
            String.concat ("Content-Length: " :: Int.toString n :: "\r\n\r\n" :: acc))
      in write (0, !buf, []); TextIO.StreamIO.flushOut lspOut;
         writerThread () end
       (* An encode-time exception must not kill the writer: the
          channel would stay Full and every send would hang. *)
       handle e => (
         TextIO.output (TextIO.stdErr,
           "[LSP-writer] dropping message; encode raised: " ^ exnMessage e ^ "\n");
         TextIO.flushOut TextIO.stdErr;
         writerThread ())
    val _ = Thread.fork (writerThread, [])
    in Channel.send send end
  in {send = send, recv = recv} end

exception ProtocolError

fun initialize ({send, recv}:connection) capabilities = let
  fun init () =
    case recv () of
      Request {method = "initialize", id, params} => (id, params)
    | Request {id, ...} => (
      send (mkResponse id (mkErr ServerNotInitialized "expected initialize request"));
      init ())
    | Notification {method = "exit", ...} => raise ProtocolError
    | Notification _ => init ()
    | _ => raise ProtocolError
  val (id, params) = init ()
  val _ = send (mkResponse id (Ok (fn print => (
    print "{\"capabilities\":"; print capabilities; print "}"))))
  val _ = case recv () of
    Notification {method = "initialized", ...} => ()
  | _ => raise ProtocolError
  in params end

fun encPosLC lines = encPosition o getLineCol lines
val encRangeLC = encRange o encPosLC
fun locToRange ({startPosition,endPosition,...}:PolyML.location) =
  (FixedInt.toInt startPosition, FixedInt.toInt endPosition)
(* fun encLocLC lines = encRangeLC lines o locToRange *)

fun encPretty textWidth pp print = let
  fun print' s = encStringContents s print
  in print "\""; PolyML.prettyPrint (print', textWidth) pp; print "\"" end

fun encDArray encode ls print = case DArray.size ls of
    0 => print "[]"
  | n => let
    fun inner i = if i < n then
      (print ","; encode (DArray.sub (ls, i)) print; inner (i+1))
    else print "]"
    in print "["; encode (DArray.sub (ls, 0)) print; inner 1 end

fun lastIndexOf c s = let
  fun go i = if i = 0 then ~1 else case i - 1 of i' =>
    if c = String.sub (s, i') then i' else go i'
  in go (String.size s) end

fun splitOn c s = let
  fun loop i j out =
    if i = 0 then String.substring (s, i, j - i) :: out
    else case i - 1 of i' =>
      if c = String.sub (s, i')
      then loop i' i' (String.substring (s, i, j - i) :: out)
      else loop i' j out
  in case String.size s of sz => loop sz sz [] end

(* `extend_path_with_includes` reads `getDir()`'s Holmakefile and
   blindly appends its INCLUDES to `Meta.loadPath` with no dedup
   against existing entries.  Cache each canonical dir we've
   already walked so per-didOpen calls don't grow the load path
   linearly in the number of opened files. *)
val walkedDirs : string Binaryset.set ref =
  ref (Binaryset.empty String.compare)

fun walkIncludesFrom dir = let
  val abs = OS.Path.mkAbsolute {path = dir, relativeTo = OS.FileSys.getDir()}
             handle _ => dir
in
  if Binaryset.member (!walkedDirs, abs) then ()
  else let
    val saved = OS.FileSys.getDir()
    fun restore () = OS.FileSys.chDir saved handle _ => ()
  in
    (OS.FileSys.chDir dir;
     ReadHMF.extend_path_with_includes
       {verbosity = 0, lpref = Meta.loadPath};
     walkedDirs := Binaryset.add (!walkedDirs, abs);
     restore ())
    handle _ => restore ()
  end
end

fun uriToPath uri =
  if String.isPrefix "file://" uri
  then SOME (String.extract (uri, 7, NONE)) else NONE

(* `hol.ML` at boot preloads project_dirs / external_includes from
   cwd's `holproject.toml`; this handler catches files whose
   Holmakefile chain isn't reached that way -- HOL4 dev under a
   `holmake = false` toml, or files opened outside any holproject. *)
fun augmentLoadPathForUri uri = case uriToPath uri of
    NONE => ()
  | SOME path => walkIncludesFrom (OS.Path.dir path)

fun start {diag, dbg} = let
  val _ = PolyML.print_depth 100
  val conn as {send, recv} = stdioConnection ()
  val _ (*clientCapabilities*) = initialize conn (concat [
    "{\"textDocumentSync\":2", (* 2 = Incremental; applyEdit supports it *)
    (* LSP 3.17 offset encoding.  Server-side buffers and fromLineCol
       count bytes, so ask the client for UTF-8 positions.  Without this
       eglot defaults to UTF-16 code units, and edits crossing multi-
       byte characters (e.g. `⇒`, `∧`) land mid-codepoint and corrupt
       the buffer — surfaces as a HOL "Lexical error" on the first byte
       of the split character. *)
    ",\"positionEncoding\":\"utf-8\"",
    ",\"hoverProvider\":true",
    ",\"definitionProvider\":true",
    ",\"referencesProvider\":true",
    "}"])
  fun logMessage str =
    send (Notification {
      method = "window/logMessage",
      params = fn print => (
        print "{\"type\":4,\"message\":"; encString str print; print "}")})
  val _ = diag "started"
  val _ = logMessage "started"
  val _ = markServerStarted ()

  val textWidth = 100 (* configure? *)
  val printDepth = 100

  val jobs = let
    val mutex = Mutex.mutex ()
    val jobs = ref []
    fun modify f = let
      val _ = Mutex.lock mutex
      val j = !jobs
      val _ = jobs := f j
      val _ = Mutex.unlock mutex
      in j end
    in modify end

  fun spawnJobCore id job = let
    val jobThread = Thread.fork (job, [])
    in jobs (fn js => (id, jobThread) :: js); () end

  fun spawnJob id params decode f = spawnJobCore id (fn () => let
    val result = f (JSONDecode.decode decode params) handle
      JSONErrors.JSONError _ => mkErr InvalidParams "json decode failed"
    | e => mkErr InternalError (exnMessage e)
    val _ = send (mkResponse id result)
    val _ = jobs (fn js => let
      fun go (_, []) = js
        | go (acc, j::js) = if #1 j = id then List.revAppend (acc, js) else go (j::acc, js)
      in go ([], js) end)
    in () end)

  val elabOnRef = ref ElabOnChange
  val holdepMode = ref HoldepQuiet

  (* Server-initiated request ids and progress tokens for
     window/workDoneProgress. *)
  val nextRequestId = ref 100000
  fun allocRequestId () =
      !nextRequestId before nextRequestId := !nextRequestId + 1
  val progressIdCounter = ref 0

  datatype report =
    Error of {hard: bool, pos: range, msg: encode}
  | CompilerOut of int * string list
  | ToplevelOut of int * string list
  | Progress of int
  | Completed
  | Interrupted

  (* Per-dec snapshot; see `parse_data.declSnapshots` below.  A resume
     to `endByte` seeds the new compile with `builtTrees` and `plugins`
     from this snapshot, restores HOL state via `compileSnap`, and
     uses `diags` as the frozen prefix of the diagnostic list. *)
  type declSnapshot = {
    endByte     : int,
    builtTrees  : HOL_IDE.built list,
    diags       : report DArray.darray,
    plugins     : plugin_data,
    compileSnap : LSPExtension.compileSnap }

  type parse_data = {
    done: bool,
    pos: int,
    builtTrees: HOL_IDE.built list,
    diags: report DArray.darray,
    plugins: plugin_data,
    (* Newest-first list of per-dec snapshots taken by the current /
       last-completed compile.  Consulted by `startCompile` to resume
       from the largest snapshot with `endByte <= minEditOffset`
       instead of restarting from byte 0. *)
    declSnapshots: declSnapshot list}
  fun emptyParseData n: parse_data = {
    done = false, pos = 0, builtTrees = [],
    diags = DArray.new (n, Completed),
    plugins = emptyPluginData,
    declSnapshots = [] }
  (* Preserve `declSnapshots` from `p` but zero the rest.  Used by
     `applyEdit` so a `didChange` doesn't discard the snapshots the
     previous compile computed. *)
  fun carryOverSnapshots ({declSnapshots, ...}:parse_data): parse_data = {
    done = false, pos = 0, builtTrees = [],
    diags = DArray.new (0, Completed),
    plugins = emptyPluginData,
    declSnapshots = declSnapshots }
  fun addBuiltTree t {done, pos, builtTrees, diags, plugins, declSnapshots} =
    {done = done, pos = pos, builtTrees = t :: builtTrees, diags = diags,
     plugins = plugins, declSnapshots = declSnapshots}
  fun setParsePos pos {done, pos = _, builtTrees, diags, plugins, declSnapshots} =
    {done = done, pos = pos, builtTrees = builtTrees, diags = diags,
     plugins = plugins, declSnapshots = declSnapshots}
  fun setParseDone pos {done = _, pos = _, builtTrees, diags, plugins, declSnapshots} =
    {done = true, pos = pos, builtTrees = builtTrees, diags = diags,
     plugins = plugins, declSnapshots = declSnapshots}
  fun setPlugins plugins {done, pos, builtTrees, diags, plugins = _, declSnapshots} =
    {done = done, pos = pos, builtTrees = builtTrees, diags = diags,
     plugins = plugins, declSnapshots = declSnapshots}
  fun addDeclSnapshot snap {done, pos, builtTrees, diags, plugins, declSnapshots} =
    {done = done, pos = pos, builtTrees = builtTrees, diags = diags,
     plugins = plugins, declSnapshots = snap :: declSnapshots}

  type text_data = {text: string, version: int, lines: lines}
  type compile_data = {parse: parse_data ref, text: text_data,
                       thread: Thread.thread, cancelled: bool ref}
  type file_data = {
    compile: compile_data option ref,
    lastTrees: {parse: parse_data, text: text_data} ref,
    (* debounce epoch: incremented on didChange and at startCompile
       entry.  scheduleCompile's forked thread captures the epoch and
       only fires startCompile if its epoch still matches when it
       wakes up.  Rapid-fire edits fork many threads but only the
       last (whose epoch survives to wake time) actually compiles. *)
    debounce: int ref,
    (* Rolling minimum edit offset across `applyEdit` batches since
       the last successful compile.  `startCompile` picks the largest
       snapshot in `lastTrees.parse.declSnapshots` with `endByte <=
       !minEditOffset` (falling back to a full boot-restore if none).
       `NONE` means no edit info is available (fresh file, or a
       previous compile completed and cleared it) — treated as 0
       (full restart). *)
    minEditOffset: int option ref,
    (* Runtime-diagnostic squiggles the walker has observed since
       the last compile: keyed by theorem name, value is the
       Error report for the failed leaf.  Fresh compiles clear
       these; a successful walker query for a theorem removes its
       entry so a user-fix removes the squiggle without waiting
       for the next compile. *)
    walkerDiags: (string, report) Binarymap.dict ref}
  local
    val mutex = Mutex.mutex ()
    val fileInfo = ref (Binarymap.mkDict String.compare: (string, file_data) Binarymap.dict)
  in
    fun withFileInfo f = (Mutex.lock mutex; let
      val (v, r) = f (!fileInfo)
      val _ = fileInfo := v
      val _ = Mutex.unlock mutex
      in r end
      handle e => (Mutex.unlock mutex; PolyML.Exception.reraise e))
  end

  fun newFile text version = let
    val text = {text = text, version = version, lines = mkLineCounter text}
    in {compile = ref NONE, lastTrees = ref {parse = emptyParseData 0, text = text},
        debounce = ref 0, minEditOffset = ref NONE,
        walkerDiags = ref (Binarymap.mkDict String.compare)} end

  (* Cooperative cancel: signal the flag, which the compile thread
     checks at each Progress event and raises Thread.Interrupt.  We
     can't use Thread.interrupt directly for two reasons: the compile
     thread runs InterruptDefer (so Poly wouldn't deliver it), and
     HOL's tactic-level `handle _ =>` would swallow it mid-proof
     without stopping the wider compile.

     stopCompile does NOT wait for the thread to exit — it's called
     from the recv thread on every didChange, and a stuck compile
     (e.g., HOL's parser recovering from an unterminated `Theorem`)
     would otherwise block recv, freezing hover requests and further
     didChanges.  The `cancelled` flag doubles as a "no longer
     current" marker: the compile thread checks it before writing
     lastTrees so a stale finish can't clobber the new state. *)
  fun stopCompile r = case !r of
    NONE => ()
  | SOME {cancelled, ...} => (r := NONE; cancelled := true)

  fun applyEdit ({compile, lastTrees, minEditOffset, ...}:file_data) version changes = let
    val _ = stopCompile compile
    fun getLines text NONE = mkLineCounter text
      | getLines _ (SOME lines) = lines
    (* Push `off` into the rolling min-edit tracker; a later `startCompile`
       consults this to decide whether to resume from a snapshot. *)
    fun bumpMin off =
      case !minEditOffset of
        NONE => minEditOffset := SOME off
      | SOME m => if off < m then minEditOffset := SOME off else ()
    (* The old `parse` value is carried through the fold so we can
       preserve its `declSnapshots` on each step (via
       `carryOverSnapshots`).  On a full-text replace (`range = NONE`)
       the snapshots become useless — their `endByte` offsets no
       longer index anything meaningful in the new text — so we drop
       them explicitly and push min-edit-offset to 0. *)
    fun applyText [] data = data
      | applyText ({range = NONE, text}::cs) _ =
        (bumpMin 0; applyText cs (emptyParseData 0, text, NONE))
      | applyText ({range = SOME (from, to), text}::cs) (parse, base, lines) = let
        val lines = getLines base lines
        val (from, to) = (fromLineCol lines from, fromLineCol lines to)
        val text = Substring.concat [
          Substring.substring (base, 0, from),
          Substring.full text,
          Substring.substring (base, to, size base - to)]
        val _ = bumpMin from
        in applyText cs (carryOverSnapshots parse, text, NONE) end
    val {parse, text = {text, lines, version = _}} = !lastTrees
    val (parse, text, lines) = applyText changes (parse, text, SOME lines)
    val text = {text = text, lines = getLines text lines, version = version}
    in lastTrees := {parse = parse, text = text} end

  fun exceptionMessage (exn: exn) =
    PolyML.PrettyBlock(0, false, [], [
      PolyML.PrettyBlock(0, false, [], [PolyML.PrettyString "Exception"]),
      PolyML.PrettyBreak(1, 3),
      PolyML.prettyRepresentation(exn, printDepth),
      PolyML.PrettyBreak(1, 3),
      PolyML.PrettyString "raised"])

  fun exnToReport i e = Error {hard = true,
    pos = case PolyML.Exception.exceptionLocation e of
      (* A HOL kernel exception (raised from Theory.new_theory or
         similar) carries a location inside the HOL source that
         raised it — mapping its byte offset via the current file's
         `lines` table produces a nonsense line.  Trust the
         location only when its `file` field is empty (meaning
         "the anonymous compile unit we're currently feeding to
         PolyML.compiler"). *)
      SOME (l as {file = "", ...}) => locToRange l
    | _ => (i, i),
    msg = encPretty textWidth (exceptionMessage e)}

  fun mergeInto msg buf =
    case (msg, DArray.last buf) of
      (CompilerOut (pos', [s]), SOME (CompilerOut (pos, ss))) =>
      if pos = pos' then DArray.setLast (buf, CompilerOut (pos, s :: ss))
      else DArray.push (buf, msg)
    | (ToplevelOut (pos', [s]), SOME (ToplevelOut (pos, ss))) =>
      if pos = pos' then DArray.setLast (buf, ToplevelOut (pos, s :: ss))
      else DArray.push (buf, msg)
    | _ => DArray.push (buf, msg)

  fun getHoldep text = let
    val {read, ...} = HOLSource.stringToReader {quietOpen = false, print = fn _ => ()} text
    in
      Binarymap.foldr (fn (a, _, r) => a :: r) [] (Holdep_tokens.reader_deps ("", read))
      handle _ => []
    end

  fun compileForReport uri code startByte lastPos builtTree onDecCompleted report = let
    val _ = HOL_IDE.initialize {
      text = code,
      filename = uri,
      (* `unclosed quotation` / `expected ...` almost always mean an
         in-progress edit; surface those as Warning, not Error. *)
      parseError = fn pos => fn s => let
        val soft = String.isSubstring "unclosed quotation" s
                   orelse String.isSubstring "expected" s
      in report (Error {hard = not soft, pos = pos, msg = encString s}) end,
      compilerOut = fn s => report (CompilerOut (!lastPos, [s])),
      toplevelOut = fn s => report (ToplevelOut (!lastPos, [s])),
      progress = fn i => (lastPos := i; report (Progress i)),
      error = fn {hard, location, message, ...} => report (Error {
        hard = hard, pos = locToRange location, msg = encPretty textWidth message}),
      runtimeExn = fn e => report (exnToReport (!lastPos) e),
      builtTree = builtTree,
      onDecCompleted = onDecCompleted,
      startByte = startByte }
    in lastPos := size code end

  (* Materialise an `encode` (`(string -> unit) -> unit`) into a plain
     string.  Used to build dedup keys for Error reports whose `msg`
     is a pretty-printer callback. *)
  fun encodeToString enc = let
    val buf = ref []
    fun sink s = buf := s :: !buf
    val () = enc sink
    in String.concat (rev (!buf)) end

  (* Drop later Error reports whose (pos, msg) matches an earlier one.
     A single mis-typed dec often triggers multiple parser recovery
     passes each emitting the same "expected 'QED'" / "expected an
     expression" pair -- users don't need to see them twice.  Non-
     Error reports pass through unchanged. *)
  fun dedupReports d = let
    val seen = ref (Binaryset.empty String.compare)
    val out = DArray.new (DArray.size d, Completed)
    fun step r = case r of
        Error {pos = (s, e), msg, ...} =>
          let val k = Int.toString s ^ ":" ^ Int.toString e ^ ":"
                      ^ encodeToString msg
          in if Binaryset.member (!seen, k) then ()
             else (seen := Binaryset.add (!seen, k);
                   DArray.push (out, r))
          end
      | _ => DArray.push (out, r)
    val () = DArray.app step d
    in out end

  (* Emit publishDiagnostics for `uri` combining the last-completed
     compile's diagnostics and any walker-observed runtime squiggles. *)
  fun publishAllDiagnostics uri
                            ({lastTrees, walkerDiags, ...}:file_data) = let
    val {text, parse} = !lastTrees
    val {lines, version, ...} = text
    val compileDiags = #diags parse
    val wd = !walkerDiags
    val total = DArray.size compileDiags + Binarymap.numItems wd
    val snapshot = DArray.clone (compileDiags, total)
    val _ = Binarymap.app (fn (_, r) => DArray.push (snapshot, r)) wd
    val snapshot = dedupReports snapshot
    fun encDiag (Error {hard, pos, msg}) print = (
        print "{\"range\":"; encRangeLC lines pos print;
        print ",\"severity\":";
        encInt (if hard then ErrorSeverity else WarnSeverity) print;
        print ",\"message\":"; msg print; print "}")
      | encDiag _ _ = raise Fail "unexpected report kind"
  in
    send (mkNotif "textDocument/publishDiagnostics" (fn print => (
      print "{\"uri\":"; encString uri print;
      print ",\"version\":"; encInt version print;
      print ",\"diagnostics\":"; encDArray encDiag snapshot print;
      print "}")))
  end

  fun startCompile uri ({compile, lastTrees, debounce, minEditOffset,
                         walkerDiags}:file_data) = (
    (* Invalidate any pending scheduleCompile thread: their epoch
       check will see the new value and self-abort. *)
    debounce := !debounce + 1;
    (* Runtime squiggles from the walker are always stale w.r.t. the
       new compile -- clear them so a fix removes squiggles even
       before the user visits the theorem to re-run the walker. *)
    walkerDiags := Binarymap.mkDict String.compare;
    if #done (#parse (!lastTrees)) then
      (!LSPExtension.notifyCompileStart (!minEditOffset);
       !LSPExtension.resetForCompile (); ())
    else let
    val _ = stopCompile compile
    val {text as {lines, ...}, parse = lastParse} = !lastTrees
    val {declSnapshots = lastSnaps, diags = oldDiags, ...} = lastParse
    (* Resume decision: pick the largest snapshot with `endByte <=
       !minEditOffset`.  If none, do a full boot-restore starting at
       byte 0. *)
    val resumeSnap =
      case !minEditOffset of
        NONE => NONE
      | SOME editOff =>
        (* `declSnapshots` is newest-first, so the first match walking
           the list is the largest `endByte <= editOff`. *)
        List.find (fn (s:declSnapshot) => #endByte s <= editOff) lastSnaps
    val (initialTrees, resumeStart, oldDiags) =
      case resumeSnap of
        NONE => (
          !LSPExtension.notifyCompileStart (!minEditOffset);
          !LSPExtension.resetForCompile ();
          (emptyParseData 8, 0, oldDiags))
      | SOME snap => let
          val _ = !LSPExtension.notifyCompileStart (!minEditOffset)
          val _ = !LSPExtension.restoreCompileSnap (#compileSnap snap)
          val {endByte, builtTrees, diags = snapDiags, plugins,
               ...} = snap
          (* Seed `diags` with the frozen snapshot; leave `oldDiags`
             empty so no post-`endByte` stale diagnostics from the
             previous compile leak into the LSP publish stream. *)
          val seededDiags = DArray.clone (snapDiags, DArray.size snapDiags)
          val trees : parse_data = {
            done = false, pos = endByte, builtTrees = builtTrees,
            diags = seededDiags, plugins = plugins,
            declSnapshots =
              List.filter (fn (s':declSnapshot) => #endByte s' <= endByte)
                          lastSnaps}
          val emptyDiags = DArray.new (0, Completed)
        in (trees, endByte, emptyDiags) end
    val _ = minEditOffset := NONE
    val _ = if dbg andalso resumeStart > 0 then
              send (mkNotif "$/compileResumedAt" (fn print => (
                print "{\"uri\":"; encString uri print;
                print ",\"version\":"; encInt (#version text) print;
                print ",\"pos\":"; encInt resumeStart print;
                print "}")))
            else ()
    val trees = ref initialTrees
    val cancelled = ref false

    fun compileThread () = ((let
      fun encDiag (Error {hard, pos, msg}) print = (
          print "{\"range\":"; encRangeLC lines pos print;
          print ",\"severity\":"; encInt (if hard then ErrorSeverity else WarnSeverity) print;
          print ",\"message\":"; msg print; print "}")
        | encDiag _ _ = raise Fail "unexpected report kind"

      val holdepMode = !holdepMode
      val mods = case holdepMode of HoldepNone => [] | _ => getHoldep (#text text)
      val files = DArray.new (8, "")
      val errors = DArray.new (1, Bind)
      val _ = app (fn m =>
        loadPlan (fn f => DArray.push (files, f)) m handle e => DArray.push (errors, e)) mods
      val _ = if DArray.isEmpty files andalso DArray.isEmpty errors then () else (
        case holdepMode of
          HoldepList => send (mkNotif "$/holdep" (fn print => (
            print "{\"uri\":"; encString uri print;
            print ",\"version\":"; encInt (#version text) print;
            print ",\"files\":"; encDArray encString files print;
            if DArray.isEmpty errors then () else (
              print ",\"errors\":"; encDArray (encDiag o exnToReport 0) errors print;
              DArray.clear errors);
            print "}")))
        | _ => ();
        DArray.app (fn f => qquse f handle e => DArray.push (errors, e)) files;
        case holdepMode of
          HoldepList => send (mkNotif "$/holdepCompleted" (fn print => (
            print "{\"uri\":"; encString uri print;
            print ",\"version\":"; encInt (#version text) print;
            if DArray.isEmpty errors then () else (
              print ",\"errors\":"; encDArray (encDiag o exnToReport 0) errors print);
            print "}")))
        | _ => ())

      fun beforeCompile () = let
        val ls = getPlugins ()
        in app (fn t => #beforeCompile t ()) ls; ls end
      fun afterCompile r ls = let
        val t = !trees
        fun f (t, map) = #afterCompile t (r, map)
        in trees := setPlugins (foldl f (#plugins t) ls) t; ls end

      fun updateDiags pos = let
        val {diags, ...} = !trees
        val n = DArray.size oldDiags
        val newDiags = DArray.clone (diags, DArray.size diags + n)
        fun loop i = if i >= n then () else let
          val x = DArray.sub (oldDiags, i)
          val keep = case x of Error {pos = (start, _), ...} => start >= pos | _ => true
          in if keep then DArray.push (newDiags, x) else (); loop (i+1) end
        in loop 0; DArray.replace (oldDiags, newDiags) end

      (* Only emit publishDiagnostics when the accumulated list has
         actually changed size since the last emit -- Progress events
         far past the point where an error was found still update
         `oldDiags` (by re-merging), but if the size didn't change,
         re-sending is pure noise for the client's log.  Both compile
         diagnostics AND walker-detected runtime squiggles contribute
         to the size we compare against. *)
      val lastSentSize = ref ~1
      (* Snapshot oldDiags for the writer thread.  A live reference
         races updateDiags on the next Progress event: DArray.replace
         mid-encode makes encDArray raise Subscript, which kills the
         writer and jams every subsequent send. *)
      fun sendDiags () = let
        val n = DArray.size oldDiags
        val wd = !walkerDiags
        val ws = Binarymap.numItems wd
        val total = n + ws
        in if total = !lastSentSize then () else (
          lastSentSize := total;
          let val snapshot = DArray.clone (oldDiags, total)
              val _ = Binarymap.app
                        (fn (_, r) => DArray.push (snapshot, r)) wd
              val snapshot = dedupReports snapshot
          in
          send (mkNotif "textDocument/publishDiagnostics" (fn print => (
            print "{\"uri\":"; encString uri print;
            print ",\"version\":"; encInt (#version text) print;
            print ",\"diagnostics\":"; encDArray encDiag snapshot print;
            print "}"))) end)
        end

      (* Standard LSP window/workDoneProgress: gives eglot a
         mode-line spinner + percentage while the compile runs. *)
      val totalSize = size (#text text)
      (* Token is a bare integer; some clients (eglot) concatenate
         title and token when reporting, so we keep the token free of
         label-like text. *)
      val progressToken = Int.toString (!progressIdCounter)
        before progressIdCounter := !progressIdCounter + 1
      val () = send (Request {
        id = Id (allocRequestId ()),
        method = "window/workDoneProgress/create",
        params = fn print => (
          print "{\"token\":"; encString progressToken print; print "}")})
      val () = send (mkNotif "$/progress" (fn print => (
        print "{\"token\":"; encString progressToken print;
        print ",\"value\":{\"kind\":\"begin\",\"title\":\"HOL compile\",";
        print "\"cancellable\":false,\"percentage\":0,\"message\":";
        encString (OS.Path.file uri) print;
        print "}}")))
      val lastReportedPct = ref 0
      fun sendProgressReport pos =
        if totalSize <= 0 then () else let
          val pct = FixedInt.toInt (FixedInt.fromInt pos * 100 div FixedInt.fromInt totalSize)
          in if pct <= !lastReportedPct then () else (
            lastReportedPct := pct;
            send (mkNotif "$/progress" (fn print => (
              print "{\"token\":"; encString progressToken print;
              print ",\"value\":{\"kind\":\"report\",\"percentage\":";
              encInt pct print; print "}}"))))
          end
      fun sendProgressEnd () =
        send (mkNotif "$/progress" (fn print => (
          print "{\"token\":"; encString progressToken print;
          print ",\"value\":{\"kind\":\"end\"}}")))

      val ls = ref (beforeCompile ())
      val lastPos = ref resumeStart
      (* Abort a doomed dec: if the file's `Libs` / `Ancestors`
         `open`s fail (e.g., a dependency of an external HOL project
         hasn't been built yet, so `open jrhUtils` fails at the top),
         every subsequent name in the same dec-expansion produces a
         "not declared" error.  The user experience is a slow trickle
         of hundreds of diagnostics for what is really one broken
         open.  Count hard errors between successive Progress events
         (each Progress marks a completed outer dec).  If a single
         dec fires `runOfErrorsLimit` hard errors without progressing,
         the file's environment is broken — set the cancel flag and
         raise Thread.Interrupt.  Real files with legitimate isolated
         errors interleave them with progress and won't trigger. *)
      val runOfErrorsLimit = 10
      val runOfErrors = ref 0
      val abortedByRunOfErrors = ref false
      fun process (Progress i) = (
          if !cancelled then raise Thread.Interrupt else ();
          runOfErrors := 0;
          trees := setParsePos i (!trees);
          afterCompile (!lastPos before lastPos := i, i) (!ls);
          send (mkNotif "$/compileProgress" (fn print => (
            print "{\"uri\":"; encString uri print;
            print ",\"pos\":"; encPosLC lines i print;
            print "}")));
          sendProgressReport i;
          updateDiags i;
          sendDiags ();
          ls := beforeCompile ())
        | process (CompilerOut (_, ss)) = logMessage (concat (rev ss))
        | process (ToplevelOut (_, ss)) = logMessage (concat (rev ss))
        | process Completed = raise Bind
        | process Interrupted = raise Bind
        | process (msg as Error {hard = true, ...}) = (
            DArray.push (#diags (!trees), msg);
            runOfErrors := !runOfErrors + 1;
            if !runOfErrors >= runOfErrorsLimit then (
              logMessage ("compile aborted after "
                          ^ Int.toString (!runOfErrors)
                          ^ " errors from a single dec: "
                          ^ "likely a broken `open` in the header");
              abortedByRunOfErrors := true;
              cancelled := true;
              raise Thread.Interrupt)
            else ())
        | process (msg as Error _) = DArray.push (#diags (!trees), msg)
      fun processBuiltTree t = trees := addBuiltTree t (!trees)
      (* After each outer dec finishes, freeze a snapshot for the LSP
         to resume from on a later `didChange` with min-edit-offset >
         endByte.  Cloning `diags` at capture time keeps the resume
         seed independent of subsequent `updateDiags` mutations.

         Skip if the cumulative `trees.diags' is non-empty at capture
         time.  A partial-parse error early in the compile (e.g. a
         `Theory foo` still being typed, whose expansion raises
         `HOL_ERR "proposed theory name '' is not an identifier"' from
         the trailing `Theory.new_theory ""') puts the file into a
         "not yet valid" state whose subsequent decs' byte extents
         will change once the user completes their edit.  Capturing
         snapshots for the file's remaining decs would carry the
         stale error forward across every subsequent didChange, since
         resume-from-snapshot seeds `trees.diags' with the snapshot's
         frozen contents.  Conservative: no snapshots until the
         current compile has produced ZERO errors so far. *)
      fun captureSnap endByte = let
        val {builtTrees, plugins, diags, ...} = !trees
        val n = DArray.size diags
        in if n > 0 then ()
           else let
             val snap = {
               endByte = endByte,
               builtTrees = builtTrees,
               diags = DArray.new (0, Completed),
               plugins = plugins,
               compileSnap = !LSPExtension.captureCompileSnap ()}
             in trees := addDeclSnapshot snap (!trees)
             end
        end
      (* Flush any diagnostics accumulated since the last Progress.
         Progress events drive `updateDiags` + `sendDiags`, so errors
         from a dec that has been INTERRUPTED before its next Progress
         (typically a `runOfErrorsLimit'-triggered abort in the middle
         of a syntactically-broken tail) are still sitting in
         `trees.diags' and haven't been merged into `oldDiags`.
         Force a merge past end-of-file so those errors reach the
         client. *)
      fun flushDiags () = (updateDiags (size (#text text)); sendDiags ())
      in (
        compileForReport uri (#text text) resumeStart lastPos processBuiltTree captureSnap process;
        afterCompile (!lastPos, size (#text text)) (!ls);
        (* stopCompile no longer waits for the thread to exit, so
           we might land here on a stale thread whose applyEdit has
           already superseded the buffer we compiled.  Emit the
           completion events only if we're still current; otherwise
           the fresh compile that replaced us owns lastTrees. *)
        if !cancelled then () else (
          flushDiags ();
          sendProgressEnd ();
          send (mkNotif "$/compileCompleted" (fn print => (
            print "{\"uri\":"; encString uri print; print "}")));
          lastTrees := {text = text,
                        parse = setParseDone (size (#text text)) (!trees)})
      ) handle Thread.Interrupt => (
        sendProgressEnd ();
        (* When the compile aborted because a single dec produced a
           runaway cascade of errors, the diagnostics are complete
           (up to the abort) and clients should treat the compile as
           done, not interrupted.  A user-initiated cancel or a
           didChange-driven stop remain compileInterrupted. *)
        if !abortedByRunOfErrors then (
          flushDiags ();
          send (mkNotif "$/compileCompleted" (fn print => (
            print "{\"uri\":"; encString uri print; print "}")));
          lastTrees := {text = text,
                        parse = setParseDone (size (#text text)) (!trees)})
        else send (mkNotif "$/compileInterrupted" (fn print => (
          print "{\"uri\":"; encString uri print; print "}"))))
           | e => (
        logMessage ("compile aborted: " ^ exnMessage e);
        sendProgressEnd ();
        send (mkNotif "$/compileInterrupted" (fn print => (
          print "{\"uri\":"; encString uri print; print "}"))))
      end);
      (* Don't clobber `compile` here — stopCompile may have moved on
         and started another compile that installed a fresh SOME.
         The `cancelled` flag already fences correctness. *)
      ())
    val thread = Thread.fork (compileThread, [Thread.InterruptState Thread.InterruptDefer])
    in compile := SOME {parse = trees, text = text, thread = thread,
                        cancelled = cancelled} end)

  (* Fire a compile after a debounce delay: rapid didChange bursts
     collapse to one compile. *)
  fun scheduleCompile uri (v as {debounce, ...}: file_data) = let
    val () = debounce := !debounce + 1
    val myEpoch = !debounce
    val debounce_ms = Time.fromMilliseconds 300
    in Thread.fork (fn () =>
        ((OS.Process.sleep debounce_ms;
          if !debounce = myEpoch then startCompile uri v else ())
         handle _ => ()),
        []); ()
    end

  fun getState {compile, lastTrees, ...} endTarget = let
    fun getIfValid {parse as {pos, ...}, text} =
      if pos > 0 then let
        val offset = fromLineCol (#lines text) endTarget
        in if offset <= pos then SOME (parse, text, offset) else NONE end
      else NONE
    val state = case !compile of
      SOME {parse, text, ...} => getIfValid {parse = !parse, text = text}
    | NONE => NONE
    in case state of NONE => getIfValid (!lastTrees) | state => state end

  fun hover uri v (startTarget, endTarget) = let
    val ({plugins, builtTrees, ...}, text, endOffset) =
      case getState v endTarget of NONE => raise Empty | SOME s => s
    val startOffset = fromLineCol (#lines text) startTarget
    fun ppToString pp = let
      val mds = DArray.new (8, "")
      val _ = PolyML.prettyPrint (fn s => DArray.push (mds, s), textWidth) pp
      in concat (DArray.toList mds) end
    val ctx = {uri = uri, lines = #lines text, plugins = plugins, ppToString = ppToString}
    val out = !LSPExtension.hover (ctx, (startOffset, endOffset))
    fun locToRange {startPosition, endPosition, ...} = (
      getLineCol (#lines text) (FixedInt.toInt startPosition),
      getLineCol (#lines text) (FixedInt.toInt endPosition))
    fun typeHover (loc, pp) = {range = SOME (locToRange loc), markdown = ppToString pp}
    fun process loc props = let
      fun fromProps [] out = out
        | fromProps (HOL_IDE.PType ty :: props) (isId, _) = fromProps props (isId, SOME ty)
        | fromProps (HOL_IDE.PRefId i :: props) (_, ty) = fromProps props (SOME i, ty)
        | fromProps (HOL_IDE.PDefId i :: props) (_, ty) = fromProps props (SOME i, ty)
        | fromProps (_ :: props) out = fromProps props out
      val (isId, ty) = fromProps props (NONE, NONE)
      val thyHov = case HOL_IDE.builtGetThy props of
        NONE => []
      | SOME name => [{range = SOME (locToRange loc), markdown = "Theory " ^ name}]
      val (id, value, help) = case isId of
        NONE => (NONE, NONE, [])
      | SOME i => let
        val {startPosition, endPosition, ...} = loc
        val startPos = FixedInt.toInt startPosition
        val endPos = FixedInt.toInt endPosition
        val id = String.substring (#text text, startPos, endPos - startPos)
        val help =
          if lastIndexOf #"." id < 0 then let
            fun validate str = let
              fun look [] = false
                | look (HOL_IDE.PStructureAt file :: props) = let
                  val basename = String.extract (file, lastIndexOf #"/" file + 1, NONE)
                  val stem = String.extract (basename, 0, SOME (lastIndexOf #"." basename))
                  in str = stem orelse look props end
                | look (_ :: props) = look props
              in look props end
            in !LSPExtension.helpLookup (id, validate) end
          else let
            val components = splitOn #"." id
            val fst = List.hd components
            in !LSPExtension.helpLookup (List.last components, fn s => s = fst) end
          handle _ => []
        val range = SOME (getLineCol (#lines text) startPos, getLineCol (#lines text) endPos)
        val help = map (fn d => {range = range, markdown = d}) help
        val isGlobalId = i = 0 orelse let
          fun look [] = NONE
            | look (HOL_IDE.PDeclaredAt loc :: _) = SOME loc
            | look (_ :: props) = look props
          fun lookRefs [] = false
            | lookRefs (HOL_IDE.PReferences exp :: _) = exp
            | lookRefs (_ :: props) = lookRefs props
          in
            case look props of
              NONE => false
            | SOME {startPosition, endPosition, ...} =>
              case HOL_IDE.builtNavigateTo' builtTrees
                  {startOffset = FixedInt.fromInt startPosition, endOffset = FixedInt.fromInt endPosition} of
                NONE => false
              | SOME (HOL_IDE.Built (_, declProps, _), _) => lookRefs declProps
          end
        (* Lookup via the LSP file layer, not `globalNameSpace`, so
           hovers on a deleted `val foo = …` return NONE instead of
           the retained Poly/ML binding.  The layer falls through to
           `globalNameSpace` for bindings from the LSP-boot session
           (bossLib etc.). *)
        val value = if isGlobalId then #lookupVal LSPNameSpace.fileNS id else NONE
        in (SOME id, value, help) end
      open PolyML
      val ty = Option.map (fn ty =>
        NameSpace.Values.printType (ty, printDepth, SOME globalNameSpace)) ty
      val value = case value of
          NONE => NONE
        | SOME value =>
          case NameSpace.Values.print (value, printDepth) of
            PrettyString "" => NONE
          | otherwise => SOME otherwise
      (* Values of type `thm` are opaque to PolyML.NameSpace.Values;
         the SML-side hover would show only "val name: thm = ?".
         When DB has a theorem by this name, replace the standard
         value-print with the theorem statement (rendered by
         Parse.thm_to_string on the LSP-init hook). *)
      val thmMd = case id of
          NONE => NONE
        | SOME id => (!LSPExtension.thmLookup id handle _ => NONE)
      val out = case (id, ty, value, thmMd) of
          (_, NONE, NONE, _) => []
        (* Type without an identifier is the walked-up enclosing
           expression's type (`Conv.conv`, `Thm.thm -> Thm.thm`, …).
           Never informative — the user's cursor missed a specific
           name and we've fallen up.  Return nothing. *)
        | (NONE, SOME _, NONE, _) => []
        | (SOME id, SOME ty, _, SOME md) => let
          (* Theorem: "val id: thm\n\n<statement>" as one markdown block.
             ppToString may leave a trailing newline; strip it before
             appending the separator so we get exactly one blank line. *)
          fun rtrim s = let
            val n = size s
            fun k i = if i > 0 andalso Char.contains "\n\r " (String.sub (s, i-1))
                      then k (i-1) else i
            in String.substring (s, 0, k n) end
          in [{range = SOME (locToRange loc),
               markdown = "val " ^ id ^ ": " ^ rtrim (ppToString ty)
                          ^ "\n\n" ^ md}]
          end
        | (SOME id, SOME ty, NONE, NONE) =>
          [typeHover (loc, PrettyBlock(0, true, [],
            [PrettyString ("val " ^ id ^ ":"), PrettyBreak(1, 2), ty]))]
        | (id, ty, SOME value, NONE) =>
          [typeHover (loc, PrettyBlock(2, true, [], [
            PrettyBlock(0, false, [],
              (case ty of
                 NONE => [PrettyString ("val " ^ Option.getOpt (id, "_"))]
                | SOME ty => [
                  PrettyString ("val " ^ Option.getOpt (id, "_") ^ ":"),
                  PrettyBreak(1, 2), ty])
              @ [PrettyBreak(1, 2), PrettyString "="]),
             PrettyBreak(1, 0), value]))]
        | _ => []
      in thyHov @ help @ out end
    fun crossesNewline (s, e) = let
      val txt = #text text
      fun loop i = i < e andalso
                   (String.sub (txt, i) = #"\n" orelse loop (i + 1))
      in loop s end
    (* Suppress hover on any Built node whose span crosses a newline —
       these are enclosing expressions (e.g. a whole `Proof … QED`
       tactic body typing as `tactic`) whose SML type is uninformative.
       Per-identifier / per-token nodes are single-line and unaffected. *)
    fun fromTree NONE = []
      | fromTree (pt as (SOME (HOL_IDE.Built ((s, e), props, _), _))) =
        if crossesNewline (FixedInt.toInt s, FixedInt.toInt e) then []
        else case process {startPosition = s, endPosition = e} props of
          [] => fromTree (HOL_IDE.builtMoveUp pt)
        | out => out
    val offset' = {startOffset = FixedInt.fromInt startOffset,
                   endOffset = FixedInt.fromInt endOffset}
    val innermost = HOL_IDE.builtNavigateTo' builtTrees offset'
    (* If the cursor sits on raw HOL-quotation text — the innermost
       built-tree node has PQuote — the SML tree hover would walk up
       to the enclosing expansion and return misleading info (e.g.
       "string" for the QUOTE-wrapped body).  Dispatch to the
       HOL-side Preterm hover instead; and if it can't produce a
       hover, return nothing rather than bogus SML type info. *)
    val inQuoteSpan =
      case innermost of
        SOME (HOL_IDE.Built (sp, props, _), _) =>
          if List.exists (fn HOL_IDE.PQuote => true | _ => false) props
          then SOME sp else NONE
      | _ => NONE
    fun fq (s, e) = let
      val qs = FixedInt.toInt s
      val qe = FixedInt.toInt e
      val quote = String.substring (#text text, qs, qe - qs)
      in !LSPExtension.hoverQuotation
           ({uri = uri, lines = #lines text, plugins = plugins,
             ppToString = ppToString},
            {quote = quote, quoteStart = qs, target = startOffset}) end
    fun f () = fromTree innermost
    val out =
      case (out, inQuoteSpan) of
        (_::_, _)     => out
      | ([], SOME sp) => fq sp
      | ([], NONE)    => f ()
    val _ = case out of [] => raise Empty | _ => ()
    fun merge ({range = NONE, ...}, a) = a
      | merge ({range = a, ...}, NONE) = a
      | merge ({range = SOME (lo1, hi1), ...}, SOME (lo2, hi2)) =
        SOME (if leLC lo1 lo2 then lo1 else lo2, if leLC hi1 hi2 then hi2 else hi1)
    val markdown = String.concatWith "\n\n---\n\n" (map #markdown out)
    in SOME {markdown = markdown, range = foldl merge NONE out} end
    handle Empty => NONE

  fun gotoDefinition uri v target = let
    fun fromFileLine {origin, file, line} = let
      val range = ((line, 0), (line+1, 0))
      in {origin = origin, uri = SOME file, range = range, selRange = range} end
    val ({plugins, builtTrees, ...}, text, offset) =
      case getState v target of NONE => raise Empty | SOME s => s
    val ctx = {uri = uri, lines = #lines text, plugins = plugins, fromFileLine = fromFileLine}
    val out = !LSPExtension.gotoDefinition (ctx, offset)
    fun f () = let
      fun fromProps [] r = r
        | fromProps (HOL_IDE.PDeclaredAt loc :: _) (file, ty, _) = (file, ty, SOME loc)
        | fromProps (HOL_IDE.PStructureAt file :: props) (_, ty, df) =
          fromProps props (SOME file, ty, df)
        | fromProps (HOL_IDE.PType ty :: props) (file, _, df) = fromProps props (file, SOME ty, df)
        | fromProps (_ :: props) r = fromProps props r
      val offset' = {startOffset = FixedInt.fromInt offset, endOffset = FixedInt.fromInt offset}
      val (HOL_IDE.Built ((startPosition, endPosition), props, _), _) =
        case HOL_IDE.builtNavigateTo' builtTrees offset' of NONE => raise Empty | SOME pt => pt
      val start = FixedInt.toInt startPosition
      val stop = FixedInt.toInt endPosition
      val origin = SOME (getLineCol (#lines text) start, getLineCol (#lines text) stop)
      val (file, ty, loc) = case fromProps props (NONE, NONE, NONE) of
        (_, _, NONE) => raise Empty
      | (file, ty, SOME loc) => (file, ty, loc)
      fun fromPolyLoc {file, startLine, startPosition, endPosition, ...} =
        if file = "" then let
          val range = (getLineCol (#lines text) startPosition, getLineCol (#lines text) endPosition)
          in {origin = origin, uri = NONE, range = range, selRange = range} end
        else fromFileLine {origin = origin, file = file, line = startLine - 1}
      val newLoc = case (file, ty) of
        (SOME file, SOME _) =>
        !LSPExtension.fixupTheoremLink {uri = file, text = #text text, start = start, stop = stop}
      | _ => NONE
      val newLoc = case newLoc of
        NONE => fromPolyLoc loc
      | SOME {file, line} => fromFileLine {origin = origin, file = file, line = line}
      in [newLoc] end
    in case out of [] => f () | _ => out end
    handle Empty => []

  (* Unlike `getState', goalStateAtPos doesn't gate on the compile
     having reached the cursor -- the walker uses `declSnapshots'
     (which survive `carryOverSnapshots') for Context and parses
     the Proof body directly from the current buffer text.
     Requiring `pos >= offset' would stall the auto-follow-cursor
     pane for the ~300 ms debounce after every keystroke. *)
  fun goalStateAtPos uri ({lastTrees, ...}:file_data) target = let
    val {parse, text} = !lastTrees
    val {plugins, declSnapshots, ...} = parse
    val offset = fromLineCol (#lines text) target
    fun ppToString pp = let
      val mds = DArray.new (8, "")
      val _ = PolyML.prettyPrint (fn s => DArray.push (mds, s), textWidth) pp
      in concat (DArray.toList mds) end
    val ctx = {uri = uri, lines = #lines text, plugins = plugins,
               ppToString = ppToString}
    (* Largest declSnapshot with endByte < theoremStart.  Restoring
       this before invoking the walker means the walker's tactics
       (in particular `simp[]` via `srw_ss()`) see the same Context
       — including srw_ss extensions — that existed when the file
       compile reached the theorem's dec.  Without this, later
       `export_rewrites` in the same file skew simp's normal form
       and slow tactics like METIS_TAC to a crawl. *)
    fun snapBefore ts = List.foldl
      (fn (s, best) =>
        if #endByte s >= ts then best
        else case best of
               NONE => SOME s
             | SOME b => if #endByte s > #endByte b then SOME s else best)
      NONE declSnapshots
    in case findEnclosingTheorem (#text text) offset of
         NONE => NONE
       | SOME (thm as {quoteStart, ...}) =>
         let val restoreLater = !LSPExtension.captureCompileSnap ()
             val () = case snapBefore quoteStart of
               NONE => ()
             | SOME s => !LSPExtension.restoreCompileSnap (#compileSnap s)
             val r = !LSPExtension.goalStateAtPos (ctx, thm)
                     handle e => (restoreLater (); raise e)
             val () = restoreLater ()
         in r end
    end handle Empty => NONE

  fun eval id {uri, code, incr, holdep} = let
    val lines = mkLineCounter code

    val mods = case holdep of HoldepNone => [] | _ => getHoldep code
    val files = DArray.new (8, "")
    val _ = app (fn m =>
      loadPlan (fn f => DArray.push (files, f)) m
      handle e => logMessage ("ignoring load error: " ^ exnMessage e)) mods
    val _ = case holdep of
      HoldepList => send (mkNotif "$/eval/holdep" (fn print => (
        print "{\"uri\":"; encString uri print;
        print ",\"id\":"; encReqId id print;
        print ",\"files\":"; encDArray encString files print; print "}")))
    | _ => ()
    val _ = DArray.app (fn f =>
      qquse f handle e => logMessage ("ignoring load error: " ^ exnMessage e)) files
    val _ = case holdep of
      HoldepList => send (mkNotif "$/eval/holdepCompleted" (fn print => (
        print "{\"uri\":"; encString uri print;
        print ",\"id\":"; encReqId id print; print "}")))
    | _ => ()

    fun encReport (Error {hard, pos, msg}) print = (
        print "{\"kind\":\"error\"";
        print ",\"hard\":"; print (if hard then "true" else "false");
        print ",\"pos\":"; encRangeLC lines pos print;
        print ",\"msg\":"; msg print; print "}")
      | encReport (CompilerOut (pos, s)) print = (
        print "{\"kind\":\"compilerOut\"";
        print ",\"pos\":"; encPosLC lines pos print;
        print ",\"body\":"; encString (concat (rev s)) print; print "}")
      | encReport (ToplevelOut (pos, s)) print = (
        print "{\"kind\":\"toplevelOut\"";
        print ",\"pos\":"; encPosLC lines pos print;
        print ",\"body\":"; encString (concat (rev s)) print; print "}")
      | encReport (Progress i) print = (
        print "{\"kind\":\"compileProgress\"";
        print ",\"pos\":"; encPosLC lines i print; print "}")
      | encReport Completed print = print "{\"kind\":\"compileCompleted\"}"
      | encReport Interrupted print = print "{\"kind\":\"interrupted\"}"

    val compile = compileForReport uri code 0 (ref 0) (fn _ => ()) (fn _ => ())
    in
      case incr of
        IncrNone => let
        val buf = DArray.new (8, Completed)
        val _ = compile (fn Progress _ => () | msg => mergeInto msg buf) handle
          Thread.Interrupt => DArray.push (buf, Interrupted)
        in Ok (encDArray encReport buf) end
      | IncrChunk => (
        spawnJobCore id (fn () => let
          val buf = DArray.new (8, Completed)
          val prev = ref 0
          fun clearBuf complete i = let
            fun params print = (
              print "{\"id\":"; encReqId id print;
              print ",\"pos\":"; encRangeLC lines (!prev before prev := i, i) print;
              print ",\"out\":"; encDArray encReport buf print;
              if complete then print ",\"complete\":true" else (); print "}")
            in send (mkNotif "$/eval/P" params); DArray.clear buf end
          val _ = compile (fn Progress i => clearBuf false i | msg => mergeInto msg buf)
            handle Thread.Interrupt => DArray.push (buf, Interrupted)
          in clearBuf true (size code) end);
        Ok encNull)
      | IncrStream => (
        spawnJobCore id (fn () => let
          fun sendMsg msg = send (mkNotif "$/eval/1" (fn print => (
            print "{\"id\":"; encReqId id print;
            print ",\"out\":"; encReport msg print; print "}")))
          val ok = (compile sendMsg; true) handle
            Thread.Interrupt => (sendMsg Interrupted; false)
          in if ok then sendMsg Completed else () end);
        Ok encNull)
    end

  fun recvExit () =
    case recv () of
      Notification {method = "exit", ...} => ()
    | _ => (diag "ignoring message after shutdown"; recvExit ())

  exception Shutdown
  fun main () = (
    (case recv () of
      Request {method = "shutdown", id, ...} => (
        diag "received shutdown request";
        send (mkResponse id (Ok encNull));
        recvExit ();
        raise Shutdown)
    | Request {method = "textDocument/hover", id, params} =>
      spawnJob id params textDocumentPositionParams (fn {uri, pos} => let
        val hov = case withFileInfo (fn fileInfo => (fileInfo, Binarymap.peek (fileInfo, uri))) of
          NONE => NONE
        | SOME v => hover uri v (pos, pos)
        in Ok (encOrNull encHover hov) end)
    | Request {method = "textDocument/definition", id, params} =>
      spawnJob id params textDocumentPositionParams (fn {uri, pos} => let
        val ls = case withFileInfo (fn fileInfo => (fileInfo, Binarymap.peek (fileInfo, uri))) of
          NONE => []
        | SOME v => gotoDefinition uri v pos
        in Ok (encArray (encLocationLink uri) ls) end)
    | Request {method = "$/setConfig", id, params} => ((
      case JSONDecode.decode (JSONDecode.fieldO "elabOn" elabOn) params of
        NONE => ()
      | SOME v => elabOnRef := v;
      send (mkResponse id (Ok encNull)))
      handle JSONDecode.JSONError _ =>
        send (mkResponse id (mkErr InvalidParams "json decode failed")))
    | Request {method = "$/eval", id, params} =>
      spawnJob id params evalParams (eval id)
    | Request {method = "$/hol/goalState", id, params} =>
      spawnJob id params textDocumentPositionParams (fn {uri, pos} => let
        val (v_opt, resp) = case withFileInfo (fn fileInfo =>
              (fileInfo, Binarymap.peek (fileInfo, uri))) of
            NONE => (NONE, NONE)
          | SOME v => (SOME v, goalStateAtPos uri v pos)
        (* Fold the walker's failure/success into per-file walker
           diagnostics keyed by theorem name so a user-fix removes
           the squiggle without waiting for the next compile.  Emit
           publishDiagnostics whenever the walker's slot changes. *)
        val () = case (v_opt, resp) of
            (SOME (v: file_data), SOME {theorem, failedRange, error, ...}) => let
              val wd = !(#walkerDiags v)
              val prev = Binarymap.peek (wd, theorem)
              val next = case (failedRange, error) of
                  (SOME (s, e), SOME msg) => SOME (Error {
                    hard = true, pos = (s, e), msg = encString msg })
                | _ => NONE
              val changed = case (prev, next) of
                  (NONE, NONE) => false
                | (SOME _, NONE) => true
                | (NONE, SOME _) => true
                | _ => true  (* re-emit even if same theorem — text may differ *)
              val () = case next of
                  NONE => #walkerDiags v := Binarymap.foldl
                    (fn (k, r, m) => if k = theorem then m
                                     else Binarymap.insert (m, k, r))
                    (Binarymap.mkDict String.compare) wd
                | SOME r => #walkerDiags v := Binarymap.insert (wd, theorem, r)
            in if changed then publishAllDiagnostics uri v else () end
          | _ => ()
        in Ok (encOrNull encGoalStateResponse resp) end)
    | Request {method, id, ...} =>
      send (mkResponse id (mkErr InvalidRequest ("unknown method: " ^ method)))
    | Notification {method = "$/cancelRequest", params} => let
      val id = JSONDecode.decode cancelParams params
      in app (fn (j,th) => if j = id then Thread.interrupt th else ()) (jobs I) end
    | Notification {method = "textDocument/didOpen", params} => let
      val {uri, text, version} = JSONDecode.decode textDocumentParams params
      val (v, existed) = withFileInfo (fn fileInfo =>
        case Binarymap.peek (fileInfo, uri) of
          SOME v => (fileInfo, (v, true))
        | NONE => let val v = newFile text version
                  in (Binarymap.insert (fileInfo, uri, v), (v, false)) end)
      val () = if existed then applyEdit v version [{range = NONE, text = text}]
               else augmentLoadPathForUri uri
      in if !elabOnRef = ElabOnChange then startCompile uri v else () end
    | Notification {method = "textDocument/didChange", params} => let
      val {uri, version, changes} = JSONDecode.decode didChangeParams params
      val _ = case withFileInfo (fn fileInfo => (fileInfo, Binarymap.peek (fileInfo, uri))) of
        NONE => ()
      | SOME v => (
        applyEdit v version changes;
        (* Debounce so keystroke bursts don't kick off a compile per
           character; only the last edit in a 300 ms window fires. *)
        if !elabOnRef = ElabOnChange then scheduleCompile uri v else ())
      in () end
    | Notification {method = "textDocument/didClose", params} => let
      val uri = JSONDecode.decode textDocumentId params
      val _ = withFileInfo (fn fileInfo => (
        case Binarymap.peek (fileInfo, uri) of
          NONE => (fileInfo, ())
        | SOME {compile, ...} =>
          (stopCompile compile; (#1 (Binarymap.remove (fileInfo, uri)), ()))))
      in () end
    | Notification {method = "textDocument/didSave", params} =>
      if !elabOnRef <> ElabOnSave then () else let
        val uri = JSONDecode.decode textDocumentId params
        val _ = case withFileInfo (fn fileInfo => (fileInfo, Binarymap.peek (fileInfo, uri))) of
          NONE => ()
        | SOME v => startCompile uri v
        in () end
    | Response _ => diag "response to unknown request"
    | Notification {method, ...} => diag ("unknown method: " ^ method))
    handle
      e as Shutdown => PolyML.Exception.reraise e
    | e => logMessage ("ignored exception " ^ exnMessage e);
    main ())
  in
    main () handle
      Shutdown => ()
    | Channel.Disconnected => diag "early abort"
  end

end (* struct *)
