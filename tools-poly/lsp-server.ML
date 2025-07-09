signature LSPServer =
sig
  val start : {diag: string -> unit} -> unit
end;

(* load "JSONDecode"; *)

structure LSPServer :> LSPServer =
struct

(* structure Thread = PolyThread; *)
open Thread LSPExtension

fun I x = x

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

fun encLocationLink uri0 {origin, uri, range, selRange} print = (
  print "{\"targetUri\":"; encString (Option.getOpt (uri, uri0)) print;
  print ",\"targetRange\":"; encRange encPosition range print;
  print ",\"targetSelectionRange\":"; encRange encPosition selRange print;
  case origin of
    NONE => ()
  | SOME origin => (print ",\"originSelectionRange\":"; encRange encPosition origin print);
  print "}")

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

  val send = let
    val (send, recv) = Channel.channel ()
    fun writerThread () = let
      val msg: encode message = Channel.recv recv
      val buf = ref []
      val () = encMessage msg (fn s => buf := s :: !buf)
      fun write (n, a :: buf, acc) = write (n + size a, buf, a :: acc)
        | write (n, [], acc) =
          TextIO.output (TextIO.stdOut,
            String.concat ("Content-Length: " :: Int.toString n :: "\r\n\r\n" :: acc))
      in write (0, !buf, []); writerThread () end
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

exception Todo
fun start {diag} = let
  val _ = PolyML.print_depth 100
  val conn as {send, recv} = stdioConnection ()
  val _ (*clientCapabilities*) = initialize conn (concat [
    "{\"textDocumentSync\":1", (* 1 = Full *)
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

  datatype report =
    Error of {hard: bool, pos: range, msg: encode}
  | CompilerOut of int * string list
  | ToplevelOut of int * string list
  | Progress of int
  | Completed
  | Interrupted

  type parse_data = {
    done: bool,
    pos: int,
    mlParseTrees: PolyML.parseTree list,
    diags: report DArray.darray,
    plugins: plugin_data}
  fun emptyParseData n: parse_data = {
    done = false, pos = 0, mlParseTrees = [], diags = DArray.new (n, Completed),
    plugins = emptyPluginData }
  fun addParseTree t {done, pos, mlParseTrees, diags, plugins} =
    {done = done, pos = pos, mlParseTrees = t :: mlParseTrees, diags = diags, plugins = plugins}
  fun setParsePos pos {done, pos = _, mlParseTrees, diags, plugins} =
    {done = done, pos = pos, mlParseTrees = mlParseTrees, diags = diags, plugins = plugins}
  fun setParseDone pos {done = _, pos = _, mlParseTrees, diags, plugins} =
    {done = true, pos = pos, mlParseTrees = mlParseTrees, diags = diags, plugins = plugins}
  fun setPlugins plugins {done, pos, mlParseTrees, diags, plugins = _} =
    {done = done, pos = pos, mlParseTrees = mlParseTrees, diags = diags, plugins = plugins}

  type text_data = {text: string, version: int, lines: lines}
  type compile_data = {parse: parse_data ref, text: text_data, thread: Thread.thread}
  type file_data = {
    compile: compile_data option ref,
    lastTrees: {parse: parse_data, text: text_data} ref}
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
    in {compile = ref NONE, lastTrees = ref {parse = emptyParseData 0, text = text}} end

  fun stopCompile r = case !r of
    NONE => ()
  | SOME {thread, ...} => (r := NONE; Thread.interrupt thread)

  fun applyEdit ({compile, lastTrees}:file_data) version changes = let
    val _ = stopCompile compile
    fun getLines text NONE = mkLineCounter text
      | getLines _ (SOME lines) = lines
    fun applyText [] data = data
      | applyText ({range = NONE, text}::cs) _ = applyText cs (emptyParseData 0, text, NONE)
      | applyText ({range = SOME (from, to), text}::cs) (_, base, lines) = let
        val lines = getLines base lines
        val (from, to) = (fromLineCol lines from, fromLineCol lines to)
        val text = Substring.concat [
          Substring.substring (base, 0, from),
          Substring.full text,
          Substring.substring (base, to, size base - to)]
        in applyText cs (emptyParseData 0, text, NONE) end
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
      NONE => (i, i)
    | SOME l => locToRange l,
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
    val {read, ...} = HolParser.stringToReader {quietOpen = false} text
    in
      Binarymap.foldr (fn (a, _, r) => a :: r) [] (Holdep_tokens.reader_deps ("", read))
      handle _ => []
    end

  fun compileForReport uri code lastPos mlParseTree report = let
    val _ = HOL_IDE.initialize {
      text = code,
      filename = uri,
      parseError = fn pos => fn s => report (Error {hard = true, pos = pos, msg = encString s}),
      compilerOut = fn s => report (CompilerOut (!lastPos, [s])),
      toplevelOut = fn s => report (ToplevelOut (!lastPos, [s])),
      progress = fn i => (lastPos := i; report (Progress i)),
      error = fn {hard, location, message, ...} => report (Error {
        hard = hard, pos = locToRange location, msg = encPretty textWidth message}),
      runtimeExn = fn e => report (exnToReport (!lastPos) e),
      mlParseTree = mlParseTree,
      holParseTree = fn _ => () }
    in lastPos := size code end

  fun startCompile uri ({compile, lastTrees}:file_data) =
    if #done (#parse (!lastTrees)) then () else let
    val _ = stopCompile compile
    val {text as {lines, ...}, parse = {diags = oldDiags, ...}} = !lastTrees
    val trees = ref (emptyParseData 8)

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
          val x = DArray.sub (diags, i)
          val keep = case x of Error {pos = (start, _), ...} => start >= pos | _ => true
          in if keep then DArray.push (newDiags, x) else (); loop (i+1) end
        in loop 0; DArray.replace (oldDiags, newDiags) end

      fun sendDiags () =
        send (mkNotif "textDocument/publishDiagnostics" (fn print => (
          print "{\"uri\":"; encString uri print;
          print ",\"version\":"; encInt (#version text) print;
          print ",\"diagnostics\":"; encDArray encDiag oldDiags print;
          print "}")))

      val ls = ref (beforeCompile ())
      val lastPos = ref 0
      fun process (Progress i) = (
          trees := setParsePos i (!trees);
          afterCompile (!lastPos before lastPos := i, i) (!ls);
          send (mkNotif "$/compileProgress" (fn print => (
            print "{\"uri\":"; encString uri print;
            print ",\"pos\":"; encPosLC lines i print;
            print "}")));
          updateDiags i;
          sendDiags ();
          ls := beforeCompile ())
        | process (CompilerOut (_, ss)) = logMessage (concat (rev ss))
        | process (ToplevelOut (_, ss)) = logMessage (concat (rev ss))
        | process Completed = raise Bind
        | process Interrupted = raise Bind
        | process (msg as Error _) = DArray.push (#diags (!trees), msg)
      fun processTree t = trees := addParseTree t (!trees)
      in
        compileForReport uri (#text text) lastPos processTree process;
        afterCompile (!lastPos, size (#text text)) (!ls);
        send (mkNotif "$/compileCompleted" (fn print => (
          print "{\"uri\":"; encString uri print; print "}")));
        lastTrees := {text = text, parse = setParseDone (size (#text text)) (!trees)}
      end
      handle Thread.Interrupt =>
        send (mkNotif "$/compileInterrupted" (fn print => (
          print "{\"uri\":"; encString uri print; print "}"))));
      compile := NONE)
    val thread = Thread.fork (compileThread, [Thread.InterruptState Thread.InterruptDefer])
    in compile := SOME {parse = trees, text = text, thread = thread} end

  fun hover {uri, pos} = let
    (* TODO *)
    in Ok encNull end

  fun gotoDefinition uri {compile, lastTrees} target = let
    fun getIfValid {parse as {pos, ...}, text} =
      if pos > 0 then let
        val offset = fromLineCol (#lines text) target
        in if offset <= pos then SOME (parse, text, offset) else NONE end
      else NONE
    val state = case !compile of
      SOME {parse, text, ...} => getIfValid {parse = !parse, text = text}
    | NONE => NONE
    val state = case state of NONE => getIfValid (!lastTrees) | state => state
    fun fromFileLine {origin, file, line} = let
      val range = ((line, 0), (line+1, 0))
      in {origin = origin, uri = SOME file, range = range, selRange = range} end
    val ({plugins, mlParseTrees, ...}, text, offset) =
      case state of NONE => raise Empty | SOME s => s
    val ctx = {uri = uri, lines = #lines text, plugins = plugins, fromFileLine = fromFileLine}
    fun fromProps [] r = r
      | fromProps (PolyML.PTdeclaredAt loc :: _) (file, ty, _) = (file, ty, SOME loc)
      | fromProps (PolyML.PTstructureAt {file,...} :: props) (_, ty, df) =
        fromProps props (SOME file, ty, df)
      | fromProps (PolyML.PTtype ty :: props) (file, _, df) = fromProps props (file, SOME ty, df)
      | fromProps (_ :: props) r = fromProps props r
    val out = !LSPExtension.gotoDefinition (ctx, offset)
    val out = case out of
      [] => let
      val offset' = {startOffset = FixedInt.fromInt offset, endOffset = FixedInt.fromInt offset}
      val ({startPosition, endPosition, ...}, props) =
        case HOL_IDE.navigateTo' mlParseTrees offset' of NONE => raise Empty | SOME pt => pt
      val start = FixedInt.toInt startPosition
      val stop = FixedInt.toInt endPosition
      val origin = SOME (getLineCol (#lines text) start, getLineCol (#lines text) stop)
      val (file, ty, loc) = case fromProps props (NONE, NONE, NONE) of
        (_, _, NONE) => raise Empty
      | (file, ty, SOME loc) => (file, ty, loc)
      fun fromPolyLoc {file, startLine, startPosition, endPosition, ...} =
        if file = "" then let
          val start = FixedInt.toInt startPosition
          val stop = FixedInt.toInt endPosition
          val range = (getLineCol (#lines text) start, getLineCol (#lines text) stop)
          in {origin = origin, uri = NONE, range = range, selRange = range} end
        else fromFileLine {origin = origin, file = file, line = FixedInt.toInt startLine - 1}
      val newLoc = case (file, ty) of
        (SOME file, SOME _) =>
        !LSPExtension.fixupTheoremLink {uri = file, text = #text text, start = start, stop = stop}
      | _ => NONE
      val newLoc = case newLoc of
        NONE => fromPolyLoc loc
      | SOME {file, line} => fromFileLine {origin = origin, file = file, line = line}
      in [newLoc] end
    | _ => out
    in out end
    handle Empty => []

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

    val compile = compileForReport uri code (ref 0) (fn _ => ())
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
      spawnJob id params textDocumentPositionParams hover
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
    | Request {method, id, ...} =>
      send (mkResponse id (mkErr InvalidRequest ("unknown method: " ^ method)))
    | Notification {method = "$/cancelRequest", params} => let
      val id = JSONDecode.decode cancelParams params
      in app (fn (j,th) => if j = id then Thread.interrupt th else ()) (jobs I) end
    | Notification {method = "textDocument/didOpen", params} => let
      val {uri, text, version} = JSONDecode.decode textDocumentParams params
      val v = withFileInfo (fn fileInfo =>
        case Binarymap.peek (fileInfo, uri) of
          SOME v => (fileInfo, SOME v)
        | NONE => (Binarymap.insert (fileInfo, uri, newFile text version), NONE))
      in case v of NONE => () | SOME v => applyEdit v version [{range = NONE, text = text}] end
    | Notification {method = "textDocument/didChange", params} => let
      val {uri, version, changes} = JSONDecode.decode didChangeParams params
      val _ = case withFileInfo (fn fileInfo => (fileInfo, Binarymap.peek (fileInfo, uri))) of
        NONE => ()
      | SOME v => (
        applyEdit v version changes;
        if !elabOnRef = ElabOnChange then startCompile uri v else ())
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
