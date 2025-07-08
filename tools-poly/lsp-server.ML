signature LSPServer =
sig
  val start : {diag: string -> unit} -> unit
end;

(* load "JSONDecode"; *)

structure LSPServer :> LSPServer =
struct

(* structure Thread = PolyThread; *)
open Thread

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

fun encLocation {uri, range} print = (
  print "{\"uri\":"; encString uri print;
  print ",\"range\":"; encRange encPosition range print;
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

val evalParams = map3 (fn (uri, code, incr) => {uri = uri, code = code, incr = incr})
  (field "uri" string, field "code" string, fieldD "incr" incr IncrNone)

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

exception Disconnected
structure Channel: sig
type 'a sender
type 'a receiver
val channel: unit -> 'a sender * 'a receiver
val send: 'a sender -> 'a -> unit
val closeSender: 'a sender -> exn option -> unit
val recv: 'a receiver -> 'a
end = struct

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

fun mkLineCounter str = let
  fun loop i ls =
    if i >= String.size str then Vector.fromList (List.rev ls)
    else
      let val c = String.sub (str, i)
      in loop (i+1) (if c = #"\n" then i+1::ls else ls) end
  in loop 0 [] end

fun partitionPoint len pred = let
  fun loop start len =
    if len = 0 then start
    else let
      val half = len div 2
      val middle = start + half
      in
        if pred middle
        then loop (middle + 1) (len - (half + 1))
        else loop start half
      end
  in loop 0 len end

fun getLineCol lines index = let
  val line = partitionPoint (Vector.length lines) (fn i => Vector.sub (lines, i) <= index)
  in (line, index - (if line = 0 then 0 else Vector.sub (lines, line - 1))) end

fun fromLineCol lines (line, col) =
  if line = 0 then col else Vector.sub (lines, line - 1) + col

type range = int * int

fun encPosLC lines = encPosition o getLineCol lines
val encRangeLC = encRange o encPosLC
fun locToRange ({startPosition,endPosition,...}:PolyML.location) =
  (FixedInt.toInt startPosition, FixedInt.toInt endPosition)
(* fun encLocLC lines = encRangeLC lines o locToRange *)

fun encPretty textWidth pp print = let
  fun print' s = encStringContents s print
  in print "\""; PolyML.prettyPrint (print', textWidth) pp; print "\"" end

structure DArray: sig

type 'a darray
val new: int * 'a -> 'a darray
val clear: 'a darray -> unit
val sub: 'a darray * int -> 'a
val update: 'a darray * int * 'a -> unit
val clone: 'a darray * int -> 'a darray
val push: 'a darray * 'a -> unit
val size: 'a darray -> int
val last: 'a darray -> 'a option
val setLast: 'a darray * 'a -> unit
val app: ('a -> unit) -> 'a darray -> unit
type 'a slice = 'a ArraySlice.slice
val slice: 'a darray * int * int option -> 'a slice
val copy: {src: 'a slice, dst: 'a darray, di: int} -> unit
val append: 'a darray * 'a slice -> unit
val replace: 'a darray * 'a darray -> unit

end = struct

type 'a darray = ('a array * int * 'a) ref
fun new (cap, v) = ref (Array.array (cap, v), 0, v)
fun clear (r as ref (a, _, dflt)) = r := (a, 0, dflt)
fun sub (ref (a, sz, _), i) = if i < sz then Array.sub (a, i) else raise Subscript
fun update (ref (a, sz, _), i, v) = if i < sz then Array.update (a, i, v) else raise Subscript
fun cloneCore ((a, sz, dflt), cap) = let
  val a' = Array.array (cap, dflt)
  val _ = ArraySlice.copy {src = ArraySlice.slice (a, 0, SOME sz), dst = a', di = 0}
  in (a', sz, dflt) end
fun clone (ref a, cap) = ref (cloneCore (a, cap))
fun ensureCapacity (r as (a, _, _), cap) =
  if cap <= Array.length a then r else cloneCore (r, Int.max (cap, Array.length a * 3 div 2))
fun push (r as ref (a as (_, sz, _:'a)), v) = let
  val (a, sz, dflt) = ensureCapacity (a, sz + 1)
  val _ = Array.update (a, sz, v)
  in r := (a, sz+1, dflt) end
fun size (ref (_, sz, _)) = sz
fun last a = case size a of 0 => NONE | sz => SOME (sub (a, sz-1))
fun setLast (a, v) = update (a, size a - 1, v)
fun app f a = let
  val n = size a
  fun go i = if i < n then (f (sub (a, i)); go (i+1)) else ()
  in go 0 end

type 'a slice = 'a ArraySlice.slice
fun slice (ref (a, sz, _), i, SOME len) =
    if i+len <= sz then ArraySlice.slice (a, i, SOME len) else raise Subscript
  | slice (ref (a, sz, _), i, NONE) =
    if i <= sz then ArraySlice.slice (a, i, SOME (sz - i)) else raise Subscript

fun copy {src, dst = ref (a, sz, _), di} =
  if di + ArraySlice.length src > sz then raise Subscript
  else ArraySlice.copy {src = src, dst = a, di = di}

fun append (r as ref (a as (_, sz, _)), v) = (
  r := ensureCapacity (a, sz + ArraySlice.length v);
  ArraySlice.copy {src = v, dst = #1 (!r), di = sz})
fun replace (r, ref a) = r := a

end

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
    plugins: (string, Universal.universal) Binarymap.dict}
  fun emptyParseData n: parse_data = {
    done = false, pos = 0, mlParseTrees = [], diags = DArray.new (n, Completed),
    plugins = Binarymap.mkDict String.compare }
  fun addParseTree t {done, pos, mlParseTrees, diags, plugins} =
    {done = done, pos = pos, mlParseTrees = t :: mlParseTrees, diags = diags, plugins = plugins}
  fun setParsePos pos {done, pos = _, mlParseTrees, diags, plugins} =
    {done = done, pos = pos, mlParseTrees = mlParseTrees, diags = diags, plugins = plugins}
  fun setParseDone pos {done = _, pos = _, mlParseTrees, diags, plugins} =
    {done = true, pos = pos, mlParseTrees = mlParseTrees, diags = diags, plugins = plugins}

  type text_data = {text: string, version: int, lines: int vector}
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

  fun mergeInto msg buf =
    case (msg, DArray.last buf) of
      (CompilerOut (pos', [s]), SOME (CompilerOut (pos, ss))) =>
      if pos = pos' then DArray.setLast (buf, CompilerOut (pos, s :: ss))
      else DArray.push (buf, msg)
    | (ToplevelOut (pos', [s]), SOME (ToplevelOut (pos, ss))) =>
      if pos = pos' then DArray.setLast (buf, ToplevelOut (pos, s :: ss))
      else DArray.push (buf, msg)
    | _ => DArray.push (buf, msg)

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
      runtimeExn = fn e => report (Error {hard = true,
        pos = case PolyML.Exception.exceptionLocation e of
          NONE => (case !lastPos of i => (i, i))
        | SOME l => locToRange l,
        msg = encPretty textWidth (exceptionMessage e)}),
      mlParseTree = mlParseTree,
      holParseTree = fn _ => () }
    in lastPos := size code end

  fun startCompile uri ({compile, lastTrees}:file_data) =
    if #done (#parse (!lastTrees)) then () else let
    val _ = stopCompile compile
    val {text as {lines, ...}, parse = {diags = oldDiags, ...}} = !lastTrees
    val trees = ref (emptyParseData 8)
    fun compileThread () = ((let
      val lastPos = ref 0
      fun updateDiags pos = let
        val {diags, ...} = !trees
        val n = DArray.size oldDiags
        val newDiags = DArray.clone (diags, DArray.size diags + n)
        fun loop i = if i >= n then () else let
          val x = DArray.sub (diags, i)
          val keep = case x of Error {pos = (start, _), ...} => start >= pos | _ => true
          in if keep then DArray.push (newDiags, x) else (); loop (i+1) end
        in loop 0; DArray.replace (oldDiags, newDiags) end

      fun encDiag (Error {hard, pos, msg}) print = (
          print "{\"range\":"; encRangeLC lines pos print;
          print ",\"severity\":"; encInt (if hard then ErrorSeverity else WarnSeverity) print;
          print ",\"message\":"; msg print; print "}")
        | encDiag _ _ = raise Fail "unexpected report kind"

      fun sendDiags () =
        send (mkNotif "textDocument/publishDiagnostics" (fn print => (
          print "{\"uri\":"; encString uri print;
          print ",\"version\":"; encInt (#version text) print;
          print ",\"diagnostics\":"; encDArray encDiag oldDiags print;
          print "}")))

      fun process (Progress i) = (
          trees := setParsePos i (!trees);
          send (mkNotif "$/compileProgress" (fn print => (
            print "{\"uri\":"; encString uri print;
            print ",\"pos\":"; encPosLC lines i print;
            print "}")));
          updateDiags i; sendDiags ())
        | process (CompilerOut (_, ss)) = logMessage (concat (rev ss))
        | process (ToplevelOut (_, ss)) = logMessage (concat (rev ss))
        | process Completed = raise Bind
        | process Interrupted = raise Bind
        | process (msg as Error _) = DArray.push (#diags (!trees), msg)
      fun processTree t = trees := addParseTree t (!trees)
      in
        compileForReport uri (#text text) lastPos processTree process;
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

  fun gotoDefinition {uri, pos} = let
    (* TODO *)
    val ls = []
    in Ok (encArray encLocation ls) end

  fun eval id {uri, code, incr} = let
    val lines = mkLineCounter code

    fun encReport (Error {hard, pos, msg}) print = (
        print "{\"kind\":\"error\"";
        print ",\"hard\":"; print (if hard then "true" else "false");
        print ",\"pos\":"; encRangeLC lines pos print;
        print ",\"msg\":"; msg print;
        print "}")
      | encReport (CompilerOut (pos, s)) print = (
        print "{\"kind\":\"compilerOut\"";
        print ",\"pos\":"; encPosLC lines pos print;
        print ",\"body\":"; encString (concat (rev s)) print;
        print "}")
      | encReport (ToplevelOut (pos, s)) print = (
        print "{\"kind\":\"toplevelOut\"";
        print ",\"pos\":"; encPosLC lines pos print;
        print ",\"body\":"; encString (concat (rev s)) print;
        print "}")
      | encReport (Progress i) print = (
        print "{\"kind\":\"compileProgress\"";
        print ",\"pos\":"; encPosLC lines i print;
        print "}")
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
      spawnJob id params textDocumentPositionParams gotoDefinition
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
    | Disconnected => diag "early abort"
  end

end (* struct *)
