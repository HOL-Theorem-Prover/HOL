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

datatype incremental = IncrNone | IncrChunk | IncrStream

local
  open JSONDecode JSON
  val error = map3 (fn (code, message, data) => {code = code, message = message, data = data})
    (field "code" int, field "message" string, fieldO "data" raw)
  exception NotIncr
  val incr = ofRaw (fn jv =>
    case decode int jv of
      0 => IncrNone | 1 => IncrChunk | 2 => IncrStream
    | _ => raise JSONError (NotIncr, jv))
in
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

val position = tuple2 (field "line" int, field "character" int)
val textDocumentPositionParams =
  map2 (fn (uri, pos) => {uri = uri, pos = pos})
    (field "textDocument" (field "uri" string), field "position" position)

val cancelParams = field "id" req_id
val evalParams = map3 (fn (uri, code, incr) => {uri = uri, code = code, incr = incr})
  (field "uri" string, field "code" string, fieldD "incr" incr IncrNone)
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

(* fun fromLineCol lines (line, col) =
  if line = 0 then col else Vector.sub (lines, line - 1) + col *)

type range = int * int

fun encPosLC lines = encPosition o getLineCol lines
val encRangeLC = encRange o encPosLC
(* fun encLocLC lines ({startPosition,endPosition,...}:PolyML.location) =
  encRangeLC lines (startPosition, endPosition) *)

fun encPretty textWidth pp print = let
  fun print' s = encStringContents s print
  in print "\""; PolyML.prettyPrint (print', textWidth) pp; print "\"" end

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

  fun hover {uri, pos} = let
    (* TODO *)
    in Ok encNull end

  fun gotoDefinition {uri, pos} = let
    (* TODO *)
    val ls = []
    in Ok (encArray encLocation ls) end

  fun eval id {uri, code, incr} = let
    val lines = mkLineCounter code

    datatype report =
      Error of {hard: bool, pos: range, msg: encode}
    | CompilerOut of string
    | ToplevelOut of string
    | Progress of int
    | Completed
    | Interrupted

    fun encReport (Error {hard, pos, msg}) print = (
        print "{\"kind\":\"error\"";
        print ",\"hard\":"; print (if hard then "true" else "false");
        print ",\"pos\":"; encRangeLC lines pos print;
        print ",\"msg\":"; msg print;
        print "}")
      | encReport (CompilerOut s) print = (
        print "{\"kind\":\"compilerOut\"";
        print ",\"body\":"; encString s print;
        print "}")
      | encReport (ToplevelOut s) print = (
        print "{\"kind\":\"toplevelOut\"";
        print ",\"body\":"; encString s print;
        print "}")
      | encReport (Progress i) print = (
        print "{\"kind\":\"compileProgress\"";
        print ",\"pos\":"; encPosLC lines i print;
        print "}")
      | encReport Completed print = print "{\"kind\":\"compileCompleted\"}"
      | encReport Interrupted print = print "{\"kind\":\"interrupted\"}"

    fun exceptionMessage (exn: exn) =
      PolyML.PrettyBlock(0, false, [], [
        PolyML.PrettyBlock(0, false, [], [PolyML.PrettyString "Exception"]),
        PolyML.PrettyBreak(1, 3),
        PolyML.prettyRepresentation(exn, printDepth),
        PolyML.PrettyBreak(1, 3),
        PolyML.PrettyString "raised"])

    val lastPos = ref 0
    fun compile report = (
      HOL_IDE.initialize {
        text = code,
        filename = uri,
        parseError = fn pos => fn s => report (Error {hard = true, pos = pos, msg = encString s}),
        compilerOut = report o CompilerOut,
        toplevelOut = report o ToplevelOut,
        progress = fn i => (lastPos := i; report (Progress i)),
        error = fn {hard, location = {startPosition = p1, endPosition = p2, ...}, message, ...} =>
          report (Error {hard = hard, pos = (p1, p2), msg = encPretty textWidth message}),
        runtimeExn = fn e => report (Error {hard = true,
          pos = case PolyML.Exception.exceptionLocation e of
            NONE => (case !lastPos of i => (i, i))
          | SOME {startPosition, endPosition, ...} => (startPosition, endPosition),
          msg = encPretty textWidth (exceptionMessage e)}),
        mlParseTree = fn _ => (),
        holParseTree = fn _ => () };
      lastPos := size code)

    in
      case incr of
        IncrNone => let
        val buf = ref []
        val _ = compile (fn Progress _ => () | msg => buf := msg :: !buf) handle
          Thread.Interrupt => buf := Interrupted :: !buf
        in Ok (encArray encReport (rev (!buf))) end
      | IncrChunk => (
        spawnJobCore id (fn () => let
          val buf = ref []
          val prev = ref 0
          fun clearBuf complete = let
            val buf = rev (!buf before buf := [])
            fun params print = (
              print "{\"id\":"; encReqId id print;
              print ",\"pos\":"; encRangeLC lines (!prev before prev := !lastPos, !lastPos) print;
              print ",\"out\":"; encArray encReport buf print;
              if complete then print ",\"complete\":true" else (); print "}")
            in send (mkNotif "$/eval/P" params) end
          val _ = compile (fn Progress _ => clearBuf false | msg => buf := msg :: !buf) handle
            Thread.Interrupt => buf := Interrupted :: !buf
          in lastPos := size code; clearBuf true end);
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
    case recv () of
      Request {method = "shutdown", id, ...} => (
        diag "received shutdown request";
        send (mkResponse id (Ok encNull));
        recvExit ();
        raise Shutdown)
    | Request {method = "textDocument/hover", id, params} =>
      spawnJob id params textDocumentPositionParams hover
    | Request {method = "textDocument/definition", id, params} =>
      spawnJob id params textDocumentPositionParams gotoDefinition
    | Request {method = "$/eval", id, params} =>
      spawnJob id params evalParams (eval id)
    | Request {method, id, ...} =>
      send (mkResponse id (mkErr InvalidRequest ("unknown method: " ^ method)))
    | Notification {method = "$/cancelRequest", params} => let
      val id = JSONDecode.decode cancelParams params
      in app (fn (j,th) => if j = id then Thread.interrupt th else ()) (jobs I) end
    | Response _ => diag "response to unknown request"
    | Notification {method, ...} => diag ("unknown method: " ^ method);
    main ())
  in
    main () handle
      Shutdown => ()
    | Disconnected => diag "early abort"
  end

end (* struct *)
