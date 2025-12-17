structure HolParser :> HolParser =
struct

fun K a _ = a
fun I a = a

type fileline = {file: string, line: int, col: int}

structure ToSML = struct

  type args = {
    read: int -> string,
    filename: string,
    parseError: int * int -> string -> unit,
    quietOpen: bool
  }
  type printer = {str: string -> unit, startSpan: int * int -> unit, stopSpan: unit -> unit}

  fun mkPushTranslator ({read, filename, parseError, quietOpen}:args) pr = let
    val {parseDec, body, events, ...} =
      HOLParser.parseSML filename read parseError HOLParser.initialScope
    val fileline = HOLAst.mkFileline body events
    val expandDec = HOLToSML.expandDec
      {parseError = parseError, quietOpen = quietOpen, fileline = fileline}
    val pr' = HOLPrinter.mkPrinter pr
    fun push () =
      case parseDec () of
        NONE => true
      | SOME dec => case expandDec dec of
          HOLAst.DecExpansion {result = [], ...} => false
        | dec => (
          HOLPrinter.printDecs parseError (rev (HOLToSML.mkSemi [dec])) pr';
          #str pr "\n"; false)
    in {fileline = fileline, push = push} end

  fun mkPullTranslator args = let
    val queue = ref []
    val atEnd = ref false
    val spans = ref []
    val {fileline, push} = mkPushTranslator args {
      str = fn s => queue := s :: !queue,
      startSpan = fn s => spans := s :: !spans,
      stopSpan = fn () => spans := tl (!spans) }
    fun topspan () = case !spans of [] => 0 | (s, _) :: _ => s
    fun loop () =
      case !queue of
        s :: rest => (queue := rest; s)
      | [] => if !atEnd then "" else (
        atEnd := push ();
        queue := rev (!queue);
        loop ())
    in {fileline = fileline o topspan, read = loop} end

end

open HOLFileSys
type reader = {read: unit -> char option, fileline: unit -> fileline, eof: unit -> bool}

fun exhaust_parser {read, close, ...} =
  let
    fun recurse acc =
      case read () of
          "" => (close(); String.concat (List.rev acc))
        | s => recurse (s::acc)
  in
    recurse []
  end

type args = {quietOpen: bool}

fun file_to_parser ({quietOpen}:args) fname = let
  val instrm = openIn fname
  (* val isscript = String.isSuffix "Script.sml" fname *)
  val {fileline, read} = ToSML.mkPullTranslator
    {read = fn _ => input instrm, filename = fname, parseError = K (K ()), quietOpen = quietOpen}
  in {read = read, fileline = fileline, close = fn () => closeIn instrm} end

fun string_to_parser ({quietOpen}:args) s = let
  val sr = ref s
  fun str_read _ = (!sr before sr := "")
  val {fileline, read} = ToSML.mkPullTranslator
    {read = str_read, filename = "", parseError = K (K ()), quietOpen = quietOpen}
  in {read = read, fileline = fileline, close = I} end

fun input_to_parser ({quietOpen}:args) fname inp = let
  val {fileline, read} = ToSML.mkPullTranslator
    {read = inp, filename = fname, parseError = K (K ()), quietOpen = quietOpen}
  in {read = read, fileline = fileline, close = I} end

fun stream_to_parser args fname strm =
  input_to_parser args fname (fn _ => input strm)

fun inputFile args fname = exhaust_parser (file_to_parser args fname)
fun fromString args s = exhaust_parser (string_to_parser args s)

fun mkReaderEOF {read, fileline, close} = let
  val i = ref 0
  val s = ref ""
  val eofp = ref false
  fun pull () = (s := read(); i := 0;
                 if !s = "" then (eofp := true; close()) else ())
  fun doit () =
    if !eofp then NONE
    else if !i < size (!s) then SOME (String.sub(!s,!i)) before i := !i + 1
    else (pull(); doit())
  fun eof () = !eofp
  in {read = doit, fileline = fileline, eof = eof} end

fun fileToReader args fname = mkReaderEOF (file_to_parser args fname)
fun stringToReader args s = mkReaderEOF (string_to_parser args s)
fun inputToReader args fnm inp = mkReaderEOF (input_to_parser args fnm inp)
fun streamToReader args fnm strm = mkReaderEOF (stream_to_parser args fnm strm)

end
