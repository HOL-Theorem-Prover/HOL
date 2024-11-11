structure QFRead :> QFRead =
struct

open HOLFileSys
type reader =
     {read : unit -> char option, reset : unit -> unit, eof : unit -> bool}

fun exhaust_lexer (read, close, _) =
  let
    fun recurse acc =
      case read () of
          "" => (close(); String.concat (List.rev acc))
        | s => recurse (s::acc)
  in
    recurse []
  end

fun reset st = fn () => QuoteFilter.UserDeclarations.resetstate st

fun mkstate b fname =
    {inscriptp = b, quotefixp = false, scriptfilename = fname}

fun file_to_lexer fname =
  let

    val instrm = openIn fname
    val isscript = String.isSuffix "Script.sml" fname
    val qstate = QuoteFilter.UserDeclarations.newstate (mkstate isscript fname)
    val read = QuoteFilter.makeLexer (fn n => input instrm) qstate
  in
    (#2 o read, (fn () => closeIn instrm), reset qstate)
  end

fun string_to_lexer isscriptp s =
  let
    val qstate = QuoteFilter.UserDeclarations.newstate (mkstate isscriptp "")
    val sr = ref s
    fun str_read _ = (!sr before sr := "")
    val read = QuoteFilter.makeLexer str_read qstate
  in
    (#2 o read, (fn () => ()), reset qstate)
  end

fun input_to_lexer isscriptp fname inp =
  let
    val qstate = QuoteFilter.UserDeclarations.newstate (mkstate isscriptp fname)
    val read = QuoteFilter.makeLexer inp qstate
  in
    (#2 o read, (fn () => ()), reset qstate)
  end

fun stream_to_lexer isscriptp fname strm =
  input_to_lexer isscriptp fname (fn n => input strm)

fun inputFile fname = exhaust_lexer (file_to_lexer fname)
fun fromString b s = exhaust_lexer (string_to_lexer b s)

fun mkReaderEOF (read, close, reset) = let
  val i = ref 0
  val s = ref ""
  val sz = ref 0
  val eofp = ref false
  fun pull () = (s := read(); sz := size (!s); i := 0;
                 if !sz = 0 then (eofp := true; close()) else ())
  fun doit () =
    if !eofp then NONE
    else if !i < !sz then SOME (String.sub(!s,!i)) before i := !i + 1
    else (pull(); doit())
  fun eof () = !eofp
in
  {read = doit, eof = eof, reset = reset}
end

fun fileToReader fname = mkReaderEOF (file_to_lexer fname)
fun stringToReader b s = mkReaderEOF (string_to_lexer b s)
fun inputToReader b fnm inp = mkReaderEOF (input_to_lexer b fnm inp)
fun streamToReader b fnm strm = mkReaderEOF (stream_to_lexer b fnm strm)

end
