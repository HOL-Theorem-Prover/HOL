structure QFRead :> QFRead =
struct

type reader =
     {read : unit -> char option, reset : unit -> unit, eof : unit -> bool}
fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)
fun exndie e = die ("Exception raised " ^ General.exnMessage e)

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

fun mkstate b = {inscriptp = b, quotefixp = false}

fun file_to_lexer fname =
  let

    val instrm = TextIO.openIn fname handle e => exndie e
    val isscript = String.isSuffix "Script.sml" fname
    val qstate = QuoteFilter.UserDeclarations.newstate (mkstate isscript)
    val read = QuoteFilter.makeLexer (fn n => TextIO.input instrm) qstate
  in
    (#2 o read, (fn () => TextIO.closeIn instrm), reset qstate)
  end

fun string_to_lexer isscriptp s =
  let
    val qstate = QuoteFilter.UserDeclarations.newstate (mkstate isscriptp)
    val sr = ref s
    fun str_read _ = (!sr before sr := "")
    val read = QuoteFilter.makeLexer str_read qstate
  in
    (#2 o read, (fn () => ()), reset qstate)
  end

fun stream_to_lexer isscriptp strm =
  let
    val qstate = QuoteFilter.UserDeclarations.newstate (mkstate isscriptp)
    val read = QuoteFilter.makeLexer (fn n => TextIO.input strm) qstate
  in
    (#2 o read, (fn () => ()), reset qstate)
  end

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
fun streamToReader b strm = mkReaderEOF (stream_to_lexer b strm)

end
