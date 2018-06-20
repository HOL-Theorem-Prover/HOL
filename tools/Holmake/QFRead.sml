structure QFRead :> QFRead =
struct

fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)
fun exndie e = die ("Exception raised " ^ General.exnMessage e)

fun exhaust_lexer (read, close) =
  let
    fun recurse acc =
      case read () of
          "" => (close(); String.concat (List.rev acc))
        | s => recurse (s::acc)
  in
    recurse []
  end

fun file_to_lexer fname =
  let
    val instrm = TextIO.openIn fname handle e => exndie e
    val isscript = String.isSuffix "Script.sml" fname
    val qstate = QuoteFilter.UserDeclarations.newstate isscript
    val read = QuoteFilter.makeLexer (fn n => TextIO.input instrm) qstate
  in
    (read, (fn () => TextIO.closeIn instrm))
  end

fun string_to_lexer s =
  let
    val qstate = QuoteFilter.UserDeclarations.newstate false
    val sr = ref s
    fun str_read _ = (!sr before sr := "")
    val read = QuoteFilter.makeLexer str_read qstate
  in
    (read, (fn () => ()))
  end

fun stream_to_lexer isscriptp strm =
  let
    val qstate = QuoteFilter.UserDeclarations.newstate isscriptp
    val read = QuoteFilter.makeLexer (fn n => TextIO.input strm) qstate
  in
    (read, (fn () => ()))
  end


fun inputFile fname = exhaust_lexer (file_to_lexer fname)
fun fromString s = exhaust_lexer (string_to_lexer s)

fun mkReaderEOF (read, close) = let
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
  (doit, eof)
end

fun fileToReaderEOF fname = mkReaderEOF (file_to_lexer fname)
fun fileToReader fname = #1 (fileToReaderEOF fname)
fun stringToReader s = #1 (mkReaderEOF (string_to_lexer s))
fun streamToReader b strm = #1 (mkReaderEOF (stream_to_lexer b strm))

end
