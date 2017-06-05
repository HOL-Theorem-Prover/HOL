structure QFRead :> QFRead =
struct

open HM_SimpleBuffer
fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)
fun exndie e = die ("Exception raised " ^ General.exnMessage e)

fun inputFile fname =
  let
    val {push, read, ...} = mkBuffer()
    val instrm = TextIO.openIn fname handle e => exndie e
    val qstate = QuoteFilter.UserDeclarations.newstate(push, fn () => ())
  in
    QuoteFilter.makeLexer (fn n => TextIO.input instrm) qstate ();
    TextIO.closeIn instrm;
    read()
  end

fun fromString s =
  let
    val {push, read, ...} = mkBuffer()
    val qstate = QuoteFilter.UserDeclarations.newstate(push, fn () => ())
    val sr = ref s
    fun str_read _ = (!sr before sr := "")
  in
    QuoteFilter.makeLexer str_read qstate ();
    read()
  end

fun mkReaderEOF s = let
  val i = ref 0
  val sz = size s
  fun doit () =
    if !i < sz then SOME (String.sub(s,!i)) before i := !i + 1
    else NONE
  fun eof () = !i = sz
in
  (doit, eof)
end

fun fileToReaderEOF fname = mkReaderEOF (inputFile fname)
fun fileToReader fname = #1 (fileToReaderEOF fname)
fun stringToReader s = #1 (mkReaderEOF (fromString s))

end
