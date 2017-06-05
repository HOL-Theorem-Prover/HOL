structure QFRead :> QFRead =
struct

fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)
fun exndie e = die ("Exception raised " ^ General.exnMessage e)

fun mkBuffer () = let
  val buf = ref ([] : string list)
  fun push s = buf := s :: !buf
  fun read () = let
    val contents = String.concat (List.rev (!buf))
  in
    buf := [contents];
    contents
  end
  fun reset() = buf := []
in
  (push, read, reset)
end

fun inputFile fname =
  let
    val (QBpush, QBread, _) = mkBuffer()
    val instrm = TextIO.openIn fname handle e => exndie e
    val qstate = QuoteFilter.UserDeclarations.newstate(QBpush, fn () => ())
  in
    QuoteFilter.makeLexer (fn n => TextIO.input instrm) qstate ();
    TextIO.closeIn instrm;
    QBread()
  end

fun fromString s =
  let
    val (QBpush, QBread, _) = mkBuffer()
    val qstate = QuoteFilter.UserDeclarations.newstate(QBpush, fn () => ())
    val sr = ref s
    fun read _ = (!sr before sr := "")
  in
    QuoteFilter.makeLexer read qstate ();
    QBread()
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
