structure QUse :> QUse =
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

val (QBpush, QBread, QBreset) = mkBuffer()

fun quoteFile fname =
  let
    val instrm = TextIO.openIn fname handle e => exndie e
    val qstate = filter.UserDeclarations.newstate(QBpush, fn () => ())
  in
    QBreset() ;
    filter.makeLexer (fn n => TextIO.input instrm) qstate ();
    TextIO.closeIn instrm;
    QBread()
  end

fun mkLex s = let
  val i = ref 0
  val sz = size s
  fun doit () =
    if !i < sz then SOME (String.sub(s,!i)) before i := !i + 1
    else NONE
  fun eof () = !i = sz
in
  (doit, eof)
end

fun use fname =
  let
    val (infn0, eof) = mkLex (quoteFile fname)
    val lineNo = ref 1
    fun infn () =
      case infn0 () of
          NONE => NONE
        | SOME (c as #"\n") => (lineNo := !lineNo + 1;
                                SOME c)
        | SOME c => SOME c
    open PolyML
  in
    while not (eof()) do
          compiler (infn, [Compiler.CPFileName fname,
                           Compiler.CPLineNo (fn () => !lineNo)]) ()
  end

end
