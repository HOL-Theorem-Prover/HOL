structure QUse :> QUse =
struct

fun use fname =
  let
    open QFRead
    val (infn0, eof) = fileToReaderEOF fname
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
