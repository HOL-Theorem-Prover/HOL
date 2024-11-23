structure QUse :> QUse =
struct

fun use_reader fname (reader as {read = infn0, eof}) =
  let
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

fun use fname = use_reader fname (HolParser.fileToReader fname)

fun useScript fname =
    let
      val istream = TextIO.openIn fname
      val reader = HolParser.streamToReader true fname istream
      val _ = use_reader fname reader
              handle e => (TextIO.closeIn istream; raise e)
    in
      TextIO.closeIn istream
    end

end
