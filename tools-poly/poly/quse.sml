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

fun prim_use cfg fname =
    use_reader fname (HolParser.fileToReader cfg fname)

val use = prim_use {quietOpen = false}


fun useScript fname =
    let
      val istream = TextIO.openIn fname
      val reader = HolParser.streamToReader {quietOpen = false} fname istream
      val _ = use_reader fname reader
              handle e => (TextIO.closeIn istream; PolyML.Exception.reraise e)
    in
      TextIO.closeIn istream
    end

end
