structure QUse :> QUse =
struct

fun use_reader fname {read = infn, fileline, eof} =
  let
    open PolyML
  in
    while not (eof()) do
      compiler (infn, [Compiler.CPFileName fname, Compiler.CPLineNo (#line o fileline)]) ()
  end

fun prim_use {quietOpen} fname =
    use_reader fname (HOLSource.fileToReader {quietOpen = quietOpen, print = print} fname)

val use = prim_use {quietOpen = false}


fun useScript fname =
    let
      val istream = TextIO.openIn fname
      val reader =
        HOLSource.streamToReader {quietOpen = false, print = print} fname istream
      val _ = use_reader fname reader
              handle e => (TextIO.closeIn istream; PolyML.Exception.reraise e)
    in
      TextIO.closeIn istream
    end

end
