structure QUse :> QUse =
struct

val {print = emit, hadError} = HOLSourceParser.trackingPrint print
val failOnError = ref false

fun use_reader fname {read = infn, fileline, eof} =
  let
    open PolyML
    fun line () = #line (fileline ()) + 1
  in
    while not (eof()) do (
      compiler (infn, [Compiler.CPFileName fname, Compiler.CPLineNo line]) ();
      if !failOnError andalso hadError () then
        OS.Process.exit OS.Process.failure
      else ()
    )
  end

fun prim_use {quietOpen} fname =
    use_reader fname (HOLSource.fileToReader {quietOpen = quietOpen, print = emit} fname)

val use = prim_use {quietOpen = false}


fun useScript fname =
    let
      val istream = TextIO.openIn fname
      val reader =
        HOLSource.streamToReader {quietOpen = false, print = emit} fname istream
      val _ = use_reader fname reader
              handle e => (TextIO.closeIn istream; PolyML.Exception.reraise e)
    in
      TextIO.closeIn istream
    end

end
