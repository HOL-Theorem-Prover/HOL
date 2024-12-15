structure holdeptool =
struct

fun die () = OS.Process.exit OS.Process.failure
fun ok () = OS.Process.exit OS.Process.success
fun warn s = TextIO.output(TextIO.stdErr, s ^ "\n")
fun usage k =
    (warn ("Usage:\n  " ^ CommandLine.name() ^ " [-h | [file]]");
     k())
fun diewith s = (warn s; die())

fun main() = let
  open Holdep_tokens
  val stdin = (TextIO.stdIn, "<stdin>", (fn () => ()))
  fun file f = let
    val strm = TextIO.openIn f
  in
    (strm, f, (fn () => TextIO.closeIn strm))
  end
  val results =
      case CommandLine.arguments() of
          [] => (stream_deps ("<stdin>", TextIO.stdIn)
                 handle LEX_ERROR s => diewith("Lexical error: " ^ s)
                      | e => diewith ("Exception: "^General.exnMessage e))
        | ["-h"] => usage ok
        | [fname] => (reader_deps (fname, #read (HolParser.fileToReader fname))
                      handle LEX_ERROR s => diewith("Lexical error: " ^ s)
                           | e => diewith ("Exception: "^General.exnMessage e))
        | _ => usage die

in
  Binarymap.app (fn (s,_) => print (s ^ "\n")) results
end

end (* struct *)
