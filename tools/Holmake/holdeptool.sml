structure holdeptool =
struct

fun die () = OS.Process.exit OS.Process.failure
fun ok () = OS.Process.exit OS.Process.success
fun usage k =
    (TextIO.output(TextIO.stdErr,
                   "Usage:\n  " ^ CommandLine.name() ^ " [-h | -n [file]]");
     k())
fun diewith s = (TextIO.output(TextIO.stdErr, s ^ "\n"); die())

fun main() = let
  open Holdep_tokens
  val stdin = (TextIO.stdIn, "<stdin>", (fn () => ()))
  fun file f = let
    val strm = TextIO.openIn f
  in
    (strm, f, (fn () => TextIO.closeIn strm))
  end
  val unsorted = ref false
  val (strm, fname, closer) =
      case CommandLine.arguments() of
          [] => stdin
        | ["-n"] => (unsorted := true; stdin)
        | ["-h"] => usage ok
        | [fname] => file fname
        | ["-n", fname] => (unsorted := true; file fname)
        | _ => usage die
  val arg = UserDeclarations.new_state fname
  val lexer = makeLexer (fn n => TextIO.inputN(strm, n)) arg
  fun safelex () =
      lexer() handle UserDeclarations.LEX_ERROR s => diewith ("Lexical error: "^ s)
  fun unsortedf () =
      case safelex() of
          NONE => closer()
        | SOME s => (TextIO.print (s ^ "\n"); unsortedf())
  fun sorted acc =
      case safelex() of
          NONE => (closer();
                   Binaryset.app (fn s => print (s ^ "\n")) acc)
        | SOME s => sorted (Binaryset.add(acc, s))
in
  if !unsorted then unsortedf() else sorted (Binaryset.empty String.compare)
end

end (* struct *)
