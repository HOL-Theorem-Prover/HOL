structure daisyLib :> daisyLib =
struct

open HolKernel Parse boolLib bossLib daisyTheory;

fun run_daisy path func = let
  val str = ``p_str "test" ^func``
    |> EVAL |> concl |> rand |> stringSyntax.fromHOLstring
  val output_filename = path ^ "/Program"
  val filename = output_filename ^ ".scala"
  val f = TextIO.openOut filename
  val _ = TextIO.output (f,str)
  val _ = TextIO.closeOut f
  val _ = OS.Process.system("cd "^path^" && ./daisy " ^ filename ^ " > /dev/null")
  val f = TextIO.openIn output_filename
  val str = (case TextIO.inputLine(f) of SOME str => str)
  val _ = TextIO.closeIn f
  val cs = explode " ,\n[]"
  val strs = String.tokens (fn c => mem c cs) str
  val err = el 3 strs |> stringSyntax.fromMLstring
  val lower = el 5 strs |> stringSyntax.fromMLstring
  val upper = el 6 strs |> stringSyntax.fromMLstring
  val tm = ``rosa_correctness fp64_conf ^func 0 [(^err,^lower,^upper)]``
  in mk_oracle_thm "Daisy" ([],tm) end

(*

EXAMPLE:

open daisyLib daisyTheory

val func = ``(Func ["x"] [Assert (Cons (LessEq (X (Const "-1")) (X (Var "x"))));
                   Assert (Cons (LessEq (X (Var "x")) (X (Const "1"))))]
                  (NonRec (Simple (Exp (X (Var "x"))))))``;
show_tags := true;
val path = "/Users/mom22/tools/daisy";

  run_daisy path func

*)

end
