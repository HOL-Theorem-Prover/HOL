structure etqLib :> etqLib =
struct

open HolKernel Abbrev

val ERR = mk_HOL_ERR "etqLib"

fun print_goal g =
  HOLPP.prettyPrint(print, !Globals.linewidth) (goalStack.pp_goal g)

fun print_goals [] = print "Goal proved.\n"
  | print_goals [g] = print_goal g
  | print_goals gs =
      (print (Int.toString (length gs) ^ " subgoals:\n\n");
       List.app (fn g => (print_goal g; print "\n")) (List.rev gs))

fun etq_tmo timeout s =
  let
    val pf = proofManagerLib.et (s, smlExecute.tactic_of_sml timeout s)
    val goals = proofManagerLib.top_goals ()
  in
    print_goals goals;
    pf
  end
  handle HOL_ERR _ => raise ERR "etq" ("Cannot compile tactic: " ^ s)

val etq = etq_tmo 30.0

end
