structure optionLib :> optionLib = 
struct

val option_rws = optionTheory.option_CLAUSES

(*
val OPTION_data = rewrites
  (map ((fn th => if (is_neg (concl th)) then EQF_INTRO th else th) o SPEC_ALL)
       (CONJUNCTS (theorem "option" "option_CLAUSES")));

in

  val OPTION_ss = mk_simpset [OPTION_data];
  val option_ss = hol_ss ++ OPTION_data;

end;
*)

end;
