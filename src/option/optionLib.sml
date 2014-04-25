structure optionLib :> optionLib =
struct

 open Parse optionTheory optionSyntax;

val option_rws = option_CLAUSES

(*
val OPTION_data = rewrites
  (map ((fn th => if (is_neg (concl th)) then EQF_INTRO th else th) o SPEC_ALL)
       (CONJUNCTS (theorem "option" "option_CLAUSES")));

in

  val OPTION_ss = mk_simpset [OPTION_data];
  val option_ss = hol_ss ++ OPTION_data;

end;
*)

val OPTION_rewrites =
  [ THE_DEF, IS_SOME_DEF, IS_NONE_DEF,
    SOME_11, NOT_NONE_SOME, NOT_SOME_NONE,
    option_case_compute, OPTION_MAP_DEF,
    OPTION_BIND_def, OPTION_GUARD_def,
    OPTION_IGNORE_BIND_def, OPTION_CHOICE_def ];

val OPTION_rws =
  computeLib.add_thms (List.map computeLib.lazyfy_thm OPTION_rewrites);

end;
