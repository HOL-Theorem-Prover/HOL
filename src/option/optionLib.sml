structure optionLib :> optionLib = 
struct

  open Parse optionTheory;

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

  val OPTION_rws = computeLib.add_thms
      (false,[ THE_DEF, IS_SOME_DEF, IS_NONE_DEF,
	       SOME_11, NOT_NONE_SOME, NOT_SOME_NONE,
	       Drule.EQT_INTRO (Thm.REFL(--`NONE : 'a option`--)),
	       option_case_compute, option_APPLY_DEF ]);

end;
