signature ratLib =
sig
	type term = Term.term
	type thm = Thm.thm
	type goal = Abbrev.goal
	type conv = Abbrev.conv
	type tactic = Abbrev.tactic
	type ssfrag = simpLib.ssfrag
	type simpset = simpLib.simpset

	(* conversions *)
	val RAT_EQ_CONV : conv
	val RAT_CALC_CONV : conv
	val RAT_ADDAC_CONV :conv
	val RAT_MULAC_CONV :conv

	(* tactics *)
	val RAT_EQ_TAC : tactic
	val RAT_ADDAC_TAC : term -> tactic
	val RAT_MULAC_TAC : term -> tactic
	val RAT_EQ_LMUL_TAC : term -> tactic
	val RAT_EQ_RMUL_TAC : term -> tactic
	val RAT_ADDSUB_TAC : term -> term -> tactic
	val RAT_CALCTERM_TAC : term -> tactic
	val RAT_STRICT_CALC_TAC : tactic
	val RAT_CALC_TAC : tactic
	val RAT_CALCEQ_TAC : tactic

	(* conversions *)
	val RAT_PRECALC_CONV : conv
	val RAT_POSTCALC_CONV : conv
	val RAT_BASIC_ARITH_CONV : conv
	val RAT_ELIMINATE_MINV_EQ_CONV : conv
	val RAT_ELIMINATE_MINV_CONV : conv

	(* tactics *)
	val RAT_SAVE_TAC : term -> tactic
	val RAT_SAVE_ALLVARS_TAC : tactic
	val RAT_BASIC_ARITH_TAC : tactic
	val RAT_ELIMINATE_MINV_TAC : tactic

	val int_rewrites : thm list;
	val rat_basic_rewrites : thm list;
	val rat_rewrites : thm list;
	val rat_num_rewrites : thm list;

end;
