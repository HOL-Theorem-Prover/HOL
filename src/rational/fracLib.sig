signature fracLib =
sig
	type term = Term.term
	type thm = Thm.thm
	type goal = Abbrev.goal
	type conv = Abbrev.conv
	type tactic = Abbrev.tactic
	type simpset = simpLib.simpset

	(* equivalence *)
	val FRAC_EQ_CONV : conv
	val FRAC_NOTEQ_CONV : conv
	val FRAC_EQ_TAC : tactic

	(* positive and non-zero *)
	val FRAC_POS_CONV : conv
	val FRAC_NOT0_CONV : conv
	val FRAC_POS_TAC : term -> tactic
	val FRAC_NOT0_TAC : term -> tactic

	(* numerator and denominator extraction *)
	val FRAC_NMR_CONV : conv
	val FRAC_DNM_CONV : conv
	val FRAC_NMRDNM_TAC : tactic

	(* calculation *)
	val FRAC_CALC_CONV : conv
	val FRAC_STRICT_CALC_TAC : tactic
	val FRAC_CALCTERM_TAC : term -> tactic
	val FRAC_CALC_TAC : tactic

	val FRAC_STRICT_CALCEQ_TAC : tactic
	val FRAC_CALCEQ_TAC : tactic

	val FRAC_SAVE_CONV : conv
	val FRAC_SAVE_TAC : tactic

end;
