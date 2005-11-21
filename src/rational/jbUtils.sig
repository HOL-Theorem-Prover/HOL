signature jbUtils =
sig
	type term = Term.term
	type thm = Thm.thm
	type goal = Abbrev.goal
	type conv = Abbrev.conv
	type tactic = Abbrev.tactic
	type hol_type = Abbrev.hol_type

	val AND_IMP_RULE: thm -> thm
	val IMP_AND_RULE: thm -> thm

	val REWRITE1_TAC: thm -> tactic
	val ONCE_REWRITE1_TAC: thm -> tactic
	val PROVE1_TAC: thm -> tactic
	val ASSUME_X_TAC: thm -> tactic
	val DISJ_LIST_CASES_TAC: thm -> tactic
	val NESTED_ASM_CASES_TAC: term list -> tactic

	val REMAINS_TO_PROVE: term -> tactic
	val NEW_GOAL_TAC: term -> tactic

	val extract_terms_of_type : hol_type -> term -> term list
	val store_thm_verbose : string * term * tactic -> thm
	val in_list : ''a list -> ''a -> bool
	val list_merge : ''a list -> ''a list -> ''a list
	val list_xmerge : ''a list list -> ''a list
	val dest_binop_triple : term -> term * term * term
end;
