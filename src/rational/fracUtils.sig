signature fracUtils =
sig
	type term = Term.term
	type thm = Thm.thm
	type goal = Abbrev.goal
	type conv = Abbrev.conv
	type tactic = Abbrev.tactic

	val dest_frac : term -> term * term list
	val extract_frac : term -> term list
	val extract_abs_frac : term -> term list
	val extract_frac_fun : term list -> term -> (term * term * term) list

	val INT_GT0_CONV : term -> thm
end;
