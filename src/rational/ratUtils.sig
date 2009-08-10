signature ratUtils =
sig
	type term = Term.term
	type thm = Thm.thm
	type goal = Abbrev.goal
	type conv = Abbrev.conv
	type tactic = Abbrev.tactic

	val dest_rat : term -> term * term list
	val extract_rat : term -> term list

	val extract_rat_vars : term -> term list
	val extract_rat_equations : term -> term list
	val extract_rat_minv : term -> term list

end;