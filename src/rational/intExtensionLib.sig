signature intExtensionLib =
sig
	type term = Term.term
	type thm = Thm.thm
	type goal = Abbrev.goal
	type conv = Abbrev.conv
	type tactic = Abbrev.tactic 
	type simpset = simpLib.simpset

	(* tactics *)
	val INT_SGN_CASES_TAC: term -> tactic
	val INT_CALCEQ_TAC: tactic
end;