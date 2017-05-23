(*---------------------------------------------------------------------------*
 * The "imperative" library. This provides a collection of proof tactics     *
 * that are called upon by imperativeTheory                                  *
 *                                                                           *
 *---------------------------------------------------------------------------*)

signature imperativeLib =
sig
	include Abbrev

	val APPLY_DEFINITIONS_TO_THEOREM : thm list -> thm -> thm

	val APPLY_DEFINITIONS_TAC : thm list -> tactic

	val REFINEMENT_RATOR : term

	val REFINEMENT_NOT_RATOR : term

	val REFINEMENT_RULE : thm -> thm

	val REFINEMENT_TAC : tactic

	val SWAPLR_RULE : thm -> thm

	val EXHAUSTIVELY : tactic -> tactic

	val REP_EVAL_TAC : tactic

	val USE_CONTEXT : term list -> thm -> thm

	val VSUB : term -> term -> thm -> thm

	val MAKE_IT_SO  : thm -> tactic 

	val MAKE_IT_NO  : thm -> tactic

	val EVAL_FOR_STATEVARS : term list -> tactic

	val DECL_STATEVARS : term -> term list -> term list
end;
