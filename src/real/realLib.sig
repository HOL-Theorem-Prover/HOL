signature realLib =
sig

   type term = Term.term
   type thm = Thm.thm
   type conv = Abbrev.conv
   type tactic = Abbrev.tactic

  val PURE_REAL_ARITH_TAC : tactic
  val REAL_ARITH_TAC      : tactic
  val REAL_ARITH          : term -> thm

   val real_ss : simpLib.simpset 
   (* Incorporates simpsets for bool, pair, and arithmetic *)

   (* Differentiation *)
   val basic_diffs :thm list ref
   val DIFF_CONV : conv

end
