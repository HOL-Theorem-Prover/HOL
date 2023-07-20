signature realLib =
sig

   type term = Term.term
   type thm = Thm.thm
   type conv = Abbrev.conv
   type tactic = Abbrev.tactic

  val PURE_REAL_ARITH_TAC : tactic
  val REAL_ARITH_TAC      : tactic
  val REAL_ARITH          : term -> thm
  val REAL_ASM_ARITH_TAC  : tactic

   val real_ss : simpLib.simpset
   (* Incorporates simpsets for bool, pair, and arithmetic *)

   (* syntax *)
   val prefer_real     : unit -> unit
   val deprecate_real  : unit -> unit

end
