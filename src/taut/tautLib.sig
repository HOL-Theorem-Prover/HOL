(* ===================================================================== *)
(* FILE          : tautLib.sig                                           *)
(* DESCRIPTION   : Signature for the tautology library.                  *)
(* ===================================================================== *)

signature tautLib =
sig
  include Abbrev

  val PTAUT_CONV   : conv
  val PTAUT_TAC    : tactic
  val PTAUT_PROVE  : term -> thm
  val TAUT_CONV    : conv
  val TAUT_TAC     : tactic
  val ASM_TAUT_TAC : tactic
  val TAUT_PROVE   : term -> thm
  val TAUT         : term quotation -> thm
end
