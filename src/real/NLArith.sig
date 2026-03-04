signature NLArith =
sig
  include Abbrev

  (* Drop-in replacement for REAL_LINEAR_PROVER with NLA heuristics.
     Enriches hypotheses with square-nonneg and hypothesis-product
     theorems before retrying the linear prover. *)
  val NLA_PROVER :
    (thm list * thm list * thm list ->
     RealArith.positivstellensatz -> 'a) ->
    thm list * thm list * thm list -> 'a

  (* Prove real-valued goals involving nonlinear arithmetic.
     Handles squares, products of bounded terms, AM-GM style goals.
     Falls back to REAL_LINEAR_PROVER for linear goals. *)
  val REAL_NLA     : conv   (* term -> thm *)
  val NLA_TAC      : tactic
  val NLA_ASM_TAC  : tactic
end
