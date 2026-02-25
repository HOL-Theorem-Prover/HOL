(* ========================================================================= *)
(* Sum-of-squares (SOS) decomposition and nonlinear real arithmetic.         *)
(*                                                                           *)
(* Ported from HOL-Light's Examples/sos.ml (BSD-2-Clause).                   *)
(*   Original author: John Harrison                                          *)
(*   Port to HOL4: Charles Cooper and Claude Opus 4.6, 2026                  *)
(* ========================================================================= *)

signature SOSLib =
sig
  include Abbrev

  (* --- Pure SOS: decompose p into k*(c1*q1^2 + ... + cn*qn^2) --- *)

  (* Given a term representing a real polynomial p, prove
       |- p = k * (q1^2 + ... + qn^2)
     by exact rational Cholesky decomposition (no external tools).
     Raises HOL_ERR if no decomposition found. *)
  val SOS_CONV    : conv

  (* Prove |- &0 <= p by SOS decomposition *)
  val PURE_SOS_TAC : tactic
  val PURE_SOS     : term -> thm

  (* --- Full nonlinear prover (Positivstellensatz + CSDP) --- *)

  (* SOS-based nonlinear real arithmetic prover.
     Uses GEN_REAL_ARITH to handle hypotheses via Positivstellensatz
     certificate search. Tries linear prover first, then CSDP.
     Handles universally quantified goals with implications. *)
  val REAL_SOS         : term -> thm
  val REAL_SOS_TAC     : tactic
  val REAL_SOS_ASM_TAC : tactic

  (* --- REAL_SOSFIELD: handles division and inv in real goals --- *)

  (* Like REAL_SOS but also handles real_div and inv.
     Adds t * inv(t) = 1 hypotheses, replaces inv(t) with fresh
     variables, tries REAL_ARITH → REAL_RING → REAL_SOS chain. *)
  val REAL_SOSFIELD         : term -> thm
  val REAL_SOSFIELD_TAC     : tactic
  val REAL_SOSFIELD_ASM_TAC : tactic

  (* --- INT_SOS: integer SOS prover --- *)

  (* SOS prover for integer goals. Normalizes negated comparisons
     using discreteness (x < y ⟺ x + 1 ≤ y), converts integer
     operations to reals via real_of_int, then calls REAL_SOS. *)
  val INT_SOS         : term -> thm
  val INT_SOS_TAC     : tactic
  val INT_SOS_ASM_TAC : tactic

  (* --- SOS_RULE: natural number SOS prover --- *)

  (* SOS prover for natural number goals. Converts num operations
     to int via int_of_num, then calls INT_SOS. Handles polynomial
     goals with +, *, EXP, <=, <, >=, >, =. *)
  val SOS_RULE         : term -> thm
  val SOS_RULE_TAC     : tactic
  val SOS_RULE_ASM_TAC : tactic

  (* --- Knobs --- *)
  val sos_debugging  : bool ref
  val max_sos_degree : int ref    (* default 20 *)

end
