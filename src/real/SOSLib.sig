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

  (* --- Knobs --- *)
  val sos_debugging  : bool ref
  val max_sos_degree : int ref    (* default 20 *)

end
