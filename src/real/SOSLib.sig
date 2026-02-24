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

  (* --- Full nonlinear prover (pure SOS + CSDP when available) --- *)

  (* SOS-based nonlinear real arithmetic prover.
     Handles universally quantified nonnegativity:
       &0 <= p, p >= &0, p >= q, p <= q, !x y. &0 <= f(x,y).
     Uses CSDP for the SDP when available, falls back to pure SOS.
     Does NOT yet handle hypotheses (future: GEN_REAL_ARITH integration). *)
  val REAL_SOS     : term -> thm
  val REAL_SOS_TAC : tactic

  (* Debugging *)
  val sos_debugging : bool ref

end
