signature pairingCurveCertificateLib =
sig
  include Abbrev
  (* Numeric PolyModRing (GF p) [1;0;1] only; ascending coefficients, [] zero.
     Both input proofs must be closed kernel theorems. Reuses the last field's
     checked setup; arithmetic witnesses remain local to each conversion. *)
  val FIELD_CONV : thm -> thm -> conv
  val SCALAR_CONV : thm -> thm -> thm -> thm -> conv
  (* Prepare at most sixteen binary bits of literal scalar operations per
     invocation, with separate doubling/addition proof branches. A nonfinal
     chunk ends in the original goal under its last scalar equality; nest
     SCALAR_CERTIFICATE_TAC there to prepare the next chunk. Only the first
     chunk includes the zero-prefix milestone, and only the final chunk may
     have a residual goal. Use explicit source >| branches with SCALAR_STEP_TAC
     so preparation and each kernel-checked operation stay separately bounded. *)
  val SCALAR_CERTIFICATE_TAC :
    thm -> thm -> thm -> thm -> tactic
  val SCALAR_STEP_TAC : thm -> thm -> thm -> thm -> tactic
  (* Literal quadratic field powers, with at most sixteen binary bits prepared
     per call. Each bit emits a doubling and, if odd, a multiplication by the
     base. The initial zero-prefix doubling is included, without a separate
     zero milestone. Nonfinal chunks continue the original goal under their
     final prefix equality; final residuals are left to FIELD_CONV. Candidate
     arithmetic is untrusted; POWER_STEP_TAC checks one operation using only
     the supplied preceding equality, never a recursive power computation. *)
  val POWER_CERTIFICATE_TAC : thm -> thm -> tactic
  val POWER_STEP_TAC : thm -> thm -> tactic
end
