signature ellipticCertificateLib =
sig
  include Abbrev

  (* Representation-independent binary proof using a kernel addition
     conversion and the matching curve/membership certificates.
     Each constructed converter retains its successful kernel equalities. *)
  val BINARY_SCALAR_CONV : conv -> thm -> thm -> conv

  (* Decompose a scalar occurrence into separate width-bit milestone goals:
     the first equation, then implications from each preceding milestone.
     candidate computes literal sw_add results but is untrusted: every
     milestone must be proved by BINARY_SCALAR_STEP_TAC. Validation chains
     the supplied theorems to recover the original scalar equality.
     A residual goal follows if replacing the scalar does not close the
     original conclusion. Expose each window with an explicit branch:
       certificate >| [step, ..., step, residual_tactic]
     Omit residual_tactic when there is no residual goal. *)
  val BINARY_SCALAR_CERTIFICATE_TAC :
    int -> (term -> term) -> thm -> thm -> tactic

  (* Operation-level alternative, bounded by maxbits complete binary bits
     per invocation (maxbits must be positive). Each bit exposes its
     scalar(2*k) doubling equality, followed for an odd bit by scalar(2*k+1).
     Resume from the largest assumed scalar prefix for the same group and
     base point, using its right-hand side as the candidate starting point.
     Each chunk has bits + popcount(bits) operation goals; the first chunk
     includes scalar zero as its first doubling, not as an extra goal.
     With a seed, the first operation goal is an implication from that
     seed; subsequent goals are implications from their preceding milestone.
     If bits remain, the last subgoal is the original conclusion under the
     final milestone assumption, to be passed recursively to this tactic.
     Validation chains the operation proofs and discharges that assumption.
     Only the final chunk rewrites the conclusion and exposes an optional
     residual goal as above. Zero has no operation goals.
     Each BINARY_SCALAR_STEP_TAC branch checks at most one point addition;
     candidate remains entirely untrusted. *)
  val BINARY_SCALAR_OPERATION_CERTIFICATE_TAC :
    int -> (term -> term) -> thm -> thm -> tactic
  val BINARY_SCALAR_STEP_TAC : conv -> thm -> thm -> tactic

  (* Prime-field specializations, with the same certificates as SCALAR_CONV.
     The candidate pass performs no theorem computation. Each checked step
     verifies modular inverses and every point addition in its window. *)
  val SCALAR_CERTIFICATE_TAC : int -> thm -> thm -> thm -> tactic
  val SCALAR_STEP_TAC : thm -> thm -> thm -> tactic

  (* SCALAR_CONV prime curve member evaluates (sw_group (GF p) a b).exp P n
     for literal p,a,b,n and a literal affine point or ECInfinity. The inputs
     prove prime p, ShortWeierstrassCurve (GF p) a b, and P IN sw_points
     (GF p) a b. Binary group laws and checked modular-inverse witnesses
     produce a kernel theorem; input hypotheses are retained. Successful
     equalities are cached per constructed converter; failures are not. *)
  val SCALAR_CONV : thm -> thm -> thm -> conv
end
