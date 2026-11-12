# Elliptic arithmetic and scalar certificates

These checkers prove arithmetic claims about the existing `sw_group` exponent;
they do not introduce a second scalar operation or trust candidate coordinates.

* `ellipticCertificates`: inverse-witness rules, binary scalar identities,
  exact prime generator-order criteria and a finite-field cube obstruction.
* `ellipticCertificateLib`: field-independent `BINARY_SCALAR_CONV` parameterized
  by a checked addition conversion; `SCALAR_CONV` for literal prime-field points.
  The certificate tactics expose bounded scalar milestones or operations whose
  proof obligations are discharged by matching step tactics.
* `pairingCurveCertificateLib`: checked field operations and scalar arithmetic
  for the numeric quadratic quotient `PolyModRing (GF p) [1;0;1]`; bounded field
  power and scalar-operation certificate tactics. This is not an evaluator for
  arbitrary extension towers.

The signatures specify input theorem order and tactic subgoal layouts.
Curve validity and point-membership hypotheses are preserved. Interfaces that
cache closed field contexts require closed prime/field proofs; a mismatched
field certificate is not interchangeable with the requested field.

Candidate Euclidean inverses, quotient/remainder computations and scalar
trajectories are untrusted data. Successful conversions return kernel
equalities; preparing a tactic's candidate goals alone does not discharge them.
The arithmetic support and polynomial checkers are supplied by the sibling
field/certificate package. Shared modular exponentiation comes from HOL's
`expMod`/`cv_std` implementation, not a private binary-power program.

Build with native Holmake from this directory. The concrete
[instance package](../instances/README.md) provides end-to-end clients and
full-cardinality certificates, including the computationally expensive cases.
