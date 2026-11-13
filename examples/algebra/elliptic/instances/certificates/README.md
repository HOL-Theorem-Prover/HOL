# Elliptic scalar certificates

Instance-support libraries for checked `sw_group` scalar arithmetic over prime
and quadratic fields. Candidate coordinates are untrusted; HOL checks the proofs.
See the library signatures for APIs and tactic subgoal layouts.

## Libraries

* `ellipticCertificates`: inverse witnesses, binary scalar laws and order rules.
* `ellipticCertificateLib`: field-independent binary scalar checking and a
  prime-field specialization.
* `pairingCurveCertificateLib`: quadratic-field arithmetic and scalar checking
  for `PolyModRing (GF p) [1;0;1]`, not arbitrary extension towers.

Certificate tactics expose bounded milestone or operation goals, discharged
by matching step tactics. A residual goal remains when scalar replacement
does not close the original conclusion. Curve and membership hypotheses
are preserved.

## Dependencies and tests

Depends on generic elliptic theories and
[field certificates](../../../field_certificates/README.md), not on the
[concrete instances](../README.md).

Build and test here with `Holmake selftest.exe && ./selftest.exe`.
These small-field regressions also run at selftest level 1.
They cover prime-field scalar certificates and arithmetic over
`GF(7)[i]/(i^2+1)`: a non-real inverse, scalar multiplication, and field
powers. Scalar and power cases use exponent 65537 to cross the sixteen-bit
chunk boundary and check continuation, residual goals, exact conclusions,
and absence of unexpected hypotheses.
