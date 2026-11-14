# Short-Weierstrass curves

Generic curves `y^2 = x^3 + a*x + b` over HOL's existing field/group records,
with characteristic other than 2 or 3 and nonzero discriminant.

## Theory map

* `shortWeierstrass`, `swAssocAlgebra`, `shortWeierstrassGroup`: points,
  curve membership and the Abelian group law.
* `ellipticTorsion`: scalar laws, rational torsion, point orders and cofactor
  clearing.
* `ellipticMorphisms`, `ellipticScaling`: field-induced maps and invertible
  coordinate changes.
* `shortWeierstrassProjective`: ordinary homogeneous coordinates and affine
  round trips, not Jacobian coordinates.
* `ellipticCardinality`: elementary cardinality bounds and exact-order
  certificates.
* `ellipticCMMap`, `ellipticCMCertificates`: cube-root automorphisms and
  finite-group independence arguments.
* `shortWeierstrassSmall`: worked examples over GF(5).

## Using the interface

Use `(sw_group r a b).exp` for scalars and the existing `order` operation.
Point constructors are total; group laws require curve and carrier hypotheses.
Torsion means rational points over the stated field, not an algebraic closure.
Cofactor clearing need not produce a nonzero point or land in a chosen
generator's subgroup. The scripts give the precise theorem statements.

## Build

Build here with `../../../bin/Holmake`; generic theories run at selftest
level 1. They are independent of the [cryptographic instances](instances/README.md)
and their certificate automation, and do not use the legacy `examples/elliptic`.
