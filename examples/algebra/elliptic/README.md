# Short-Weierstrass curves

This package develops the affine equation `y^2 = x^3 + a*x + b`, together
with a point at infinity, over arbitrary fields in the existing algebra
hierarchy. It does not introduce a new field or group hierarchy.

## Theory map

* `shortWeierstrass`: the datatype `'a sw_point`, constructors
  `ECInfinity` and `ECAffine x y`, curve equation, discriminant,
  `ShortWeierstrassCurve`, `sw_on_curve` and `sw_points`.
* `swAssocAlgebra`: ring-based polynomial identities for secant and tangent
  equations and the associativity calculation, proved using `ringLib`.
* `shortWeierstrassGroup`: `sw_neg`, `sw_add`, the record `sw_group`, closure,
  inverses, commutativity and associativity. The main results are
  `short_weierstrass_group`, `short_weierstrass_abelian_group` and
  `short_weierstrass_finite_group`.
* `ellipticTorsion`: scalar laws, rational n-torsion as a kernel subgroup,
  generated groups, point orders and cofactor clearing.
* `ellipticMorphisms`: coordinatewise maps induced by field homomorphisms
  and isomorphisms, preserving group operations, scalars and torsion.
* `ellipticScaling`: invertible coordinate scaling between curves, with
  group, scalar, point-order and torsion transport.
* `shortWeierstrassProjective`: ordinary homogeneous triples, nonzero
  scaling equivalence, curve representatives, chart equations and
  round trips to affine points and infinity.
* `ellipticCardinality`: the elementary bound of two points per
  x-coordinate, odd-cardinality criteria, cardinality identification
  from a sufficiently large odd divisor, and exact-order certificates.
* `ellipticCMMap`: the cube-root coordinate automorphism on curves with
  `a = 0`, preserving addition and scalar multiplication.
* `ellipticCMCertificates`: companion finite-group facts about
  order-three endomorphisms, cubic eigenvalues and independent
  generators; the resulting product cardinality gives an ambient
  group-cardinality lower bound.
* `shortWeierstrassSmall`: the example `y^2 = x^3 + 1` over `GF 5`.
  Its carrier has cardinality six and `ECAffine 2 2` has order six.
  The examples identify its rational 3-torsion and generated six-point
  group, transport points to an option field, and scale by `u = 2` to
  `y^2 = x^3 + 4`, preserving generator order six. Homogeneous examples
  identify scaled affine and infinity representatives and reject invalid
  triples. They use existing primality facts, not new primality APIs.

## API semantics

`ShortWeierstrassCurve r a b` requires `Field r`, coefficients in
`r.carrier`, `char r <> 2`, `char r <> 3`, and nonzero discriminant
`-16 * (4*a^3 + 27*b^2)`. The generic results do not require a finite field;
`FiniteField r` is an additional premise of the finite-group theorem.

The point datatype is total: `ECAffine x y` can be constructed even when
coordinates are outside the field carrier or do not satisfy the equation.
`sw_on_curve` checks both coordinate membership and the equation;
`sw_points` is the resulting carrier and always contains `ECInfinity`.
Addition and negation are total HOL functions too. Their curve/group laws
require the stated curve and point-membership hypotheses, not merely
values of the point datatype.

Infinity is the identity. Negation sends `(x,y)` to `(x,-y)`. Adding affine
points with the same x-coordinate and opposite y-coordinates yields
infinity, including doubling a point with y-coordinate zero. Otherwise,
equal x-coordinates use the tangent slope `(3*x^2+a)/(2*y)` and distinct
x-coordinates use the secant slope `(y2-y1)/(x2-x1)`. These cases, including
infinity and inverse cases, are covered by the group and associativity
results; the formulas alone are not unconditional group laws off-carrier.

`sw_group r a b` is an existing `'a sw_point group` record with carrier
`sw_points r a b`, identity `ECInfinity` and operation `sw_add r a b`.
Use its existing `.exp` operation for natural-number scalar multiplication
and `order (sw_group r a b) P` for point order. `sw_group_inv` identifies
the existing derived group inverse with `sw_neg r P` on the carrier.
There is no separate scalar-multiplication or point-order API.

`sw_torsion_group r a b n` is the kernel of the nth-power endomorphism:
its carrier consists of points in `sw_points r a b` killed by `n`.
These are rational points over the given field, not all torsion points
over an algebraic closure. For `n = 0` it is the whole curve group; for
`n = 1` its carrier is just infinity. This is distinct from
`Generated (sw_group r a b) P`, the existing group API's named generated
group. Its subgroup and cyclicity results here assume a finite field;
its cardinality equals the order of `P` when that order is positive.
For a finite field, if the curve cardinality is `h * n`, cofactor clearing
by `h` lands in rational n-torsion. It need not give a nonidentity point
or a point in a chosen generator's subgroup. The stronger exact-order
result requires the input point itself to have order `h * n`, with
`h` and `n` positive.

`sw_map_point f` fixes infinity and maps `(x,y)` to `(f x,f y)`.
Given a source curve, a target field and `FieldHomo f r s`, it induces
an injective group homomorphism to coefficients `(f a,f b)`, preserving
scalar multiplication and sending rational n-torsion to rational n-torsion.
It need not cover all points over a larger target field. `FieldIso`
supports group isomorphism, point-order preservation and isomorphism of
the corresponding rational torsion groups.

`sw_scale_point r u` fixes infinity and sends `(x,y)` to
`(u^2*x,u^3*y)`. For `u IN r.carrier` and `u <> 0`, it gives a group
isomorphism from coefficients `(a,b)` to `(u^4*a,u^6*b)`, with inverse
scaling by `u^-1`, preserving scalar multiplication, order and torsion.
This changes affine coordinates and curve coefficients; it is not
homogeneous-coordinate scaling. These group and transport results retain
the stated curve, field and point-membership hypotheses.

`sw_projective_valid r (X,Y,Z)` requires carrier coordinates and excludes
the zero triple. These are ordinary homogeneous coordinates, with affine
coordinates `(X/Z,Y/Z)`, not Jacobian coordinates. Validity alone does not
assert the curve equation. `sw_projective_on_curve` adds
`Y^2*Z = X^3 + a*X*Z^2 + b*Z^3`. Under the stated field and coefficient
conditions, `sw_projective_rep` relates precisely these representatives
to their decoded curve points, and `sw_projective_equiv` identifies
common nonzero scalings. Infinity representatives have `X = Z = 0` and
`Y <> 0`. The total decoder maps every triple with `Z = 0` to infinity,
including invalid triples, so decoding is not a validity test.
`sw_projective_equiv_iff_to_point` retains the infinity guards needed
to characterize equivalence by equality of decoding.

`sw_points_card_bound` proves `CARD (sw_points r a b) <= 2*CARD r.carrier+1`
for a finite field and a short-Weierstrass curve. It is not Hasse's bound.
The absence of nonidentity rational 2-torsion makes the cardinality odd;
a root-free cubic is a sufficient test for that absence.
`sw_cardinality_from_odd_divisor` then identifies the full cardinality
as a positive odd divisor `N` when `2*CARD r.carrier+1 < 3*N`. Companion
results obtain the divisor from a subgroup or point order.
`sw_exact_order_certificate` proves order `N > 0` from `[N]P = O` and
`[N/q]P <> O` for every prime divisor `q` of `N`. An annihilation equation
alone does not establish exact order.

`sw_cm_map r beta` fixes infinity and sends `(x,y)` to `(beta*x,y)`.
For a short-Weierstrass curve with `a = 0`, a carrier element `beta` with
`beta^3 = 1` induces a group automorphism whose third iterate is identity;
`beta = 1` is allowed. No primitive-root or concrete eigenvalue claim
is implicit. `sw_cm_map_scalar` states compatibility with the existing
group exponent.

The independent companion theory `ellipticCMCertificates` uses the
existing `GroupEndo`, `Generated`, `order`, `independent` and
`subgroup_cross` APIs, without introducing another group hierarchy.
`cm_independent` starts with a point `P` of exact positive order `M`,
a positive divisor `d` of `M`, and an endomorphism `f` whose third iterate
is identity. For `Q = g.exp (f P) (M DIV d)`, it proves independence
provided the stated cubic eigenvalues are excluded on each prime-order
line for primes dividing `d`. The subgroup-product carrier then has size
`M*d`, giving `M*d <= CARD g.carrier`. This does not require `d` and
`M DIV d` to be coprime. These are generic hypotheses, not certificates
for a particular curve or named field.

## Native builds

With HOL configured and built, run from the repository root:

```sh
(cd examples/algebra/elliptic && ../../../bin/Holmake)
```

The native algebra aggregate also includes this directory:

```sh
(cd examples/algebra && ../../bin/Holmake)
```

The package is explicitly registered in the core parallel build's level-1
example set; it is not dependent on the level-2 algebra aggregate for
selftest coverage. Its local include paths use the sibling `field` and
`ring` directories.

## Scope and legacy development

The historical `examples/elliptic` directory is a separate development
with its own legacy field/group hierarchy and tooling. This package does
not import or modify that hierarchy; its field and group records come
from the current algebra libraries.

The generic theories do not depend on concrete cryptographic instances or
arithmetic certificate libraries. The GF(5) examples illustrate the generic
group, transport and projective interfaces. The separately built
[instance package](instances/README.md) combines these theories with the
[field/certificate package](../field_certificates/README.md); its long
full-cardinality proofs are selected at selftest level 3.
