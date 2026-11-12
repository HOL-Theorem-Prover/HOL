# Named fields and checked polynomial certificates

This standalone package uses HOL's existing `GF`, `PolyRing` and
`PolyModRing` constructions. It depends on the field, finite-field and
polynomial libraries and on `primality/examples`, but not on elliptic-curve
theories. Keeping it outside those prerequisite directories avoids include
cycles.

## Mathematical interface

* `namedPrimeFields` defines `*_base_field` and `*_scalar_field` for the
  prefixes `secp256k1`, `p256`, `bn254` and `bls12381`. The `_field`,
  `_finite_field`, `_card` and `_char` facts establish their field structure,
  size and characteristic. The eight `*_p`/`*_n` constants, their `_def`
  theorems and `_prime` proofs belong to **`namedPrimesTheory`**, imported
  from `../primality/examples`; this package does not duplicate or re-export
  them. Add `namedPrimes` explicitly to `Ancestors` when using those facts.
* `pairingQuadraticFields` constructs `bn254_fp2` and `bls12381_fp2` modulo
  `X^2 + 1`. The reusable `prime_3mod4_quadratic_irreducible` theorem uses
  `prime p` and `p MOD 4 = 3`.
* `bn254Degree12Certificate` and `bls12381Degree12Certificate` prove monicity,
  degree twelve and irreducibility of `X^12 - 18*X^6 + 82` and
  `X^12 - 2*X^6 + 2`, respectively.
* `pairingDegree12Fields` constructs `bn254_fp12` and `bls12381_fp12` from
  these irreducible polynomials. Both extension-field theories expose
  `_finite_field`, `_card`, `_char`, `_carrier`, coefficient-bound and
  Frobenius results.
* `pairingFieldEmbeddings` supplies `bn254_fp2_to_fp12` and
  `bls12381_fp2_to_fp12`, their `_field_homo` and `_inj` proofs, and constant
  and generator-image theorems. With `w = X` in the degree-twelve quotient,
  the quadratic generator maps to `w^6 - 9` for BN254 and `w^6 - 1` for
  BLS12-381.

## Representation

Prime-field elements are natural residues strictly below their modulus.
Extension elements are canonical polynomial lists in **ascending coefficient
order**: `[a; b; c]` represents `a + b*X + c*X^2`. Coefficients are residues,
trailing zeros are absent, and **zero is `[]`, not `[0]`**. Constant inclusion
is `if c = 0 then [] else [c]` for `c < p`.

The `_carrier` theorems require `Poly (GF p) x` and a degree bound. Use the
field-record operations, not ordinary list operations; these are polynomial
quotients, not pair or tower datatypes. The embeddings and Frobenius results
apply to carrier elements. A scalar modulus being prime is not a curve-order
proof, and field embeddings do not establish a pairing.

## Computation and trust boundary

* `certificateComputeTheory.certificate_gf_add` and `_gf_mult` expose GF
  operation equations without unfolding noncomputable record components.
* `certificateComputeLib.NAT_CONV` normalizes natural arithmetic without
  rewriting surrounding Boolean structure. `EVAL_COMPSET ()` and
  `EVAL_CONV ()` snapshot loaded equations with fast arithmetic callbacks;
  retain a snapshot for repeated bounded calculations.
* `certificateComputeLib.MODPOW_CONV` accepts closed `a ** e MOD n`, first
  normalizing arithmetic in its arguments. It rewrites with
  `expModTheory.exp_mod_binary_eqn` and evaluates using
  `cv_transLib.cv_eval` and the shared `cv_stdTheory` translations. There
  is no separate modular-exponentiation implementation or CV program.
  Modulus zero retains HOL's unreduced-power semantics.
* `polynomialCertificateLib` supplies bounded arithmetic, `REMAINDER_CONV`,
  `MODPOW_CONV`, `RABIN12_RULE` and `NO_ROOTS_RULE`. Contexts require a
  **closed** theorem `|- prime p` with numeral `p` and a canonical,
  nonconstant monic literal modulus. Mixed rings/moduli and inappropriate
  input shapes are rejected. See its signature for exact term contracts.
* `pairingFieldCertificateLib.QUOTIENT_CONV` evaluates quotient zero/one,
  addition, multiplication, natural powers and substitution remainders.
  Powers check base membership. Irreducibility is unnecessary for these
  ring computations; abstract quotient inverses remain unevaluated.

ML integer arithmetic, division and Euclid computations only propose
quotients, remainders and Bezout coefficients. HOL checks bounded identities
before applying the polynomial remainder, no-roots and degree-twelve Rabin
criteria. Primality is supplied by the existing Lucas certificate package.
All results are kernel theorems; candidate calculations introduce no axiom or
external arithmetic oracle. The libraries require Poly/ML and CV-capable
standard or experimental kernels, not the OpenTheory kernel.

## Native build and regression checks

With a configured Poly/ML HOL checkout:

```sh
cd "$HOLDIR/examples/algebra/field_certificates"
"$HOLDIR/bin/Holmake"
./selftest.exe
```

`Holmake` builds the full theory/library graph, including both degree-twelve
certificates, and compiles the small converter-contract selftest. The selftest
checks exact input equalities and absence of hypotheses, arithmetic edge
cases, checked small-field computations, and rejection of malformed or
hypothetical certificate contexts. Alternatively, `Holmake` from
`examples/algebra` selects the package through the native aggregate.

Poly/ML PR selftest builds select the package directly at level 1. That level
builds named and quadratic fields and runs the converter tests, without the
degree-twelve irreducibility proofs, which can each take several minutes.
Normal builds and selftest levels 2 and above build the complete package.
`HOLSELFTESTLEVEL` also enables execution of the regression target.

All algebra prerequisite includes are relative to this package, so a worktree
build uses that worktree's mathematical sources even when `HOLDIR` points at
the checkout providing the native binaries. No holbuild manifest is needed.
