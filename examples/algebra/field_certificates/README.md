# Named fields and polynomial certificates

Named prime fields for secp256k1, P-256, BN254 and BLS12-381, plus quadratic
and degree-twelve pairing fields and embeddings. Uses HOL's `GF`, `PolyRing`
and `PolyModRing`; has no elliptic-curve dependency. Prime constants and proofs
come from `namedPrimesTheory`.

## Contents

* `namedPrimeFields`: base and scalar fields for the named curves.
* `pairingQuadraticFields`: BN254 and BLS12-381 quadratic extensions.
* `bn254Degree12Certificate`, `bls12381Degree12Certificate`,
  `pairingDegree12Fields`: checked irreducibility and degree-twelve fields.
* `pairingFieldEmbeddings`: injective quadratic-to-degree-twelve field maps.
* `certificateComputeLib`: bounded arithmetic and shared modular powering.
* `polynomialCertificateLib`, `pairingFieldCertificateLib`: checked polynomial
  remainders, modular powers, irreducibility and quotient arithmetic.

## Representation and contracts

Extension elements are ascending-coefficient polynomial lists with residue
coefficients and no trailing zeros; zero is `[]`, not `[0]`.
The certificate libraries kernel-check arithmetic witnesses. See their
signatures for conversion contracts.

Certificate contexts require a closed primality theorem and the documented
literal modulus. Mixed fields/moduli and invalid coefficients are rejected.
Field embeddings alone do not establish a pairing.

## Build

With Poly/ML and a CV-capable standard or experimental kernel, run here:

```sh
"$HOLDIR/bin/Holmake"
./selftest.exe
```

Level-1 selftests cover named/quadratic fields and converter regressions.
Normal builds and levels 2+ also build the expensive degree-twelve certificates.
