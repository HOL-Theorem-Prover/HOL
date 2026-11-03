# Primality certificate infrastructure
Lucas primality certificates to prove primeness of cryptographic sized primes.
`modExpTheory` and `modExpLib` provide kernel-checked modular exponentiation
using repeated squaring. The certificate checker uses
`modExpLib.MODPOW_CONV` for modular powers and `modExpLib.NAT_CONV` for
the remaining subtraction, division, multiplication, less-than, and numeral
equality checks. The library contains only the arithmetic used by this checker;
modular powers are evaluated by the CV program, not ordinary exponentiation.

The `examples` directory proves primes relevant for elliptic curves.

## Building

With HOL built and `$HOLDIR` set to its root, build the certificate libraries:

```sh
cd "$HOLDIR/examples/algebra/primality"
"$HOLDIR/bin/Holmake"
```

After building, run the decimal-key regressions with `./selftest.exe`.

Build all four example theories (`namedPrimes`, `bn254CofactorPrimes`,
`bls12381CofactorPrimes`, and `bls12381TwistCofactorPrimes`):

```sh
cd "$HOLDIR/examples/algebra/primality/examples"
"$HOLDIR/bin/Holmake"
```

For a single example, use a theory target, for example:

```sh
"$HOLDIR/bin/Holmake" namedPrimesTheory.uo
```

The recursive algebra build also includes the libraries and all four examples:

```sh
cd "$HOLDIR/examples/algebra"
"$HOLDIR/bin/Holmake"
```

`primeCertificateLib.PRIME_CERT_CONV` accepts decimal certificate keys with
leading zeros: keys are normalized before lookup, so `"00017"` and `"17"`
identify the same prime.
