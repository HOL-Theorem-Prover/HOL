# Primality certificate infrastructure
Lucas primality certificates to prove primeness of cryptographic sized primes.
The certificate checker rewrites modular powers using
`expModTheory.exp_mod_binary_eqn` and evaluates `exp_mod_binary` through
`cv_transLib.cv_eval`, using the shared translations loaded from `cv_stdTheory`.
It does not define a separate modular-exponentiation algorithm or CV program.
A private arithmetic conversion handles the remaining subtraction, division,
multiplication, less-than, and numeral equality checks without changing the
surrounding Boolean structure.

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
