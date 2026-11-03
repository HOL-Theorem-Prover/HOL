# Primality certificate infrastructure
Lucas primality certificates to prove primeness of cryptographic sized primes.
`modExpTheory` and `modExpLib` provide kernel-checked modular exponentiation
using repeated squaring. The certificate checker uses
`modExpLib.MODPOW_CONV` for modular powers and `modExpLib.NAT_CONV` for
the remaining subtraction, division, multiplication, less-than, and numeral
equality checks. The library contains only the arithmetic used by this checker;
modular powers are evaluated by the CV program, not ordinary exponentiation.

In examples some primes relevant for elliptic curves are shown.
