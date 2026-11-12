(* -------------------------------------------------------------------------
   BLS12-381 degree-twelve irreducibility certificate

   Documentation
   bls12381_fp12_poly_def names X^12 - 2*X^6 + 2 over GF bls12381_p,
   using ascending canonical coefficients (polynomial zero is []).

   Public interface
   bls12381_fp12_poly_monic and bls12381_fp12_poly_degree establish the
   modulus shape; bls12381_fp12_irreducible proves irreducibility for
   constructing bls12381_fp12 in pairingDegree12Fields.

   The proof uses bls12381_p_prime and polynomialCertificateLib.RABIN12_RULE:
   ML proposes remainders/Bezout data and HOL checks the Rabin premises.
   ------------------------------------------------------------------------- *)

Theory bls12381Degree12Certificate
Ancestors
  namedPrimes namedPrimeFields polynomialCertificate
Libs
  polynomialCertificateLib

open fieldTheory ringTheory polynomialTheory

(* X^12 - 2 X^6 + 2; ascending coefficients in the named prime field.
   ML supplies candidates; HOL checks all remainder and Bezout identities. *)
Definition bls12381_fp12_poly_def:
  bls12381_fp12_poly = [2n;0;0;0;0;0;bls12381_p-2;0;0;0;0;0;1]
End

Theorem bls12381_fp12_poly_monic:
  poly_monic (GF bls12381_p) bls12381_fp12_poly
Proof
  CONV_TAC polynomialCertificateLib.ARITH_CONV
QED

Theorem bls12381_fp12_poly_degree:
  poly_deg (GF bls12381_p) bls12381_fp12_poly = 12
Proof
  simp[bls12381_fp12_poly_def, poly_deg_def]
QED

Theorem bls12381_fp12_irreducible:
  irreducible (PolyRing (GF bls12381_p)) bls12381_fp12_poly
Proof
  REWRITE_TAC [bls12381_p_def] >>
  CONV_TAC (RAND_CONV EVAL) >>
  ACCEPT_TAC (polynomialCertificateLib.RABIN12_RULE
    (REWRITE_RULE [bls12381_p_def] bls12381_p_prime)
    (rhs (concl (EVAL ``bls12381_fp12_poly``))))
QED
