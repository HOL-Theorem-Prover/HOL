(* -------------------------------------------------------------------------
   BN254 degree-twelve irreducibility certificate

   Documentation
   bn254_fp12_poly_def names X^12 - 18*X^6 + 82 over GF bn254_p,
   using ascending canonical coefficients (polynomial zero is []).

   Public interface
   bn254_fp12_poly_monic and bn254_fp12_poly_degree establish the modulus
   shape; bn254_fp12_irreducible proves irreducibility for constructing
   bn254_fp12 in pairingDegree12Fields.

   The proof uses bn254_p_prime and polynomialCertificateLib.RABIN12_RULE:
   ML proposes remainders/Bezout data and HOL checks the Rabin premises.
   ------------------------------------------------------------------------- *)

Theory bn254Degree12Certificate
Ancestors
  namedPrimes namedPrimeFields polynomialCertificate
Libs
  polynomialCertificateLib

open fieldTheory ringTheory polynomialTheory

(* X^12 - 18 X^6 + 82; ascending coefficients in the named prime field.
   ML supplies candidates; HOL checks all remainder and Bezout identities. *)
Definition bn254_fp12_poly_def:
  bn254_fp12_poly = [82n;0;0;0;0;0;bn254_p-18;0;0;0;0;0;1]
End

Theorem bn254_fp12_poly_monic:
  poly_monic (GF bn254_p) bn254_fp12_poly
Proof
  CONV_TAC polynomialCertificateLib.ARITH_CONV
QED

Theorem bn254_fp12_poly_degree:
  poly_deg (GF bn254_p) bn254_fp12_poly = 12
Proof
  simp[bn254_fp12_poly_def, poly_deg_def]
QED

Theorem bn254_fp12_irreducible:
  irreducible (PolyRing (GF bn254_p)) bn254_fp12_poly
Proof
  REWRITE_TAC [bn254_p_def] >>
  CONV_TAC (RAND_CONV EVAL) >>
  ACCEPT_TAC (polynomialCertificateLib.RABIN12_RULE
    (REWRITE_RULE [bn254_p_def] bn254_p_prime)
    (rhs (concl (EVAL ``bn254_fp12_poly``))))
QED
