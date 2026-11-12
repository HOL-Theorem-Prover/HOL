(* -------------------------------------------------------------------------
   Degree-twelve fields for BN254 and BLS12-381

   Documentation
   bn254_fp12_def and bls12381_fp12_def construct PolyModRing fields from
   the named primes and the irreducibility results in the degree-twelve
   certificate theories. Elements are canonical ascending coefficient lists
   of degree below twelve, with [] zero, not a separate tower datatype.

   Public interface
   - bn254_fp12_finite_field and bls12381_fp12_finite_field establish the
     fields; matching *_card and *_char give p^12 elements and characteristic p.
   - *_carrier and *_coefficients_above_eleven describe representatives;
     *_poly_coefficients specifies the sparse defining polynomials.
   - *_frobenius_twelfth gives x^(p^12) = x for carrier elements.

   The imported certificate theorems, rather than unchecked ML polynomial
   calculations, justify the irreducible quotient construction.
   ------------------------------------------------------------------------- *)

Theory pairingDegree12Fields
Ancestors
  namedPrimes namedPrimeFields bn254Degree12Certificate bls12381Degree12Certificate
  polyFieldModulo polyModuloRing polyMonic polyWeak fieldInstances

open fieldTheory ringTheory polynomialTheory

Definition bn254_fp12_def:
  bn254_fp12 = PolyModRing (GF bn254_p) bn254_fp12_poly
End

Definition bls12381_fp12_def:
  bls12381_fp12 = PolyModRing (GF bls12381_p) bls12381_fp12_poly
End

Theorem bn254_fp12_finite_field:
  FiniteField bn254_fp12
Proof
  simp[bn254_fp12_def, poly_mod_irreducible_finite_field,
       GF_finite_field, bn254_p_prime, bn254_fp12_irreducible]
QED

Theorem bls12381_fp12_finite_field:
  FiniteField bls12381_fp12
Proof
  simp[bls12381_fp12_def, poly_mod_irreducible_finite_field,
       GF_finite_field, bls12381_p_prime, bls12381_fp12_irreducible]
QED

Theorem bn254_fp12_card:
  CARD bn254_fp12.carrier = bn254_p ** 12
Proof
  simp[bn254_fp12_def, poly_mod_irreducible_field_card,
       GF_finite_field, bn254_p_prime, bn254_fp12_irreducible,
       GF_card, bn254_fp12_poly_degree]
QED

Theorem bls12381_fp12_card:
  CARD bls12381_fp12.carrier = bls12381_p ** 12
Proof
  simp[bls12381_fp12_def, poly_mod_irreducible_field_card,
       GF_finite_field, bls12381_p_prime, bls12381_fp12_irreducible,
       GF_card, bls12381_fp12_poly_degree]
QED

Theorem bn254_fp12_char:
  char bn254_fp12 = bn254_p
Proof
  simp[bn254_fp12_def, poly_mod_ring_char_alt, GF_field, bn254_p_prime,
       bn254_fp12_poly_monic, bn254_fp12_poly_degree, GF_prime_char]
QED

Theorem bls12381_fp12_char:
  char bls12381_fp12 = bls12381_p
Proof
  simp[bls12381_fp12_def, poly_mod_ring_char_alt, GF_field, bls12381_p_prime,
       bls12381_fp12_poly_monic, bls12381_fp12_poly_degree, GF_prime_char]
QED

(* Canonical representatives have at most twelve ascending coefficients;
   [] is zero.  There is no separate list-carrier arithmetic implementation. *)
Theorem bn254_fp12_carrier:
  !x. x IN bn254_fp12.carrier <=>
      Poly (GF bn254_p) x /\ poly_deg (GF bn254_p) x < 12
Proof
  simp[bn254_fp12_def, poly_mod_ring_element, bn254_fp12_poly_degree]
QED

Theorem bls12381_fp12_carrier:
  !x. x IN bls12381_fp12.carrier <=>
      Poly (GF bls12381_p) x /\ poly_deg (GF bls12381_p) x < 12
Proof
  simp[bls12381_fp12_def, poly_mod_ring_element, bls12381_fp12_poly_degree]
QED

Theorem bn254_fp12_coefficients_above_eleven:
  !x k. x IN bn254_fp12.carrier /\ 12 <= k ==>
        poly_coeff (GF bn254_p) x k = 0
Proof
  rw[bn254_fp12_carrier] >>
  `poly_deg (GF bn254_p) x < k` by decide_tac >>
  Cases_on `x = []` >>
  simp[poly_coeff_nonzero, GF_zero]
QED

Theorem bls12381_fp12_coefficients_above_eleven:
  !x k. x IN bls12381_fp12.carrier /\ 12 <= k ==>
        poly_coeff (GF bls12381_p) x k = 0
Proof
  rw[bls12381_fp12_carrier] >>
  `poly_deg (GF bls12381_p) x < k` by decide_tac >>
  Cases_on `x = []` >>
  simp[poly_coeff_nonzero, GF_zero]
QED

Theorem degree12_sparse_coefficients[local]:
  !p c a k.
    poly_coeff (GF p) [c;0;0;0;0;0;a;0;0;0;0;0;1] k =
    if k = 0 then c else if k = 6 then a else if k = 12 then 1 else 0
Proof
  rpt gen_tac >>
  Cases_on `k < 13` >- (
    `k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
     k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12`
      by decide_tac >>
    rpt (first_x_assum DISJ_CASES_TAC) >>
    simp[poly_coeff_nonzero_alt, GF_zero]) >>
  `k <> 0 /\ k <> 6 /\ k <> 12` by decide_tac >>
  simp[poly_coeff_nonzero_alt, GF_zero]
QED

Theorem bn254_fp12_poly_coefficients:
  !k. poly_coeff (GF bn254_p) bn254_fp12_poly k =
      if k = 0 then 82 else if k = 6 then bn254_p-18 else
      if k = 12 then 1 else 0
Proof
  simp[bn254_fp12_poly_def, degree12_sparse_coefficients]
QED

Theorem bls12381_fp12_poly_coefficients:
  !k. poly_coeff (GF bls12381_p) bls12381_fp12_poly k =
      if k = 0 then 2 else if k = 6 then bls12381_p-2 else
      if k = 12 then 1 else 0
Proof
  simp[bls12381_fp12_poly_def, degree12_sparse_coefficients]
QED

(* Twelve iterations of p-power Frobenius are the identity. *)
Theorem bn254_fp12_frobenius_twelfth:
  !x. x IN bn254_fp12.carrier ==>
      bn254_fp12.prod.exp x (bn254_p ** 12) = x
Proof
  metis_tac[finite_field_fermat_thm, bn254_fp12_finite_field, bn254_fp12_card]
QED

Theorem bls12381_fp12_frobenius_twelfth:
  !x. x IN bls12381_fp12.carrier ==>
      bls12381_fp12.prod.exp x (bls12381_p ** 12) = x
Proof
  metis_tac[finite_field_fermat_thm, bls12381_fp12_finite_field, bls12381_fp12_card]
QED
