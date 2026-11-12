(* -------------------------------------------------------------------------
   Quadratic fields for BN254 and BLS12-381

   Documentation
   Construct bn254_fp2 and bls12381_fp2 as PolyModRing (GF p) [1;0;1].
   Representatives are canonical ascending coefficient lists, with [] zero;
   field operations are the existing polynomial quotient operations.

   Public interface
   - prime_3mod4_quadratic_irreducible proves irreducibility of X^2+1
     under prime p and p MOD 4 = 3. finite_field_3mod4_no_square_minus_one
     supplies the finite-field obstruction (including char r <> 2).
   - bn254_fp2_def, bls12381_fp2_def and their *_poly_def definitions name
     the fields and moduli. The matching *_irreducible and *_finite_field
     theorems discharge the construction's hypotheses for these primes.
   - *_card, *_char, *_carrier, *_coefficients_above_one and
     *_frobenius_square describe size, characteristic and representatives;
     the Frobenius identity assumes membership in the corresponding carrier.
   ------------------------------------------------------------------------- *)

Theory pairingQuadraticFields
Ancestors
  namedPrimes namedPrimeFields fieldInstances polyFieldModulo polyIrreducible
  polyModuloRing polyMonic polyRoot polyWeak arithmetic divides

open fieldTheory ringTheory polynomialTheory pred_setTheory

(* HOL polynomial lists have ascending coefficient order: [1;0;1]
   represents 1 + 0*X + X^2, not X^2 + 0*X + 1 by a descending
   coefficient convention.  Quotient elements remain canonical polynomial
   lists (zero is []), rather than pairs with a separately defined product. *)

Theorem finite_field_3mod4_no_square_minus_one:
  !r:'a field.
    FiniteField r /\ CARD r.carrier MOD 4 = 3 /\ char r <> 2 ==>
    !x. x IN r.carrier ==>
      r.prod.exp x 2 <> r.sum.inv r.prod.id
Proof
  rpt strip_tac >>
  `Field r` by metis_tac[FiniteField_def] >>
  qabbrev_tac `k = CARD r.carrier DIV 4` >>
  `CARD r.carrier = 4 * k + 3`
    by (qunabbrev_tac `k` >>
        metis_tac[arithmeticTheory.DIVISION, arithmeticTheory.MULT_COMM,
                  DECIDE ``(0:num) < 4``]) >>
  `r.prod.exp x 4 = r.prod.id`
    by ( `(4:num) = 2 * 2` by decide_tac >>
         metis_tac[field_exp_mult, field_neg_square,
                   field_one_exp, field_one_element]) >>
  `r.prod.exp x 3 = r.prod.op (r.prod.exp x 2) x` by
    metis_tac[field_exp_add, field_exp_small, DECIDE ``(3:num) = 2 + 1``] >>
  `r.prod.exp x 3 = r.sum.inv x`
    by ASM_SIMP_TAC bool_ss
      [field_mult_lneg, field_mult_lone, field_one_element] >>
  `r.prod.exp x (CARD r.carrier) = r.sum.inv x`
    by ASM_SIMP_TAC bool_ss
      [field_exp_add, field_exp_mult, field_one_exp,
       field_mult_lone, field_neg_element] >>
  `x = r.sum.inv x` by metis_tac[finite_field_fermat_thm] >>
  `x <> r.sum.id`
    by metis_tac[field_exp_eq_zero, field_one_ne_zero,
                 DECIDE ``(4:num) <> 0``] >>
  `x IN ring_nonzero r` by metis_tac[field_nonzero_eq] >>
  `r.prod.op x r.prod.id =
   r.prod.op x (r.sum.inv r.prod.id)`
    by metis_tac[field_mult_rneg, field_mult_rone, field_one_element] >>
  `r.prod.id = r.sum.inv r.prod.id`
    by metis_tac[field_mult_lcancel, field_one_element,
                 field_neg_element] >>
  metis_tac[field_neg_one_eq_one]
QED

Theorem prime_3mod4_quadratic_monic:
  !p. prime p ==> poly_monic (GF p) [1;0;1]
Proof
  rpt strip_tac >>
  `1 < p` by metis_tac[ONE_LT_PRIME] >>
  simp[poly_monic_def, Poly_def, GF_element, GF_zero, GF_one,
       poly_lead_def]
QED

Theorem prime_3mod4_quadratic_degree:
  !p. poly_deg (GF p) [1;0;1] = 2
Proof
  simp[poly_deg_def]
QED

Theorem prime_quadratic_eval[local]:
  !p x. prime p /\ x IN (GF p).carrier ==>
    poly_eval (GF p) [1;0;1] x =
    (GF p).sum.op (GF p).prod.id ((GF p).prod.exp x 2)
Proof
  rpt strip_tac >>
  `Field (GF p)` by simp[GF_field] >>
  once_rewrite_tac[GSYM (SPEC ``p:num`` GF_one),
                   GSYM (SPEC ``p:num`` GF_zero)] >>
  simp[poly_eval_def, field_exp_small]
QED

Theorem prime_3mod4_quadratic_roots:
  !p. prime p /\ p MOD 4 = 3 ==>
    poly_roots (GF p) [1;0;1] = {}
Proof
  rpt strip_tac >>
  `FiniteField (GF p) /\ Field (GF p)`
    by simp[GF_finite_field, GF_field] >>
  `char (GF p) <> 2` by (simp[GF_prime_char] >> strip_tac >> fs[]) >>
  `!x. x IN (GF p).carrier ==>
       (GF p).prod.exp x 2 <> (GF p).sum.inv (GF p).prod.id`
    by metis_tac[finite_field_3mod4_no_square_minus_one, GF_card] >>
  simp_tac std_ss[EXTENSION, NOT_IN_EMPTY, poly_roots_def,
                 GSPECIFICATION, poly_root_def] >>
  metis_tac[prime_quadratic_eval, field_add_eq_zero,
            field_exp_element, field_one_element]
QED

Theorem prime_3mod4_quadratic_irreducible:
  !p. prime p /\ p MOD 4 = 3 ==>
    irreducible (PolyRing (GF p)) [1;0;1]
Proof
  metis_tac[GF_field, poly_deg_2_irreducible,
            prime_3mod4_quadratic_monic,
            prime_3mod4_quadratic_degree,
            prime_3mod4_quadratic_roots]
QED

Definition bn254_fp2_poly_def:
  bn254_fp2_poly = [1n;0;1]
End

Definition bn254_fp2_def:
  bn254_fp2 = PolyModRing (GF bn254_p) bn254_fp2_poly
End

Definition bls12381_fp2_poly_def:
  bls12381_fp2_poly = [1n;0;1]
End

Definition bls12381_fp2_def:
  bls12381_fp2 = PolyModRing (GF bls12381_p) bls12381_fp2_poly
End

Theorem bn254_p_mod4:
  bn254_p MOD 4 = 3
Proof
  EVAL_TAC
QED

Theorem bls12381_p_mod4:
  bls12381_p MOD 4 = 3
Proof
  EVAL_TAC
QED

Theorem bn254_fp2_poly_monic:
  poly_monic (GF bn254_p) bn254_fp2_poly
Proof
  simp[bn254_fp2_poly_def, prime_3mod4_quadratic_monic, bn254_p_prime]
QED

Theorem bls12381_fp2_poly_monic:
  poly_monic (GF bls12381_p) bls12381_fp2_poly
Proof
  simp[bls12381_fp2_poly_def, prime_3mod4_quadratic_monic, bls12381_p_prime]
QED

Theorem bn254_fp2_poly_degree:
  poly_deg (GF bn254_p) bn254_fp2_poly = 2
Proof
  simp[bn254_fp2_poly_def, prime_3mod4_quadratic_degree]
QED

Theorem bls12381_fp2_poly_degree:
  poly_deg (GF bls12381_p) bls12381_fp2_poly = 2
Proof
  simp[bls12381_fp2_poly_def, prime_3mod4_quadratic_degree]
QED

Theorem bn254_fp2_irreducible:
  irreducible (PolyRing (GF bn254_p)) bn254_fp2_poly
Proof
  simp[bn254_fp2_poly_def, prime_3mod4_quadratic_irreducible,
       bn254_p_prime, bn254_p_mod4]
QED

Theorem bls12381_fp2_irreducible:
  irreducible (PolyRing (GF bls12381_p)) bls12381_fp2_poly
Proof
  simp[bls12381_fp2_poly_def, prime_3mod4_quadratic_irreducible,
       bls12381_p_prime, bls12381_p_mod4]
QED

Theorem bn254_fp2_finite_field:
  FiniteField bn254_fp2
Proof
  simp[bn254_fp2_def, poly_mod_irreducible_finite_field,
       GF_finite_field, bn254_p_prime, bn254_fp2_irreducible]
QED

Theorem bls12381_fp2_finite_field:
  FiniteField bls12381_fp2
Proof
  simp[bls12381_fp2_def, poly_mod_irreducible_finite_field,
       GF_finite_field, bls12381_p_prime, bls12381_fp2_irreducible]
QED

Theorem bn254_fp2_card:
  CARD bn254_fp2.carrier = bn254_p ** 2
Proof
  simp[bn254_fp2_def, poly_mod_irreducible_field_card,
       GF_finite_field, bn254_p_prime, bn254_fp2_irreducible,
       GF_card, bn254_fp2_poly_degree]
QED

Theorem bls12381_fp2_card:
  CARD bls12381_fp2.carrier = bls12381_p ** 2
Proof
  simp[bls12381_fp2_def, poly_mod_irreducible_field_card,
       GF_finite_field, bls12381_p_prime, bls12381_fp2_irreducible,
       GF_card, bls12381_fp2_poly_degree]
QED

Theorem bn254_fp2_char:
  char bn254_fp2 = bn254_p
Proof
  simp[bn254_fp2_def, poly_mod_ring_char_alt, GF_field, bn254_p_prime,
       bn254_fp2_poly_monic, bn254_fp2_poly_degree, GF_prime_char]
QED

Theorem bls12381_fp2_char:
  char bls12381_fp2 = bls12381_p
Proof
  simp[bls12381_fp2_def, poly_mod_ring_char_alt, GF_field, bls12381_p_prime,
       bls12381_fp2_poly_monic, bls12381_fp2_poly_degree, GF_prime_char]
QED

(* Canonical representatives have degree less than two.  This includes [],
   the canonical zero; nonzero representatives have one or two coefficients. *)
Theorem bn254_fp2_carrier:
  !x. x IN bn254_fp2.carrier <=>
      Poly (GF bn254_p) x /\ poly_deg (GF bn254_p) x < 2
Proof
  simp[bn254_fp2_def, poly_mod_ring_element, bn254_fp2_poly_degree]
QED

Theorem bls12381_fp2_carrier:
  !x. x IN bls12381_fp2.carrier <=>
      Poly (GF bls12381_p) x /\ poly_deg (GF bls12381_p) x < 2
Proof
  simp[bls12381_fp2_def, poly_mod_ring_element, bls12381_fp2_poly_degree]
QED

Theorem bn254_fp2_coefficients_above_one:
  !x k. x IN bn254_fp2.carrier /\ 2 <= k ==>
        poly_coeff (GF bn254_p) x k = 0
Proof
  rw[bn254_fp2_carrier] >>
  `poly_deg (GF bn254_p) x < k` by decide_tac >>
  Cases_on `x = []` >>
  simp[poly_coeff_nonzero, GF_zero]
QED

Theorem bls12381_fp2_coefficients_above_one:
  !x k. x IN bls12381_fp2.carrier /\ 2 <= k ==>
        poly_coeff (GF bls12381_p) x k = 0
Proof
  rw[bls12381_fp2_carrier] >>
  `poly_deg (GF bls12381_p) x < k` by decide_tac >>
  Cases_on `x = []` >>
  simp[poly_coeff_nonzero, GF_zero]
QED

(* Applying the p-power Frobenius twice is the identity. *)
Theorem bn254_fp2_frobenius_square:
  !x. x IN bn254_fp2.carrier ==>
      bn254_fp2.prod.exp x (bn254_p ** 2) = x
Proof
  metis_tac[finite_field_fermat_thm, bn254_fp2_finite_field, bn254_fp2_card]
QED

Theorem bls12381_fp2_frobenius_square:
  !x. x IN bls12381_fp2.carrier ==>
      bls12381_fp2.prod.exp x (bls12381_p ** 2) = x
Proof
  metis_tac[finite_field_fermat_thm, bls12381_fp2_finite_field, bls12381_fp2_card]
QED
