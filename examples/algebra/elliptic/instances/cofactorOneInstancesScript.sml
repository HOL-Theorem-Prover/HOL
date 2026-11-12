(* Cofactor-one cardinalities for secp256k1, P-256 and BN254 G1.

   Documentation
   Starting from the concrete generator-order and finite-field results,
   root-free cubic certificates exclude nonidentity two-torsion. The
   elementary point bound and odd-divisor argument determine the full
   rational-point cardinality; no curve-order formula is assumed here.

   Cofactor definitions: secp256k1_cofactor_def, p256_cofactor_def,
   bn254_g1_cofactor_def (each is 1).
   Cardinalities: secp256k1_card, p256_card, bn254_g1_card.
   Cofactor relations: secp256k1_cofactor, p256_cofactor, bn254_g1_cofactor.
   Full-group identifications: secp256k1_generated_full_group,
   p256_generated_full_group, bn254_g1_generated_full_group.

   Each curve also exports *_cubic_root_free and *_no_two_torsion.
   The equality of Generated with the full sw_group is specific to these
   three curves; it does not extend to BLS12-381 G1 or the G2 twists. *)

Theory cofactorOneInstances
Ancestors
  namedPrimes
  secp256k1Instance p256Instance bn254G1Instance ellipticCardinality
  ellipticTorsion namedPrimeFields fieldInstances shortWeierstrass
  shortWeierstrassGroup polyRoot polyWeak polynomial
Libs
  polynomialCertificateLib

open fieldTheory

Theorem sw_cubic_polynomial_eval[local]:
  !(r:'a field) a b x.
    Field r /\ a IN r.carrier /\ b IN r.carrier /\ x IN r.carrier ==>
    poly_eval r [b;a;r.sum.id;r.prod.id] x = sw_curve_rhs r a b x
Proof
  rpt strip_tac >>
  simp[poly_eval_def, sw_curve_rhs_def, field_exp_small,
       field_mult_ladd, field_mult_radd, field_mult_assoc,
       field_add_assoc, field_add_comm, field_add_assoc_comm]
QED

Theorem sw_cubic_polynomial_root_free[local]:
  !(r:'a field) a b.
    Field r /\ a IN r.carrier /\ b IN r.carrier /\
    poly_roots r [b;a;r.sum.id;r.prod.id] = {} ==>
    !x. x IN r.carrier ==> sw_curve_rhs r a b x <> r.sum.id
Proof
  rpt strip_tac >>
  `poly_eval r [b;a;r.sum.id;r.prod.id] x = r.sum.id` by
    metis_tac[sw_cubic_polynomial_eval] >>
  `x IN poly_roots r [b;a;r.sum.id;r.prod.id]` by
    simp[poly_roots_member, poly_root_def] >>
  metis_tac[pred_setTheory.NOT_IN_EMPTY]
QED

Definition secp256k1_cofactor_def:
  secp256k1_cofactor = 1n
End

Theorem secp256k1_cubic_root_free:
  poly_roots (GF secp256k1_p) [secp256k1_b;secp256k1_a;0;1] = {}
Proof
  let
    val definitions = [secp256k1_p_def, secp256k1_a_def, secp256k1_b_def]
    val normalize = REWRITE_CONV definitions THENC numLib.REDUCE_CONV
    val f = rhs (concl (normalize ``[secp256k1_b;secp256k1_a;0;1]``))
    val prime = REWRITE_RULE [secp256k1_p_def] secp256k1_p_prime
    val certificate = polynomialCertificateLib.NO_ROOTS_RULE prime f
  in CONV_TAC normalize >> ACCEPT_TAC certificate end
QED

Theorem secp256k1_no_two_torsion:
  !P. P IN sw_points secp256k1_base_field secp256k1_a secp256k1_b /\
      (sw_group secp256k1_base_field secp256k1_a secp256k1_b).exp P 2 = ECInfinity ==>
      P = ECInfinity
Proof
  match_mp_tac sw_root_free_no_two_torsion >>
  conj_tac >- ACCEPT_TAC secp256k1_curve >>
  `Field secp256k1_base_field /\ secp256k1_a IN secp256k1_base_field.carrier /\
    secp256k1_b IN secp256k1_base_field.carrier` by
    metis_tac[secp256k1_curve, ShortWeierstrassCurve_def] >>
  match_mp_tac sw_cubic_polynomial_root_free >>
  asm_rewrite_tac[] >>
  simp[secp256k1_base_field_def, GF_eval, secp256k1_cubic_root_free]
QED

Theorem secp256k1_card:
  CARD (sw_points secp256k1_base_field secp256k1_a secp256k1_b) = secp256k1_n
Proof
  `secp256k1_n divides CARD (sw_points secp256k1_base_field secp256k1_a secp256k1_b)` by
    metis_tac[sw_point_order_divides_card, secp256k1_curve,
              secp256k1_base_field_finite_field, secp256k1_generator_member,
              secp256k1_generator_order, secp256k1_group_def] >>
  `0 < secp256k1_n /\ ODD secp256k1_n /\ 2 * secp256k1_p + 1 < 3 * secp256k1_n` by
    (rw[secp256k1_n_def, secp256k1_p_def] >> EVAL_TAC) >>
  irule sw_cardinality_from_odd_divisor >>
  asm_simp_tac bool_ss [secp256k1_curve, secp256k1_base_field_finite_field,
                       secp256k1_base_field_card, secp256k1_no_two_torsion]
QED

Theorem secp256k1_cofactor:
  CARD (sw_points secp256k1_base_field secp256k1_a secp256k1_b) =
    secp256k1_cofactor * secp256k1_n
Proof
  simp[secp256k1_card, secp256k1_cofactor_def]
QED

Theorem secp256k1_generated_full_group:
  secp256k1_subgroup = secp256k1_group
Proof
  rw[secp256k1_subgroup_def, secp256k1_group_def] >>
  irule sw_cofactor_one_generated >>
  simp[secp256k1_curve, secp256k1_base_field_finite_field, secp256k1_generator_member,
       secp256k1_card, REWRITE_RULE [secp256k1_group_def] secp256k1_generator_order]
QED

Definition p256_cofactor_def:
  p256_cofactor = 1n
End

Theorem p256_cubic_root_free:
  poly_roots (GF p256_p) [p256_b;p256_a;0;1] = {}
Proof
  let
    val definitions = [p256_p_def, p256_a_def, p256_b_def]
    val normalize = REWRITE_CONV definitions THENC numLib.REDUCE_CONV
    val f = rhs (concl (normalize ``[p256_b;p256_a;0;1]``))
    val prime = REWRITE_RULE [p256_p_def] p256_p_prime
    val certificate = polynomialCertificateLib.NO_ROOTS_RULE prime f
  in CONV_TAC normalize >> ACCEPT_TAC certificate end
QED

Theorem p256_no_two_torsion:
  !P. P IN sw_points p256_base_field p256_a p256_b /\
      (sw_group p256_base_field p256_a p256_b).exp P 2 = ECInfinity ==>
      P = ECInfinity
Proof
  match_mp_tac sw_root_free_no_two_torsion >>
  conj_tac >- ACCEPT_TAC p256_curve >>
  `Field p256_base_field /\ p256_a IN p256_base_field.carrier /\
    p256_b IN p256_base_field.carrier` by
    metis_tac[p256_curve, ShortWeierstrassCurve_def] >>
  match_mp_tac sw_cubic_polynomial_root_free >>
  asm_rewrite_tac[] >>
  simp[p256_base_field_def, GF_eval, p256_cubic_root_free]
QED

Theorem p256_card:
  CARD (sw_points p256_base_field p256_a p256_b) = p256_n
Proof
  `p256_n divides CARD (sw_points p256_base_field p256_a p256_b)` by
    metis_tac[sw_point_order_divides_card, p256_curve,
              p256_base_field_finite_field, p256_generator_member,
              p256_generator_order, p256_group_def] >>
  `0 < p256_n /\ ODD p256_n /\ 2 * p256_p + 1 < 3 * p256_n` by
    (rw[p256_n_def, p256_p_def] >> EVAL_TAC) >>
  irule sw_cardinality_from_odd_divisor >>
  asm_simp_tac bool_ss [p256_curve, p256_base_field_finite_field,
                       p256_base_field_card, p256_no_two_torsion]
QED

Theorem p256_cofactor:
  CARD (sw_points p256_base_field p256_a p256_b) =
    p256_cofactor * p256_n
Proof
  simp[p256_card, p256_cofactor_def]
QED

Theorem p256_generated_full_group:
  p256_subgroup = p256_group
Proof
  rw[p256_subgroup_def, p256_group_def] >>
  irule sw_cofactor_one_generated >>
  simp[p256_curve, p256_base_field_finite_field, p256_generator_member,
       p256_card, REWRITE_RULE [p256_group_def] p256_generator_order]
QED

Definition bn254_g1_cofactor_def:
  bn254_g1_cofactor = 1n
End

Theorem bn254_g1_cubic_root_free:
  poly_roots (GF bn254_p) [bn254_g1_b;bn254_g1_a;0;1] = {}
Proof
  let
    val definitions = [bn254_p_def, bn254_g1_a_def, bn254_g1_b_def]
    val normalize = REWRITE_CONV definitions THENC numLib.REDUCE_CONV
    val f = rhs (concl (normalize ``[bn254_g1_b;bn254_g1_a;0;1]``))
    val prime = REWRITE_RULE [bn254_p_def] bn254_p_prime
    val certificate = polynomialCertificateLib.NO_ROOTS_RULE prime f
  in CONV_TAC normalize >> ACCEPT_TAC certificate end
QED

Theorem bn254_g1_no_two_torsion:
  !P. P IN sw_points bn254_base_field bn254_g1_a bn254_g1_b /\
      (sw_group bn254_base_field bn254_g1_a bn254_g1_b).exp P 2 = ECInfinity ==>
      P = ECInfinity
Proof
  match_mp_tac sw_root_free_no_two_torsion >>
  conj_tac >- ACCEPT_TAC bn254_g1_curve >>
  `Field bn254_base_field /\ bn254_g1_a IN bn254_base_field.carrier /\
    bn254_g1_b IN bn254_base_field.carrier` by
    metis_tac[bn254_g1_curve, ShortWeierstrassCurve_def] >>
  match_mp_tac sw_cubic_polynomial_root_free >>
  asm_rewrite_tac[] >>
  simp[bn254_base_field_def, GF_eval, bn254_g1_cubic_root_free]
QED

Theorem bn254_g1_card:
  CARD (sw_points bn254_base_field bn254_g1_a bn254_g1_b) = bn254_n
Proof
  `bn254_n divides CARD (sw_points bn254_base_field bn254_g1_a bn254_g1_b)` by
    metis_tac[sw_point_order_divides_card, bn254_g1_curve,
              bn254_base_field_finite_field, bn254_g1_generator_member,
              bn254_g1_generator_order, bn254_g1_group_def] >>
  `0 < bn254_n /\ ODD bn254_n /\ 2 * bn254_p + 1 < 3 * bn254_n` by
    (rw[bn254_n_def, bn254_p_def] >> EVAL_TAC) >>
  irule sw_cardinality_from_odd_divisor >>
  asm_simp_tac bool_ss [bn254_g1_curve, bn254_base_field_finite_field,
                       bn254_base_field_card, bn254_g1_no_two_torsion]
QED

Theorem bn254_g1_cofactor:
  CARD (sw_points bn254_base_field bn254_g1_a bn254_g1_b) =
    bn254_g1_cofactor * bn254_n
Proof
  simp[bn254_g1_card, bn254_g1_cofactor_def]
QED

Theorem bn254_g1_generated_full_group:
  bn254_g1_subgroup = bn254_g1_group
Proof
  rw[bn254_g1_subgroup_def, bn254_g1_group_def] >>
  irule sw_cofactor_one_generated >>
  simp[bn254_g1_curve, bn254_base_field_finite_field, bn254_g1_generator_member,
       bn254_g1_card, REWRITE_RULE [bn254_g1_group_def] bn254_g1_generator_order]
QED

