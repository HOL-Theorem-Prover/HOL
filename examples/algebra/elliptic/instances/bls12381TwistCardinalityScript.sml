(* BLS12-381 G2: full twist cardinality and full-cofactor clearing.

   Documentation
   Over bls12381_fp2, this combines the arithmetic certificates from
   bls12381TwistCardinalityCertificates with a CM-independent product of
   cyclic subgroups. No nonidentity two-torsion and the elementary point
   bound identify its size with the full rational-point cardinality.

   Orders: bls12381_g2_large_point_order, bls12381_g2_second_point_order.
   Product subgroup: bls12381_g2_cardinality_subgroup_is_subgroup,
   bls12381_g2_cardinality_subgroup_card.
   Main interface: bls12381_g2_full_cardinality,
   bls12381_g2_group_card, bls12381_g2_subgroup_is_proper,
   bls12381_g2_full_cofactor_clearing.
   Supporting public facts: bls12381_g2_no_two_torsion,
   bls12381_g2_cofactor_primes, bls12381_g2_cm_eigenvalue_exclusion.

   The full count is bls12381_g2_full_cofactor * bls12381_n; the standard
   generated subgroup has size bls12381_n. Clearing requires a curve
   point and concludes membership in n-torsion, not explicitly in that
   generated subgroup. Effective hash-to-curve cofactors are not used. *)

Theory bls12381TwistCardinality
Ancestors
  namedPrimes bls12381TwistCofactorPrimes
  bls12381TwistCardinalityCertificates
  pairingQuadraticFields pairingTwistInstances ellipticCertificates
  ellipticCardinality ellipticCMMap ellipticCMCertificates ellipticTorsion
  shortWeierstrass shortWeierstrassGroup
Libs
  certificateComputeLib

open arithmeticTheory dividesTheory pred_setTheory groupTheory monoidTheory
     fieldTheory ringTheory fieldInstancesTheory primeTheory numberTheory gcdTheory

(* Expensive scalar and field-power computations are checked in the ancestor
   certificate theory; this theory contains the cardinality argument itself. *)

Theorem bls12381_g2_cubic_nonresidue:
  !z. z IN bls12381_fp2.carrier ==>
    bls12381_fp2.prod.exp z 3 <> bls12381_fp2.sum.inv bls12381_g2_b
Proof
  gen_tac >> disch_tac >>
  irule (ISPECL [``bls12381_fp2``,
    ``bls12381_fp2.sum.inv bls12381_g2_b``,
    ``(bls12381_p ** 2 - 1) DIV 3``] finite_field_cube_nonresidue) >>
  simp[bls12381_fp2_finite_field, bls12381_fp2_card,
       bls12381_g2_cubic_nonresidue_certificate] >>
  CONV_TAC (certificateComputeLib.EVAL_CONV ())
QED

Theorem bls12381_g2_no_two_torsion:
  !P. P IN sw_points bls12381_fp2 bls12381_g2_a bls12381_g2_b /\
      bls12381_g2_group.exp P 2 = ECInfinity ==> P = ECInfinity
Proof
  REWRITE_TAC [bls12381_g2_group_def] >>
  rpt strip_tac >> irule sw_root_free_no_two_torsion >>
  qexistsl_tac [`bls12381_g2_a`, `bls12381_g2_b`, `bls12381_fp2`] >>
  simp[bls12381_g2_curve] >> rpt strip_tac >>
  `bls12381_g2_b IN bls12381_fp2.carrier` by
    metis_tac[bls12381_g2_curve, ShortWeierstrassCurve_def] >>
  qpat_x_assum `sw_curve_rhs bls12381_fp2 bls12381_g2_a bls12381_g2_b x = _`
    mp_tac >>
  ASM_SIMP_TAC bool_ss
    [sw_curve_rhs_def, bls12381_g2_zero_coefficient,
     bls12381_g2_cardinality_field, field_mult_lzero, field_add_rzero,
     field_exp_element, field_add_eq_zero] >>
  strip_tac >>
  mp_tac (Q.SPEC `x` bls12381_g2_cubic_nonresidue) >>
  ASM_SIMP_TAC bool_ss
    [bls12381_g2_cardinality_field, field_exp_element, field_neg_neg]
QED


Theorem bls12381_g2_torsion_prime_divisors:
  prime q /\ q divides bls12381_g2_torsion_factor ==> q = 13 \/ q = 23
Proof
  strip_tac >>
  `q divides (13 * 23)` by
    metis_tac[bls12381_g2_full_cofactor_factorization] >>
  metis_tac[gcdTheory.P_EUCLIDES, prime_divides_only_self,
            bls12381_g2_cofactor_primes]
QED

Theorem bls12381_g2_large_order_prime_divisors:
  prime q /\ q divides bls12381_g2_large_order ==>
  q = 13 \/ q = 23 \/ q = 2713 \/ q = 11953 \/ q = 262069 \/
  q = bls12381_g2_cofactor_prime \/ q = bls12381_n
Proof
  strip_tac >>
  `q divides
    (13 * 23 * 2713 * 11953 * 262069 * bls12381_g2_cofactor_prime * bls12381_n)` by
    metis_tac[bls12381_g2_full_cofactor_factorization] >>
  metis_tac[gcdTheory.P_EUCLIDES, prime_divides_only_self,
            bls12381_g2_cofactor_primes, bls12381_n_prime]
QED

Theorem bls12381_g2_large_point_order:
  order bls12381_g2_group bls12381_g2_large_point = bls12381_g2_large_order
Proof
  REWRITE_TAC [bls12381_g2_group_def] >>
  irule sw_exact_order_certificate >>
  simp[bls12381_g2_curve, bls12381_g2_large_point_member] >>
  `0 < bls12381_g2_large_order` by EVAL_TAC >>
  metis_tac[bls12381_g2_large_order_prime_divisors,
    REWRITE_RULE [bls12381_g2_group_def] bls12381_g2_large_point_scalar_tests]
QED

Theorem bls12381_g2_cube_roots_13[local]:
  t < 13 /\ t ** 3 MOD 13 = 1 ==> t = 1 \/ t = 3 \/ t = 9
Proof
  strip_tac >>
  `t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/
   t = 6 \/ t = 7 \/ t = 8 \/ t = 9 \/ t = 10 \/ t = 11 \/ t = 12` by decide_tac >>
  fs[]
QED

Theorem bls12381_g2_torsion_cubic_roots:
  prime q /\ q divides bls12381_g2_torsion_factor /\
  t < q /\ t ** 3 MOD q = 1 ==>
  (q = 13 /\ (t = 1 \/ t = 3 \/ t = 9)) \/ (q = 23 /\ t = 1)
Proof
  strip_tac >>
  `q = 13 \/ q = 23` by metis_tac[bls12381_g2_torsion_prime_divisors] >>
  fs[] >> metis_tac[bls12381_g2_cube_roots_13, cm_cube_root_coprime,
                    EVAL ``coprime 3 (23 - 1)``]
QED

Theorem bls12381_g2_cm_eigenvalue_exclusion:
  !q t. prime q /\ q divides bls12381_g2_torsion_factor /\
        t < q /\ t ** 3 MOD q = 1 ==>
    sw_cm_map bls12381_fp2 bls12381_g2_cm_beta
      (bls12381_g2_group.exp bls12381_g2_large_point (bls12381_g2_large_order DIV q)) <>
    bls12381_g2_group.exp
      (bls12381_g2_group.exp bls12381_g2_large_point (bls12381_g2_large_order DIV q)) t
Proof
  rpt strip_tac >>
  `Group bls12381_g2_group /\
   bls12381_g2_large_point IN bls12381_g2_group.carrier` by
    metis_tac[bls12381_g2_finite_group, FiniteAbelianGroup_def_alt,
              FiniteGroup_def, bls12381_g2_group_def, sw_group_carrier,
              bls12381_g2_large_point_member] >>
  drule_all bls12381_g2_torsion_cubic_roots >>
  strip_tac >>
  FULL_SIMP_TAC bool_ss
    [GSYM group_exp_mult,
     bls12381_g2_cm_scalar_exclusions, arithmeticTheory.MULT_CLAUSES]
QED

Theorem bls12381_g2_second_point_member:
  bls12381_g2_second_point IN bls12381_g2_group.carrier
Proof
  `Group bls12381_g2_group /\
   bls12381_g2_large_point IN bls12381_g2_group.carrier` by
    metis_tac[bls12381_g2_finite_group, FiniteAbelianGroup_def_alt,
              FiniteGroup_def, bls12381_g2_group_def,
              sw_group_carrier, bls12381_g2_large_point_member] >>
  rw[bls12381_g2_second_point_def] >>
  metis_tac[bls12381_g2_cm_endomorphism, GroupEndo_def,
            group_homo_element, group_exp_element]
QED

Theorem bls12381_g2_second_point_order:
  order bls12381_g2_group bls12381_g2_second_point = bls12381_g2_torsion_factor
Proof
  `Group bls12381_g2_group /\
   bls12381_g2_large_point IN bls12381_g2_group.carrier` by
    metis_tac[bls12381_g2_finite_group, FiniteAbelianGroup_def_alt,
              FiniteGroup_def, bls12381_g2_group_def,
              sw_group_carrier, bls12381_g2_large_point_member] >>
  `GroupIso (sw_cm_map bls12381_fp2 bls12381_g2_cm_beta)
     bls12381_g2_group bls12381_g2_group` by
    metis_tac[cm_order_three_automorphism, bls12381_g2_cm_endomorphism,
              bls12381_g2_cm_third] >>
  `0 < bls12381_g2_torsion_factor /\
   bls12381_g2_torsion_factor divides bls12381_g2_large_order` by EVAL_TAC >>
  rw[bls12381_g2_second_point_def] >>
  `sw_cm_map bls12381_fp2 bls12381_g2_cm_beta bls12381_g2_large_point
     IN bls12381_g2_group.carrier` by
    metis_tac[GroupIso_def, group_homo_element] >>
  `order bls12381_g2_group
     (sw_cm_map bls12381_fp2 bls12381_g2_cm_beta bls12381_g2_large_point) =
   bls12381_g2_large_order` by
    metis_tac[group_iso_order, bls12381_g2_large_point_order] >>
  `0 < bls12381_g2_large_order` by
    CONV_TAC (REWRITE_CONV [bls12381_g2_large_order_def] THENC
      certificateComputeLib.NAT_CONV) >>
  metis_tac[group_order_exp_cofactor]
QED

Theorem bls12381_g2_cardinality_subgroup_is_subgroup:
  Subgroup bls12381_g2_cardinality_subgroup bls12381_g2_group
Proof
  rw[bls12381_g2_cardinality_subgroup_def] >>
  irule abelian_subgroup_cross_subgroup >>
  metis_tac[bls12381_g2_finite_group, FiniteAbelianGroup_def,
            FiniteAbelianGroup_def_alt, AbelianGroup_def, generated_subgroup,
            bls12381_g2_second_point_member, bls12381_g2_large_point_member,
            bls12381_g2_group_def, sw_group_carrier]
QED

Theorem bls12381_g2_cardinality_subgroup_card:
  CARD bls12381_g2_cardinality_subgroup.carrier =
    bls12381_g2_full_cofactor * bls12381_n
Proof
  `0 < bls12381_g2_large_order /\ 0 < bls12381_g2_torsion_factor /\
   bls12381_g2_torsion_factor divides bls12381_g2_large_order` by EVAL_TAC >>
  REWRITE_TAC [bls12381_g2_cardinality_subgroup_def] >>
  `bls12381_g2_full_cofactor * bls12381_n =
    bls12381_g2_large_order * bls12381_g2_torsion_factor` by
    metis_tac[bls12381_g2_full_cofactor_factorization] >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  irule (Q.INST
    [`f` |-> `sw_cm_map bls12381_fp2 bls12381_g2_cm_beta`]
    (INST_TYPE [``:'a`` |-> ``:num list sw_point``]
      cm_independent_product_card)) >>
  metis_tac[bls12381_g2_finite_group, FiniteAbelianGroup_def_alt,
            bls12381_g2_large_point_member, bls12381_g2_group_def,
            sw_group_carrier, bls12381_g2_large_point_order,
            bls12381_g2_cm_endomorphism, bls12381_g2_cm_third,
            bls12381_g2_second_point_def, bls12381_g2_cm_eigenvalue_exclusion]
QED

Theorem bls12381_g2_full_cardinality:
  CARD (sw_points bls12381_fp2 bls12381_g2_a bls12381_g2_b) =
    bls12381_g2_full_cofactor * bls12381_n
Proof
  irule (Q.INST [`h` |-> `bls12381_g2_cardinality_subgroup`]
    (INST_TYPE [``:'a`` |-> ``:num list``]
      sw_cardinality_from_odd_subgroup)) >>
  simp[bls12381_g2_curve, bls12381_fp2_finite_field,
       GSYM bls12381_g2_group_def,
       bls12381_g2_cardinality_subgroup_is_subgroup,
       bls12381_g2_cardinality_subgroup_card,
       bls12381_g2_no_two_torsion, bls12381_fp2_card] >>
  CONV_TAC (REWRITE_CONV
    [bls12381_g2_full_cofactor_def, bls12381_n_def, bls12381_p_def] THENC
    certificateComputeLib.NAT_CONV) >>
  EVAL_TAC
QED

Theorem bls12381_g2_group_card:
  CARD bls12381_g2_group.carrier = bls12381_g2_full_cofactor * bls12381_n
Proof
  simp[bls12381_g2_group_def, bls12381_g2_full_cardinality]
QED

Theorem bls12381_g2_subgroup_is_proper:
  bls12381_g2_subgroup.carrier PSUBSET bls12381_g2_group.carrier
Proof
  `bls12381_g2_subgroup.carrier SUBSET bls12381_g2_group.carrier` by
    metis_tac[bls12381_g2_subgroup_is_subgroup, subgroup_property_all] >>
  `CARD bls12381_g2_subgroup.carrier < CARD bls12381_g2_group.carrier` by
    (SIMP_TAC bool_ss
       [bls12381_g2_subgroup_card, bls12381_g2_group_card] >>
     CONV_TAC (certificateComputeLib.EVAL_CONV ())) >>
  metis_tac[PSUBSET_DEF, prim_recTheory.LESS_REFL]
QED

Theorem bls12381_g2_full_cofactor_clearing:
  P IN sw_points bls12381_fp2 bls12381_g2_a bls12381_g2_b ==>
  bls12381_g2_group.exp P bls12381_g2_full_cofactor IN
    (sw_torsion_group bls12381_fp2 bls12381_g2_a bls12381_g2_b bls12381_n).carrier
Proof
  strip_tac >> REWRITE_TAC [bls12381_g2_group_def] >>
  irule sw_cofactor_clearing >>
  metis_tac[bls12381_fp2_finite_field, bls12381_g2_curve,
            bls12381_g2_full_cardinality]
QED

