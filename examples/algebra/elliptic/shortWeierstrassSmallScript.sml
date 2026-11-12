(* ------------------------------------------------------------------------- *)
(* Worked Example: y^2 = x^3 + 1 over GF 5                                    *)
(* ------------------------------------------------------------------------- *)
(*
   Documentation

   A small concrete example of the generic curve, group, torsion and
   field-map interfaces. It transports the curve through the isomorphic
   option-valued field ring_inj_image (GF 5) SOME, and changes coordinates
   by (x,y) -> (2^2*x,2^3*y) over GF 5.

   Point set and group:
     sw_GF5_curve, sw_GF5_points, sw_GF5_card, sw_GF5_finite_group.
   Scalars and subgroups:
     sw_GF5_scalar_six, sw_GF5_order_divides_six.
     sw_GF5_generator_order, sw_GF5_generated   (2,2) generates all six points.
     sw_GF5_cofactor_subgroups, sw_GF5_torsion_three.
   Field transport:
     sw_GF5_option_field, sw_GF5_option_curve, sw_GF5_option_group_iso,
       sw_GF5_option_generator_order, sw_GF5_option_torsion_three.
   Coordinate scaling:
     sw_GF5_scaled_curve, sw_GF5_scale_group_iso, sw_GF5_scale_generator,
       sw_GF5_scaled_generator_order.
     The target is y^2 = x^3 + 4; (2,2) maps to (3,1), still of order six.
   Projective coordinates:
     sw_GF5_projective_affine, sw_GF5_projective_infinity,
       sw_GF5_projective_nonrepresentatives, sw_GF5_projective_classes.
     (4,4,2) represents (2,2), (0,3,0) represents infinity, and the zero
     triple and off-curve infinity triples are rejected.
*)

Theory shortWeierstrassSmall
Ancestors
  shortWeierstrass shortWeierstrassGroup
  ellipticTorsion ellipticMorphisms ellipticScaling fieldInstances fieldMap
  shortWeierstrassProjective

Theorem sw_GF5_elements[local]:
  !x.
    x IN (GF 5).carrier <=>
    x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4
Proof
  rw[GF_element] >>
  decide_tac
QED

Theorem sw_GF5_curve:
  ShortWeierstrassCurve (GF 5) 0 1
Proof
  rw[ShortWeierstrassCurve_def, GF_field, groupTheory.PRIME_5, GF_element,
     GF_char, sw_discriminant_def, GF_eval, GF_sum_inv,
     monoidTheory.monoid_exp_def] >>
  EVAL_TAC
QED

Theorem sw_GF5_affine_truth_table[local]:
  ~sw_on_curve (GF 5) 0 1 (ECAffine 0 0) /\
   sw_on_curve (GF 5) 0 1 (ECAffine 0 1) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 0 2) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 0 3) /\
   sw_on_curve (GF 5) 0 1 (ECAffine 0 4) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 1 0) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 1 1) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 1 2) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 1 3) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 1 4) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 2 0) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 2 1) /\
   sw_on_curve (GF 5) 0 1 (ECAffine 2 2) /\
   sw_on_curve (GF 5) 0 1 (ECAffine 2 3) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 2 4) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 3 0) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 3 1) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 3 2) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 3 3) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 3 4) /\
   sw_on_curve (GF 5) 0 1 (ECAffine 4 0) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 4 1) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 4 2) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 4 3) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 4 4)
Proof
  rw[sw_on_curve_def, sw_curve_rhs_def, GF_element, GF_eval,
     monoidTheory.monoid_exp_def] >>
  EVAL_TAC
QED

Theorem sw_GF5_affine_points[local]:
  !x y.
    sw_on_curve (GF 5) 0 1 (ECAffine x y) <=>
    (x = 0 /\ y = 1) \/
    (x = 0 /\ y = 4) \/
    (x = 2 /\ y = 2) \/
    (x = 2 /\ y = 3) \/
    (x = 4 /\ y = 0)
Proof
  metis_tac[sw_on_curve_ECAffine, sw_GF5_elements,
            sw_GF5_affine_truth_table]
QED

Theorem sw_GF5_points:
  sw_points (GF 5) 0 1 =
    {ECInfinity;
     ECAffine 0 1;
     ECAffine 0 4;
     ECAffine 2 2;
     ECAffine 2 3;
     ECAffine 4 0}
Proof
  rw[pred_setTheory.EXTENSION, sw_points_member] >>
  Cases_on `x` >-
    simp[] >>
  rw[sw_GF5_affine_points] >>
  simp[]
QED

Theorem sw_GF5_card:
  CARD (sw_points (GF 5) 0 1) = 6
Proof
  rw[sw_GF5_points]
QED

Theorem sw_GF5_finite_group:
  FiniteAbelianGroup (sw_group (GF 5) 0 1)
Proof
  irule short_weierstrass_finite_group >>
  simp[sw_GF5_curve, GF_finite_field, groupTheory.PRIME_5]
QED

Theorem sw_GF5_scalar_six:
  P IN sw_points (GF 5) 0 1 ==>
  (sw_group (GF 5) 0 1).exp P 6 = ECInfinity
Proof
  strip_tac >>
  `FiniteGroup (sw_group (GF 5) 0 1)` by
    metis_tac[sw_GF5_finite_group, groupTheory.FiniteAbelianGroup_def_alt] >>
  MP_TAC (Q.ISPECL [`sw_group (GF 5) 0 1`, `P:num sw_point`]
    groupTheory.finite_group_Fermat) >>
  simp[sw_group_carrier, sw_group_id, sw_GF5_card]
QED

Theorem sw_GF5_order_divides_six:
  P IN sw_points (GF 5) 0 1 ==>
  order (sw_group (GF 5) 0 1) P divides 6
Proof
  strip_tac >>
  `FiniteGroup (sw_group (GF 5) 0 1)` by
    metis_tac[sw_GF5_finite_group, groupTheory.FiniteAbelianGroup_def_alt] >>
  MP_TAC (Q.ISPEC `sw_group (GF 5) 0 1` groupTheory.group_order_divides) >>
  simp[sw_group_carrier, sw_GF5_card] >>
  metis_tac[sw_points_member]
QED

Theorem sw_GF5_prod_inv_witness[local]:
  x < 5 /\ x <> 0 /\ y < 5 /\ (x * y) MOD 5 = 1 ==>
  (GF 5).prod.inv x = y
Proof
  rpt strip_tac >>
  `Field (GF 5)` by simp[GF_field, groupTheory.PRIME_5] >>
  `(GF 5).prod.inv x = (Invertibles (GF 5).prod).inv x` by
    metis_tac[sw_field_prod_inv_eq, GF_eval] >>
  asm_rewrite_tac[] >>
  CONV_TAC SYM_CONV >>
  irule ringTheory.ring_unit_rinv_unique >>
  simp[GSYM fieldTheory.field_nonzero_unit, fieldTheory.field_nonzero_eq,
       GF_eval, fieldTheory.field_is_ring]
QED

Theorem sw_GF5_prod_inv_table[local]:
  (GF 5).prod.inv 1 = 1 /\
  (GF 5).prod.inv 2 = 3 /\
  (GF 5).prod.inv 3 = 2 /\
  (GF 5).prod.inv 4 = 4
Proof
  rpt conj_tac >> irule sw_GF5_prod_inv_witness >> simp[]
QED

Theorem sw_GF5_generator_scalars[local]:
  (sw_group (GF 5) 0 1).exp (ECAffine 2 2) 1 = ECAffine 2 2 /\
  (sw_group (GF 5) 0 1).exp (ECAffine 2 2) 2 = ECAffine 0 4 /\
  (sw_group (GF 5) 0 1).exp (ECAffine 2 2) 3 = ECAffine 4 0 /\
  (sw_group (GF 5) 0 1).exp (ECAffine 2 2) 4 = ECAffine 0 1 /\
  (sw_group (GF 5) 0 1).exp (ECAffine 2 2) 5 = ECAffine 2 3
Proof
  simp[monoidTheory.monoid_exp_def,
       EVAL ``FUNPOW (f:'a->'a) 1 x``,
       EVAL ``FUNPOW (f:'a->'a) 2 x``,
       EVAL ``FUNPOW (f:'a->'a) 3 x``,
       EVAL ``FUNPOW (f:'a->'a) 4 x``,
       EVAL ``FUNPOW (f:'a->'a) 5 x``,
       sw_group_id, sw_group_op, sw_add_def, sw_slope_def,
       sw_add_x_def, sw_add_y_def, sw_GF5_prod_inv_table,
       GF_eval, GF_sum_inv] >>
  EVAL_TAC
QED

Theorem sw_GF5_generator_order:
  order (sw_group (GF 5) 0 1) (ECAffine 2 2) = 6
Proof
  rw[groupTheory.group_order_thm] >-
    (irule sw_GF5_scalar_six >>
     SIMP_TAC bool_ss [sw_GF5_points, pred_setTheory.IN_INSERT,
                      pred_setTheory.NOT_IN_EMPTY]) >>
  `m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5` by decide_tac >>
  pop_assum strip_assume_tac >>
  fs[sw_GF5_generator_scalars]
QED

Theorem sw_GF5_generated:
  Generated (sw_group (GF 5) 0 1) (ECAffine 2 2) =
  sw_group (GF 5) 0 1
Proof
  irule sw_cofactor_one_generated >>
  SIMP_TAC bool_ss
    [sw_GF5_curve, sw_GF5_points, sw_GF5_card, sw_GF5_generator_order,
     GF_finite_field, groupTheory.PRIME_5,
     pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]
QED

Theorem sw_GF5_cofactor_subgroups:
  (sw_group (GF 5) 0 1).exp (ECAffine 2 2) 2 = ECAffine 0 4 /\
  (sw_group (GF 5) 0 1).exp (ECAffine 2 2) 3 = ECAffine 4 0 /\
  order (sw_group (GF 5) 0 1)
    ((sw_group (GF 5) 0 1).exp (ECAffine 2 2) 2) = 3 /\
  order (sw_group (GF 5) 0 1)
    ((sw_group (GF 5) 0 1).exp (ECAffine 2 2) 3) = 2 /\
  (sw_group (GF 5) 0 1).exp (ECAffine 2 2) 2 IN
    (sw_torsion_group (GF 5) 0 1 3).carrier /\
  (sw_group (GF 5) 0 1).exp (ECAffine 2 2) 3 IN
    (sw_torsion_group (GF 5) 0 1 2).carrier
Proof
  rpt conj_tac >| [
    simp[sw_GF5_generator_scalars],
    simp[sw_GF5_generator_scalars],
    irule sw_cofactor_clearing_order,
    irule sw_cofactor_clearing_order,
    irule sw_cofactor_clearing,
    irule sw_cofactor_clearing
  ] >>
  SIMP_TAC bool_ss
    [sw_GF5_curve, sw_GF5_points, sw_GF5_card, sw_GF5_generator_order,
     GF_finite_field, groupTheory.PRIME_5,
     pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >>
  decide_tac
QED

Theorem sw_GF5_scalar_three[local]:
  !P. P IN sw_points (GF 5) 0 1 ==>
    ((sw_group (GF 5) 0 1).exp P 3 = ECInfinity <=>
     P = ECInfinity \/ P = ECAffine 0 1 \/ P = ECAffine 0 4)
Proof
  SIMP_TAC bool_ss [sw_GF5_points, pred_setTheory.IN_INSERT,
                   pred_setTheory.NOT_IN_EMPTY] >>
  rw[] >>
  simp[monoidTheory.monoid_exp_def,
       EVAL ``FUNPOW (f:'a->'a) 3 x``,
       EVAL ``FUNPOW (f:'a->'a) 2 x``,
       sw_group_id, sw_group_op, sw_add_def, sw_slope_def,
       sw_add_x_def, sw_add_y_def, sw_GF5_prod_inv_table,
       GF_eval, GF_sum_inv] >>
  EVAL_TAC
QED

Theorem sw_GF5_torsion_three:
  (sw_torsion_group (GF 5) 0 1 3).carrier =
  {ECInfinity; ECAffine 0 1; ECAffine 0 4}
Proof
  SIMP_TAC bool_ss [pred_setTheory.EXTENSION, sw_torsion_member] >>
  metis_tac[sw_GF5_scalar_three, sw_GF5_points,
            pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]
QED

Theorem sw_GF5_option_field:
  FiniteField (ring_inj_image (GF 5) SOME) /\
  FieldIso SOME (GF 5) (ring_inj_image (GF 5) SOME)
Proof
  `INJ (SOME:num->num option) (GF 5).carrier UNIV` by
    rw[pred_setTheory.INJ_DEF] >>
  `FiniteField (GF 5)` by
    simp[GF_finite_field, groupTheory.PRIME_5] >>
  conj_tac >- metis_tac[field_inj_image_finite_field] >>
  rw[FieldIso_def] >-
    metis_tac[field_inj_image_field_homo, fieldTheory.FiniteField_def] >>
  rw[ringTheory.ring_inj_image_carrier, pred_setTheory.BIJ_DEF,
     pred_setTheory.INJ_DEF, pred_setTheory.SURJ_DEF,
     pred_setTheory.IN_IMAGE] >>
  metis_tac[]
QED

Theorem sw_GF5_option_curve:
  ShortWeierstrassCurve
    (ring_inj_image (GF 5) SOME) (SOME 0) (SOME 1)
Proof
  metis_tac[sw_field_iso_curve, sw_GF5_curve, sw_GF5_option_field,
            fieldTheory.FiniteField_def]
QED

Theorem sw_GF5_option_group_iso:
  GroupIso (sw_map_point SOME) (sw_group (GF 5) 0 1)
    (sw_group (ring_inj_image (GF 5) SOME) (SOME 0) (SOME 1))
Proof
  metis_tac[sw_field_iso_group, sw_GF5_curve, sw_GF5_option_field,
            fieldTheory.FiniteField_def]
QED

Theorem sw_GF5_option_generator_order:
  order (sw_group (ring_inj_image (GF 5) SOME) (SOME 0) (SOME 1))
    (ECAffine (SOME 2) (SOME 2)) = 6
Proof
  `ECAffine 2 2 IN sw_points (GF 5) 0 1` by
    SIMP_TAC bool_ss [sw_GF5_points, pred_setTheory.IN_INSERT,
                     pred_setTheory.NOT_IN_EMPTY] >>
  `order (sw_group (ring_inj_image (GF 5) SOME) (SOME 0) (SOME 1))
     (sw_map_point SOME (ECAffine 2 2)) = 6` by
    metis_tac[sw_curve_iso_order, sw_GF5_curve, sw_GF5_option_curve,
              sw_GF5_option_group_iso, sw_GF5_generator_order] >>
  fs[sw_map_point_def]
QED

Theorem sw_GF5_option_torsion_three:
  (sw_torsion_group
    (ring_inj_image (GF 5) SOME) (SOME 0) (SOME 1) 3).carrier =
  {ECInfinity; ECAffine (SOME 0) (SOME 1); ECAffine (SOME 0) (SOME 4)}
Proof
  `GroupIso (sw_map_point SOME)
     (sw_torsion_group (GF 5) 0 1 3)
     (sw_torsion_group
       (ring_inj_image (GF 5) SOME) (SOME 0) (SOME 1) 3)` by
    metis_tac[sw_field_iso_torsion, sw_GF5_curve, sw_GF5_option_field,
              fieldTheory.FiniteField_def] >>
  `(sw_torsion_group
      (ring_inj_image (GF 5) SOME) (SOME 0) (SOME 1) 3).carrier =
   IMAGE (sw_map_point SOME) (sw_torsion_group (GF 5) 0 1 3).carrier` by
    metis_tac[groupTheory.group_iso_bij, pred_setTheory.BIJ_IMAGE] >>
  simp[sw_GF5_torsion_three, sw_map_point_def]
QED

(* With u = 2 the coefficients (0,1) become (0,4), not (0,1). *)
Theorem sw_GF5_scale_parameters[local]:
  2 IN (GF 5).carrier /\ 2 <> (GF 5).sum.id /\
  (GF 5).prod.op ((GF 5).prod.exp 2 4) 0 = 0 /\
  (GF 5).prod.op ((GF 5).prod.exp 2 6) 1 = 4
Proof
  rw[GF_element, GF_eval, monoidTheory.monoid_exp_def] >>
  EVAL_TAC
QED

Theorem sw_GF5_scaled_curve:
  ShortWeierstrassCurve (GF 5) 0 4
Proof
  metis_tac[sw_scale_curve, sw_GF5_curve, sw_GF5_scale_parameters]
QED

Theorem sw_GF5_scale_group_iso:
  GroupIso (sw_scale_point (GF 5) 2)
    (sw_group (GF 5) 0 1) (sw_group (GF 5) 0 4)
Proof
  metis_tac[sw_scale_group_iso, sw_GF5_curve, sw_GF5_scale_parameters]
QED

Theorem sw_GF5_scale_generator:
  sw_scale_point (GF 5) 2 (ECAffine 2 2) = ECAffine 3 1
Proof
  rw[sw_scale_point_def, GF_eval, monoidTheory.monoid_exp_def] >>
  EVAL_TAC
QED

Theorem sw_GF5_scaled_generator_order:
  order (sw_group (GF 5) 0 4) (ECAffine 3 1) = 6
Proof
  `ECAffine 2 2 IN sw_points (GF 5) 0 1` by
    SIMP_TAC bool_ss [sw_GF5_points, pred_setTheory.IN_INSERT,
                     pred_setTheory.NOT_IN_EMPTY] >>
  metis_tac[sw_scale_order, sw_GF5_curve, sw_GF5_scale_parameters,
            sw_GF5_scale_generator, sw_GF5_generator_order]
QED

Theorem sw_GF5_projective_affine:
  sw_projective_rep (GF 5) 0 1 (4,4,2) (ECAffine 2 2)
Proof
  qsuff_tac
    `sw_projective_rep (GF 5) 0 1
       (sw_projective_scale (GF 5) 2
         (sw_point_to_projective (GF 5) (ECAffine 2 2)))
       (ECAffine 2 2)`
  >- simp[sw_projective_scale_def, sw_point_to_projective_def, GF_eval] >>
  MATCH_MP_TAC sw_projective_rep_scale >>
  simp[GF_field, groupTheory.PRIME_5, GF_eval] >>
  MATCH_MP_TAC sw_point_to_projective_rep >>
  SIMP_TAC bool_ss [GF_field, groupTheory.PRIME_5, sw_GF5_points,
                   pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]
QED

Theorem sw_GF5_projective_infinity:
  sw_projective_rep (GF 5) 0 1 (0,3,0) ECInfinity
Proof
  simp[sw_projective_rep_def, sw_projective_valid_def,
       sw_projective_to_point_def, GF_eval]
QED

Theorem sw_GF5_projective_nonrepresentatives:
  ~sw_projective_valid (GF 5) (0,0,0) /\
  ~sw_projective_rep (GF 5) 0 1 (1,1,0) ECInfinity
Proof
  simp[sw_projective_valid_def, sw_projective_rep_def, GF_eval]
QED

Theorem sw_GF5_projective_classes:
  sw_projective_equiv (GF 5) (2,2,1) (4,4,2) /\
  ~sw_projective_equiv (GF 5) (4,4,2) (0,3,0)
Proof
  `Field (GF 5)` by simp[GF_field, groupTheory.PRIME_5] >>
  `sw_projective_rep (GF 5) 0 1 (2,2,1) (ECAffine 2 2)` by
    (qsuff_tac
       `sw_projective_rep (GF 5) 0 1
          (sw_point_to_projective (GF 5) (ECAffine 2 2)) (ECAffine 2 2)`
     >- simp[sw_point_to_projective_def, GF_eval] >>
     MATCH_MP_TAC sw_point_to_projective_rep >>
     SIMP_TAC bool_ss [GF_field, groupTheory.PRIME_5, sw_GF5_points,
                      pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]) >>
  metis_tac[sw_projective_reps_equiv, sw_GF5_projective_affine,
            sw_GF5_projective_infinity, sw_point_distinct]
QED
