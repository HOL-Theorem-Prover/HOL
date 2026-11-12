(* ------------------------------------------------------------------------- *)
(* Change of Short-Weierstrass Coordinates                                    *)
(* ------------------------------------------------------------------------- *)
(*
   Documentation

   sw_scale_point_def fixes infinity and maps (x,y) to (u^2*x,u^3*y).
   The target coefficients are u^4*a and u^6*b. This is a change between
   affine curve models, not common scaling of a homogeneous triple.

   Main results:
     sw_scale_curve, sw_scale_on_curve, sw_scale_points.
     sw_scale_inverse, sw_scale_add, sw_scale_group_homo, sw_scale_group_iso.
     sw_scale_scalar, sw_scale_order, sw_scale_torsion.

   Group isomorphism and transport results require ShortWeierstrassCurve,
   u in the field carrier and u <> 0; the inverse uses the field inverse of u.
*)

Theory ellipticScaling
Ancestors
  ellipticMorphisms ringLib
  shortWeierstrass shortWeierstrassGroup ellipticTorsion
Libs
  ringLib

open fieldTheory ringTheory groupTheory pred_setTheory ringLibTheory

Definition sw_scale_point_def:
  (sw_scale_point (r:'a field) u ECInfinity = ECInfinity) /\
  (sw_scale_point r u (ECAffine x y) =
    ECAffine (r.prod.op (r.prod.exp u 2) x)
             (r.prod.op (r.prod.exp u 3) y))
End

(* Discharge polynomial identities in the existing commutative-ring model.
   Inverse equations are supplied explicitly by sw_field_prod_inv. *)
fun scale_ring_tac (g as (asl,w)) =
  let
    val ops = CONJUNCTS (MATCH_MP sw_ring_ops
      (ASSUME ``Field (r:'a field)``))
    val rules = map GSYM ops
  in
    (RULE_ASSUM_TAC (REWRITE_RULE rules) >>
     REWRITE_TAC rules >>
     qabbrev_tac `scale_ring = toRing r` >>
     ((W (fn (_,w) => MATCH_MP_TAC (ringLib.RING_RULE w)) >>
       ASM_REWRITE_TAC []) ORELSE ringLib.RING_TAC)) g
  end;

Theorem sw_scale_fraction[local]:
  !(r:'a field) u v n d i j. Field r /\
  u IN r.carrier /\ v IN r.carrier /\ n IN r.carrier /\
  d IN r.carrier /\ i IN r.carrier /\ j IN r.carrier /\
  r.prod.op d i = r.prod.id /\
  r.prod.op (r.prod.op v d) j = r.prod.id ==>
  r.prod.op (r.prod.op (r.prod.op u v) n) j =
    r.prod.op u (r.prod.op n i)
Proof
  rpt strip_tac >> scale_ring_tac
QED

Theorem sw_scale_power_nonzero[local]:
  Field (r:'a field) /\ u IN r.carrier /\ u <> r.sum.id ==>
  !n. r.prod.exp u n IN r.carrier /\ r.prod.exp u n <> r.sum.id
Proof
  metis_tac[field_exp_element, field_exp_eq_zero]
QED

Theorem sw_scale_cancel[local]:
  Field (r:'a field) /\ u IN r.carrier /\ u <> r.sum.id /\
  x IN r.carrier /\ y IN r.carrier ==>
  (r.prod.op (r.prod.exp u n) x = r.prod.op (r.prod.exp u n) y <=> x = y)
Proof
  metis_tac[sw_scale_power_nonzero, field_nonzero_eq, field_mult_lcancel]
QED

Theorem sw_scale_curve:
  ShortWeierstrassCurve (r:'a field) a b /\
  u IN r.carrier /\ u <> r.sum.id ==>
  ShortWeierstrassCurve r (r.prod.op (r.prod.exp u 4) a)
    (r.prod.op (r.prod.exp u 6) b)
Proof
  strip_tac >>
  `Field r /\ a IN r.carrier /\ b IN r.carrier` by
    metis_tac[ShortWeierstrassCurve_def] >>
  `sw_discriminant r (r.prod.op (r.prod.exp u 4) a)
      (r.prod.op (r.prod.exp u 6) b) =
    r.prod.op (r.prod.exp u 12) (sw_discriminant r a b)` by
    (simp_tac bool_ss [sw_discriminant_def] >> scale_ring_tac) >>
  `sw_discriminant r a b IN r.carrier` by
    (simp_tac bool_ss [sw_discriminant_def] >>
     metis_tac[field_neg_element, field_mult_element,
       field_add_element, field_num_element, field_exp_element]) >>
  fs[ShortWeierstrassCurve_def] >>
  metis_tac[field_mult_element, field_exp_element,
    sw_scale_power_nonzero, field_mult_eq_zero]
QED

Theorem sw_scale_on_curve:
  Field (r:'a field) /\ a IN r.carrier /\ b IN r.carrier /\
  u IN r.carrier /\ sw_on_curve r a b P ==>
  sw_on_curve r (r.prod.op (r.prod.exp u 4) a)
    (r.prod.op (r.prod.exp u 6) b) (sw_scale_point r u P)
Proof
  Cases_on `P` >- simp[sw_scale_point_def, sw_on_curve_def] >>
  rename1 `ECAffine x y` >>
  rw[sw_on_curve_def, sw_scale_point_def] >>
  fs[sw_curve_rhs_def] >> scale_ring_tac
QED

Theorem sw_scale_points:
  ShortWeierstrassCurve (r:'a field) a b /\
  u IN r.carrier /\ u <> r.sum.id /\ P IN sw_points r a b ==>
  sw_scale_point r u P IN sw_points r
    (r.prod.op (r.prod.exp u 4) a) (r.prod.op (r.prod.exp u 6) b)
Proof
  metis_tac[sw_scale_on_curve, sw_points_member, ShortWeierstrassCurve_def]
QED

Theorem sw_scale_inverse:
  Field (r:'a field) /\ u IN r.carrier /\ u <> r.sum.id /\
  P IN sw_points r a b ==>
  sw_scale_point r (r.prod.inv u) (sw_scale_point r u P) = P /\
  sw_scale_point r u (sw_scale_point r (r.prod.inv u) P) = P
Proof
  Cases_on `P` >- simp[sw_scale_point_def] >>
  rename1 `ECAffine x y` >> strip_tac >>
  `x IN r.carrier /\ y IN r.carrier` by
    metis_tac[sw_points_member, sw_on_curve_def] >>
  drule_all sw_field_prod_inv >> strip_tac >>
  simp_tac bool_ss [sw_scale_point_def, sw_point_11] >>
  rpt conj_tac >> scale_ring_tac
QED

Theorem sw_scale_neg[local]:
  Field (r:'a field) /\ u IN r.carrier /\
  x IN r.carrier /\ y IN r.carrier ==>
  r.prod.op (r.prod.exp u 3) (r.sum.inv y) =
    r.sum.inv (r.prod.op (r.prod.exp u 3) y)
Proof
  rpt strip_tac >> scale_ring_tac
QED

Theorem sw_scale_slope[local]:
  ShortWeierstrassCurve (r:'a field) a b /\
  u IN r.carrier /\ u <> r.sum.id /\
  sw_on_curve r a b (ECAffine x1 y1) /\
  sw_on_curve r a b (ECAffine x2 y2) /\
  ~(x1 = x2 /\ y1 = r.sum.inv y2) ==>
  sw_slope r a x1 y1 x2 y2 IN r.carrier /\
  sw_slope r (r.prod.op (r.prod.exp u 4) a)
    (r.prod.op (r.prod.exp u 2) x1) (r.prod.op (r.prod.exp u 3) y1)
    (r.prod.op (r.prod.exp u 2) x2) (r.prod.op (r.prod.exp u 3) y2) =
  r.prod.op u (sw_slope r a x1 y1 x2 y2)
Proof
  strip_tac >>
  `Field r /\ a IN r.carrier /\ b IN r.carrier /\
   x1 IN r.carrier /\ y1 IN r.carrier /\
   x2 IN r.carrier /\ y2 IN r.carrier` by
    metis_tac[ShortWeierstrassCurve_def, sw_on_curve_def] >>
  `r.prod.op (r.prod.exp u 2) x1 = r.prod.op (r.prod.exp u 2) x2 <=> x1 = x2` by
    metis_tac[sw_scale_cancel] >>
  Cases_on `x1 = x2` >| [
    `y2 = y1` by
      metis_tac[sw_same_x_on_curve, field_neg_neg, sw_on_curve_def] >>
    gvs[] >>
    `r.prod.op (r.sum.exp r.prod.id 2) y1 IN r.carrier /\
     r.prod.op (r.sum.exp r.prod.id 2) y1 <> r.sum.id` by
      (conj_tac >- metis_tac[field_num_element, field_mult_element] >>
       `r.prod.op (r.sum.exp r.prod.id 2) y1 = r.sum.op y1 y1` by
         rw[field_num_2, field_mult_ladd, field_mult_lone] >>
       metis_tac[field_add_eq_zero]) >>
    `r.prod.op (r.sum.exp r.prod.id 2)
       (r.prod.op (r.prod.exp u 3) y1) =
     r.prod.op (r.prod.exp u 3) (r.prod.op (r.sum.exp r.prod.id 2) y1)` by
       scale_ring_tac >>
    `r.prod.exp u 3 IN r.carrier /\ r.prod.exp u 3 <> r.sum.id` by
      metis_tac[sw_scale_power_nonzero] >>
    `r.prod.op (r.sum.exp r.prod.id 2)
       (r.prod.op (r.prod.exp u 3) y1) IN r.carrier /\
     r.prod.op (r.sum.exp r.prod.id 2)
       (r.prod.op (r.prod.exp u 3) y1) <> r.sum.id` by
      ASM_SIMP_TAC bool_ss [field_mult_element, field_mult_eq_zero] >>
    `r.prod.inv (r.prod.op (r.sum.exp r.prod.id 2) y1) IN r.carrier /\
     r.prod.op (r.prod.op (r.sum.exp r.prod.id 2) y1)
       (r.prod.inv (r.prod.op (r.sum.exp r.prod.id 2) y1)) = r.prod.id` by
       metis_tac[sw_field_prod_inv] >>
    `r.prod.inv (r.prod.op (r.sum.exp r.prod.id 2)
       (r.prod.op (r.prod.exp u 3) y1)) IN r.carrier /\
     r.prod.op (r.prod.op (r.sum.exp r.prod.id 2)
       (r.prod.op (r.prod.exp u 3) y1))
       (r.prod.inv (r.prod.op (r.sum.exp r.prod.id 2)
         (r.prod.op (r.prod.exp u 3) y1))) = r.prod.id` by
       metis_tac[sw_field_prod_inv] >>
    conj_tac >- ASM_SIMP_TAC bool_ss [sw_slope_def, field_mult_element,
      field_add_element, field_num_element, field_exp_element] >>
    ASM_SIMP_TAC bool_ss [sw_slope_def] >>
    qpat_x_assum
      `r.prod.op (r.sum.exp r.prod.id 2) (r.prod.op (r.prod.exp u 3) y1) =
       r.prod.op (r.prod.exp u 3) (r.prod.op (r.sum.exp r.prod.id 2) y1)`
      (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
    qabbrev_tac `tangent_inv = r.prod.inv
      (r.prod.op (r.sum.exp r.prod.id 2) y1)` >>
    qabbrev_tac `scaled_tangent_inv = r.prod.inv
      (r.prod.op (r.prod.exp u 3) (r.prod.op (r.sum.exp r.prod.id 2) y1))` >>
    `r.prod.exp u 3 IN r.carrier /\
     r.sum.op (r.prod.op (r.sum.exp r.prod.id 3) (r.prod.exp x1 2)) a
       IN r.carrier` by
      metis_tac[field_exp_element, field_num_element,
                field_mult_element, field_add_element] >>
    `r.sum.op
       (r.prod.op (r.sum.exp r.prod.id 3)
         (r.prod.op (r.prod.exp (r.prod.exp u 2) 2) (r.prod.exp x1 2)))
       (r.prod.op (r.prod.exp u 4) a) =
     r.prod.op (r.prod.op u (r.prod.exp u 3))
       (r.sum.op (r.prod.op (r.sum.exp r.prod.id 3) (r.prod.exp x1 2)) a)`
      by scale_ring_tac >>
    mp_tac (Q.SPECL
      [`r`, `u`, `r.prod.exp u 3`,
       `r.sum.op (r.prod.op (r.sum.exp r.prod.id 3) (r.prod.exp x1 2)) a`,
       `r.prod.op (r.sum.exp r.prod.id 2) y1`,
       `tangent_inv`, `scaled_tangent_inv`] sw_scale_fraction) >>
    ASM_SIMP_TAC bool_ss [],
    `r.sum.op x2 (r.sum.inv x1) IN r.carrier /\
     r.sum.op x2 (r.sum.inv x1) <> r.sum.id` by
      metis_tac[field_add_element, field_neg_element, field_add_eq_zero,
        field_neg_neg] >>
    `r.prod.op (r.prod.exp u 2) x1 IN r.carrier /\
     r.prod.op (r.prod.exp u 2) x2 IN r.carrier` by
      metis_tac[field_mult_element, field_exp_element] >>
    `r.sum.op (r.prod.op (r.prod.exp u 2) x2)
       (r.sum.inv (r.prod.op (r.prod.exp u 2) x1)) IN r.carrier /\
     r.sum.op (r.prod.op (r.prod.exp u 2) x2)
       (r.sum.inv (r.prod.op (r.prod.exp u 2) x1)) <> r.sum.id` by
      (ASM_SIMP_TAC bool_ss
         [field_add_element, field_neg_element, field_add_eq_zero,
          field_neg_eq] >>
       metis_tac[]) >>
    `r.prod.inv (r.sum.op x2 (r.sum.inv x1)) IN r.carrier /\
     r.prod.op (r.sum.op x2 (r.sum.inv x1))
       (r.prod.inv (r.sum.op x2 (r.sum.inv x1))) = r.prod.id` by
      metis_tac[sw_field_prod_inv] >>
    `r.prod.inv (r.sum.op (r.prod.op (r.prod.exp u 2) x2)
       (r.sum.inv (r.prod.op (r.prod.exp u 2) x1))) IN r.carrier /\
     r.prod.op (r.sum.op (r.prod.op (r.prod.exp u 2) x2)
       (r.sum.inv (r.prod.op (r.prod.exp u 2) x1)))
       (r.prod.inv (r.sum.op (r.prod.op (r.prod.exp u 2) x2)
         (r.sum.inv (r.prod.op (r.prod.exp u 2) x1)))) = r.prod.id` by
      metis_tac[sw_field_prod_inv] >>
    conj_tac >- ASM_SIMP_TAC bool_ss [sw_slope_def, field_mult_element,
      field_add_element, field_neg_element] >>
    ASM_SIMP_TAC bool_ss [sw_slope_def] >>
    qabbrev_tac `secant_inv = r.prod.inv (r.sum.op x2 (r.sum.inv x1))` >>
    qabbrev_tac `scaled_secant_inv = r.prod.inv
      (r.sum.op (r.prod.op (r.prod.exp u 2) x2)
        (r.sum.inv (r.prod.op (r.prod.exp u 2) x1)))` >>
    `r.prod.exp u 2 IN r.carrier /\
     r.sum.op y2 (r.sum.inv y1) IN r.carrier` by
      metis_tac[field_exp_element, field_neg_element, field_add_element] >>
    `r.sum.op (r.prod.op (r.prod.exp u 2) x2)
       (r.sum.inv (r.prod.op (r.prod.exp u 2) x1)) =
     r.prod.op (r.prod.exp u 2) (r.sum.op x2 (r.sum.inv x1))`
      by scale_ring_tac >>
    qpat_x_assum
      `r.sum.op (r.prod.op (r.prod.exp u 2) x2)
         (r.sum.inv (r.prod.op (r.prod.exp u 2) x1)) =
       r.prod.op (r.prod.exp u 2) (r.sum.op x2 (r.sum.inv x1))`
      (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
    `r.sum.op (r.prod.op (r.prod.exp u 3) y2)
       (r.sum.inv (r.prod.op (r.prod.exp u 3) y1)) =
     r.prod.op (r.prod.op u (r.prod.exp u 2))
       (r.sum.op y2 (r.sum.inv y1))` by scale_ring_tac >>
    mp_tac (Q.SPECL
      [`r`, `u`, `r.prod.exp u 2`, `r.sum.op y2 (r.sum.inv y1)`,
       `r.sum.op x2 (r.sum.inv x1)`, `secant_inv`, `scaled_secant_inv`]
      sw_scale_fraction) >>
    ASM_SIMP_TAC bool_ss []
  ]
QED

Theorem sw_scale_add:
  ShortWeierstrassCurve (r:'a field) a b /\
  u IN r.carrier /\ u <> r.sum.id /\
  P IN sw_points r a b /\ Q IN sw_points r a b ==>
  sw_scale_point r u (sw_add r a b P Q) =
  sw_add r (r.prod.op (r.prod.exp u 4) a) (r.prod.op (r.prod.exp u 6) b)
    (sw_scale_point r u P) (sw_scale_point r u Q)
Proof
  Cases_on `P` >- simp[sw_scale_point_def, sw_add_def] >>
  Cases_on `Q` >- simp[sw_scale_point_def, sw_add_def] >>
  rename1 `sw_add r a b (ECAffine x1 y1) (ECAffine x2 y2)` >>
  strip_tac >>
  `Field r /\ x1 IN r.carrier /\ y1 IN r.carrier /\
   x2 IN r.carrier /\ y2 IN r.carrier` by
    metis_tac[ShortWeierstrassCurve_def, sw_points_member, sw_on_curve_def] >>
  `(r.prod.op (r.prod.exp u 2) x1 = r.prod.op (r.prod.exp u 2) x2 /\
    r.prod.op (r.prod.exp u 3) y1 =
      r.sum.inv (r.prod.op (r.prod.exp u 3) y2)) <=>
   (x1 = x2 /\ y1 = r.sum.inv y2)` by
    metis_tac[sw_scale_cancel, sw_scale_neg, field_neg_element] >>
  Cases_on `x1 = x2 /\ y1 = r.sum.inv y2` >-
    ASM_SIMP_TAC bool_ss [sw_add_def, sw_scale_point_def,
                          field_mult_rneg, field_exp_element] >>
  `sw_slope r a x1 y1 x2 y2 IN r.carrier /\
   sw_slope r (r.prod.op (r.prod.exp u 4) a)
     (r.prod.op (r.prod.exp u 2) x1) (r.prod.op (r.prod.exp u 3) y1)
     (r.prod.op (r.prod.exp u 2) x2) (r.prod.op (r.prod.exp u 3) y2) =
   r.prod.op u (sw_slope r a x1 y1 x2 y2)` by
    metis_tac[sw_scale_slope, sw_points_member] >>
  ASM_SIMP_TAC bool_ss [sw_add_def, sw_scale_point_def, LET_THM,
    sw_point_11, sw_add_x_def, sw_add_y_def] >>
  conj_tac >> scale_ring_tac
QED

Theorem sw_scale_group_homo:
  ShortWeierstrassCurve (r:'a field) a b /\
  u IN r.carrier /\ u <> r.sum.id ==>
  GroupHomo (sw_scale_point r u) (sw_group r a b)
    (sw_group r (r.prod.op (r.prod.exp u 4) a) (r.prod.op (r.prod.exp u 6) b))
Proof
  simp_tac bool_ss [GroupHomo_def, sw_group_carrier, sw_group_op] >>
  metis_tac[sw_scale_points, sw_scale_add]
QED

Theorem sw_scale_inverse_power:
  Field (r:'a field) /\ u IN r.carrier /\ u <> r.sum.id /\ b IN r.carrier ==>
  r.prod.op (r.prod.exp (r.prod.inv u) n)
    (r.prod.op (r.prod.exp u n) b) = b
Proof
  strip_tac >> drule_all sw_field_prod_inv >> strip_tac >>
  `r.prod.op (r.prod.inv u) u = r.prod.id` by metis_tac[field_mult_comm] >>
  `r.prod.op (r.prod.exp (r.prod.inv u) n) (r.prod.exp u n) = r.prod.id`
    by metis_tac[field_mult_exp, field_one_exp] >>
  ASM_SIMP_TAC bool_ss
    [GSYM field_mult_assoc, field_exp_element, field_mult_lone]
QED

Theorem sw_scale_group_iso:
  ShortWeierstrassCurve (r:'a field) a b /\
  u IN r.carrier /\ u <> r.sum.id ==>
  GroupIso (sw_scale_point r u) (sw_group r a b)
    (sw_group r (r.prod.op (r.prod.exp u 4) a) (r.prod.op (r.prod.exp u 6) b))
Proof
  strip_tac >>
  `Field r /\ a IN r.carrier /\ b IN r.carrier` by
    metis_tac[ShortWeierstrassCurve_def] >>
  `r.prod.inv u IN r.carrier /\ r.prod.inv u <> r.sum.id` by
    (drule_all sw_field_prod_inv >> strip_tac >>
     metis_tac[field_mult_rzero, field_one_ne_zero]) >>
  `ShortWeierstrassCurve r (r.prod.op (r.prod.exp u 4) a)
     (r.prod.op (r.prod.exp u 6) b)` by metis_tac[sw_scale_curve] >>
  `!Q. Q IN sw_points r (r.prod.op (r.prod.exp u 4) a)
       (r.prod.op (r.prod.exp u 6) b) ==>
     sw_scale_point r (r.prod.inv u) Q IN sw_points r a b` by
    metis_tac[sw_scale_points, sw_scale_inverse_power] >>
  simp_tac bool_ss [GroupIso_def, sw_group_carrier] >>
  conj_tac >- metis_tac[sw_scale_group_homo] >>
  simp_tac bool_ss [BIJ_DEF, INJ_DEF, SURJ_DEF] >>
  rpt conj_tac >- metis_tac[sw_scale_points] >-
    metis_tac[sw_scale_inverse] >- metis_tac[sw_scale_points] >>
  rpt strip_tac >>
  rename1 `Q IN sw_points r (r.prod.op (r.prod.exp u 4) a)
    (r.prod.op (r.prod.exp u 6) b)` >>
  qexists_tac `sw_scale_point r (r.prod.inv u) Q` >>
  metis_tac[sw_scale_inverse]
QED

Theorem sw_scale_scalar:
  ShortWeierstrassCurve (r:'a field) a b /\
  u IN r.carrier /\ u <> r.sum.id /\ P IN sw_points r a b ==>
  sw_scale_point r u ((sw_group r a b).exp P n) =
  (sw_group r (r.prod.op (r.prod.exp u 4) a)
    (r.prod.op (r.prod.exp u 6) b)).exp (sw_scale_point r u P) n
Proof
  metis_tac[sw_curve_homo_scalar, sw_scale_curve, sw_scale_group_homo]
QED

Theorem sw_scale_order:
  ShortWeierstrassCurve (r:'a field) a b /\
  u IN r.carrier /\ u <> r.sum.id /\ P IN sw_points r a b ==>
  order (sw_group r (r.prod.op (r.prod.exp u 4) a)
    (r.prod.op (r.prod.exp u 6) b)) (sw_scale_point r u P) =
  order (sw_group r a b) P
Proof
  metis_tac[sw_curve_iso_order, sw_scale_curve, sw_scale_group_iso]
QED

Theorem sw_scale_torsion:
  ShortWeierstrassCurve (r:'a field) a b /\
  u IN r.carrier /\ u <> r.sum.id ==>
  GroupIso (sw_scale_point r u) (sw_torsion_group r a b n)
    (sw_torsion_group r (r.prod.op (r.prod.exp u 4) a)
      (r.prod.op (r.prod.exp u 6) b) n)
Proof
  metis_tac[sw_curve_iso_torsion, sw_scale_curve, sw_scale_group_iso]
QED
