(* ------------------------------------------------------------------------- *)
(* Cube-Root Coordinate Endomorphism                                         *)
(* ------------------------------------------------------------------------- *)
(*
   Documentation

   sw_cm_map_def fixes infinity and sends (x,y) to (beta*x,y).
   On a short-Weierstrass curve with a = 0, beta in the field carrier and
   beta^3 = 1 give a curve-group endomorphism and an isomorphism.
   beta need not be a primitive cube root: beta = 1 is allowed.

   Main results:
     sw_cm_map_on_curve, sw_cm_map_points, sw_cm_map_add.
     sw_cm_map_third          Three applications give the original point.
     sw_cm_map_group_homo, sw_cm_map_group_endo, sw_cm_map_group_iso.
     sw_cm_map_scalar         Compatibility with scalar multiplication.

*)

Theory ellipticCMMap
Ancestors
  ellipticMorphisms ringLib
  shortWeierstrass shortWeierstrassGroup ellipticTorsion
Libs
  ringLib

open fieldTheory ringTheory groupTheory pred_setTheory ringLibTheory

Definition sw_cm_map_def:
  (sw_cm_map (r:'a field) beta ECInfinity = ECInfinity) /\
  (sw_cm_map r beta (ECAffine x y) = ECAffine (r.prod.op beta x) y)
End

(* Polynomial identities live in the existing ring model; the coordinate
   proofs below use sw_ring_ops rather than a second field hierarchy. *)
Overload "+"[local] = ``ring_add (s:'a Ring)``
Overload "-"[local] = ``ring_sub (s:'a Ring)``
Overload "*"[local] = ``ring_mul (s:'a Ring)``
Overload "**"[local] = ``ring_pow (s:'a Ring)``

Theorem sw_cm_cube_algebra[local]:
  !(s:'a Ring) beta x.
  beta IN ring_carrier s /\ x IN ring_carrier s /\
  beta ** 3 = ring_1 s ==>
  (beta * x) ** 3 = x ** 3 /\ beta * (beta * (beta * x)) = x
Proof
  ringLib.RING_TAC
QED

Theorem sw_cm_tangent_algebra[local]:
  !(s:'a Ring) beta x di.
  beta IN ring_carrier s /\ x IN ring_carrier s /\
  di IN ring_carrier s ==>
  (ring_of_num s 3 * (beta * x) ** 2 + ring_0 s) * di =
    beta ** 2 * ((ring_of_num s 3 * x ** 2 + ring_0 s) * di)
Proof
  ringLib.RING_TAC
QED

Theorem sw_cm_secant_algebra[local]:
  !(s:'a Ring) beta x1 x2 y1 y2 di ei.
  EVERY (\x. x IN ring_carrier s) [beta; x1; x2; y1; y2; di; ei] /\
  beta ** 3 = ring_1 s /\
  (x2 - x1) * di = ring_1 s /\
  (beta * x2 - beta * x1) * ei = ring_1 s ==>
  (y2 - y1) * ei = beta ** 2 * ((y2 - y1) * di)
Proof
  simp[listTheory.EVERY_DEF] >> ringLib.RING_TAC
QED

Theorem sw_cm_coordinates_algebra[local]:
  !(s:'a Ring) beta x1 x2 y1 m.
  EVERY (\x. x IN ring_carrier s) [beta; x1; x2; y1; m] /\
  beta ** 3 = ring_1 s ==>
  let z = m ** 2 - x1 - x2;
      n = beta ** 2 * m;
      w = n ** 2 - beta * x1 - beta * x2
  in w = beta * z /\
     n * (beta * x1 - w) - y1 = m * (x1 - z) - y1
Proof
  simp[listTheory.EVERY_DEF, LET_THM] >> ringLib.RING_TAC
QED

Theorem sw_cm_beta_nonzero[local]:
  Field (r:'a field) /\ beta IN r.carrier /\
  r.prod.exp beta 3 = r.prod.id ==> beta <> r.sum.id
Proof
  metis_tac[field_exp_eq_zero, field_one_ne_zero, DECIDE ``(3:num) <> 0``]
QED

Theorem sw_cm_scale_eq[local]:
  Field (r:'a field) /\ beta IN r.carrier /\
  r.prod.exp beta 3 = r.prod.id /\
  x IN r.carrier /\ y IN r.carrier ==>
  (r.prod.op beta x = r.prod.op beta y <=> x = y)
Proof
  metis_tac[sw_cm_beta_nonzero, field_nonzero_eq, field_mult_lcancel]
QED

Theorem sw_cm_map_on_curve:
  ShortWeierstrassCurve (r:'a field) r.sum.id b /\
  beta IN r.carrier /\ r.prod.exp beta 3 = r.prod.id /\
  sw_on_curve r r.sum.id b P ==>
  sw_on_curve r r.sum.id b (sw_cm_map r beta P)
Proof
  Cases_on `P` >- simp[sw_cm_map_def] >>
  rename1 `ECAffine x y` >> strip_tac >>
  `Field r /\ b IN r.carrier /\ x IN r.carrier /\ y IN r.carrier` by
    metis_tac[ShortWeierstrassCurve_def, sw_on_curve_def] >>
  `r.prod.exp (r.prod.op beta x) 3 = r.prod.exp x 3` by
    (mp_tac (Q.SPECL [`toRing r`, `beta`, `x`] sw_cm_cube_algebra) >>
     ASM_SIMP_TAC bool_ss [sw_ring_ops]) >>
  fs[sw_cm_map_def, sw_on_curve_def, sw_curve_rhs_def,
     field_mult_element, field_mult_lzero, field_add_rzero]
QED

Theorem sw_cm_map_points:
  ShortWeierstrassCurve (r:'a field) r.sum.id b /\
  beta IN r.carrier /\ r.prod.exp beta 3 = r.prod.id /\
  P IN sw_points r r.sum.id b ==>
  sw_cm_map r beta P IN sw_points r r.sum.id b
Proof
  metis_tac[sw_points_member, sw_cm_map_on_curve]
QED

Theorem sw_cm_map_third:
  Field (r:'a field) /\ beta IN r.carrier /\
  r.prod.exp beta 3 = r.prod.id /\ P IN sw_points r a b ==>
  sw_cm_map r beta (sw_cm_map r beta (sw_cm_map r beta P)) = P
Proof
  Cases_on `P` >- simp[sw_cm_map_def] >>
  rename1 `ECAffine x y` >> strip_tac >>
  `x IN r.carrier` by metis_tac[sw_points_member, sw_on_curve_def] >>
  simp_tac bool_ss [sw_cm_map_def, sw_point_11] >>
  mp_tac (Q.SPECL [`toRing r`, `beta`, `x`] sw_cm_cube_algebra) >>
  ASM_SIMP_TAC bool_ss [sw_ring_ops]
QED

Theorem sw_cm_slope[local]:
  ShortWeierstrassCurve (r:'a field) r.sum.id b /\
  beta IN r.carrier /\ r.prod.exp beta 3 = r.prod.id /\
  sw_on_curve r r.sum.id b (ECAffine x1 y1) /\
  sw_on_curve r r.sum.id b (ECAffine x2 y2) /\
  ~(x1 = x2 /\ y1 = r.sum.inv y2) ==>
  sw_slope r r.sum.id x1 y1 x2 y2 IN r.carrier /\
  sw_slope r r.sum.id (r.prod.op beta x1) y1 (r.prod.op beta x2) y2 =
    r.prod.op (r.prod.exp beta 2) (sw_slope r r.sum.id x1 y1 x2 y2)
Proof
  strip_tac >>
  `Field r /\ x1 IN r.carrier /\ y1 IN r.carrier /\
   x2 IN r.carrier /\ y2 IN r.carrier` by
    metis_tac[ShortWeierstrassCurve_def, sw_on_curve_def] >>
  `(r.prod.op beta x1 = r.prod.op beta x2) <=> x1 = x2` by
    metis_tac[sw_cm_scale_eq] >>
  Cases_on `x1 = x2` >| [
    `y2 = y1` by
      metis_tac[sw_same_x_on_curve, field_neg_neg, sw_on_curve_def] >>
    `r.prod.op (r.sum.exp r.prod.id 2) y1 IN r.carrier /\
     r.prod.op (r.sum.exp r.prod.id 2) y1 <> r.sum.id` by
      (conj_tac >- metis_tac[field_num_element, field_mult_element] >>
       `r.prod.op (r.sum.exp r.prod.id 2) y1 = r.sum.op y1 y1` by
         rw[field_num_2, field_mult_ladd, field_mult_lone] >>
       metis_tac[field_add_eq_zero]) >>
    drule_all sw_field_prod_inv >> strip_tac >>
    conj_tac >-
      ASM_SIMP_TAC bool_ss [sw_slope_def, field_mult_element,
        field_add_element, field_num_element, field_exp_element,
        field_zero_element] >>
    ASM_SIMP_TAC bool_ss [sw_slope_def] >>
    mp_tac (Q.SPECL [`toRing r`, `beta`, `x1`,
      `r.prod.inv (r.prod.op (r.sum.exp r.prod.id 2) y1)`]
      sw_cm_tangent_algebra) >>
    ASM_SIMP_TAC bool_ss [sw_ring_ops],
    `r.sum.op x2 (r.sum.inv x1) IN r.carrier /\
     r.sum.op x2 (r.sum.inv x1) <> r.sum.id` by
      metis_tac[field_add_element, field_neg_element,
                field_add_eq_zero, field_neg_neg] >>
    `r.prod.op beta x1 IN r.carrier /\ r.prod.op beta x2 IN r.carrier` by
      metis_tac[field_mult_element] >>
    `r.sum.op (r.prod.op beta x2) (r.sum.inv (r.prod.op beta x1))
       IN r.carrier /\
     r.sum.op (r.prod.op beta x2) (r.sum.inv (r.prod.op beta x1)) <>
       r.sum.id` by
      metis_tac[field_add_element, field_neg_element,
                field_add_eq_zero, field_neg_neg] >>
    `r.prod.inv (r.sum.op x2 (r.sum.inv x1)) IN r.carrier /\
     r.prod.op (r.sum.op x2 (r.sum.inv x1))
       (r.prod.inv (r.sum.op x2 (r.sum.inv x1))) = r.prod.id` by
      metis_tac[sw_field_prod_inv] >>
    `r.prod.inv (r.sum.op (r.prod.op beta x2)
       (r.sum.inv (r.prod.op beta x1))) IN r.carrier /\
     r.prod.op (r.sum.op (r.prod.op beta x2)
       (r.sum.inv (r.prod.op beta x1)))
       (r.prod.inv (r.sum.op (r.prod.op beta x2)
         (r.sum.inv (r.prod.op beta x1)))) = r.prod.id` by
      metis_tac[sw_field_prod_inv] >>
    conj_tac >-
      ASM_SIMP_TAC bool_ss [sw_slope_def, field_mult_element,
                            field_add_element, field_neg_element] >>
    ASM_SIMP_TAC bool_ss [sw_slope_def] >>
    mp_tac (Q.SPECL [`toRing r`, `beta`, `x1`, `x2`, `y1`, `y2`,
      `r.prod.inv (r.sum.op x2 (r.sum.inv x1))`,
      `r.prod.inv (r.sum.op (r.prod.op beta x2)
        (r.sum.inv (r.prod.op beta x1)))`] sw_cm_secant_algebra) >>
    ASM_SIMP_TAC bool_ss [listTheory.EVERY_DEF, ring_sub, sw_ring_ops]
  ]
QED

Theorem sw_cm_map_add:
  ShortWeierstrassCurve (r:'a field) r.sum.id b /\
  beta IN r.carrier /\ r.prod.exp beta 3 = r.prod.id /\
  P IN sw_points r r.sum.id b /\ Q IN sw_points r r.sum.id b ==>
  sw_cm_map r beta (sw_add r r.sum.id b P Q) =
    sw_add r r.sum.id b (sw_cm_map r beta P) (sw_cm_map r beta Q)
Proof
  Cases_on `P` >- simp[sw_cm_map_def, sw_add_def] >>
  Cases_on `Q` >- simp[sw_cm_map_def, sw_add_def] >>
  rename1 `sw_add r r.sum.id b (ECAffine x1 y1) (ECAffine x2 y2)` >>
  strip_tac >>
  `Field r /\ x1 IN r.carrier /\ y1 IN r.carrier /\
   x2 IN r.carrier /\ y2 IN r.carrier` by
    metis_tac[ShortWeierstrassCurve_def, sw_points_member, sw_on_curve_def] >>
  `(r.prod.op beta x1 = r.prod.op beta x2) <=> x1 = x2` by
    metis_tac[sw_cm_scale_eq] >>
  Cases_on `x1 = x2 /\ y1 = r.sum.inv y2` >-
    ASM_SIMP_TAC bool_ss [sw_cm_map_def, sw_add_def] >>
  `sw_slope r r.sum.id x1 y1 x2 y2 IN r.carrier /\
   sw_slope r r.sum.id (r.prod.op beta x1) y1 (r.prod.op beta x2) y2 =
     r.prod.op (r.prod.exp beta 2) (sw_slope r r.sum.id x1 y1 x2 y2)` by
    metis_tac[sw_cm_slope, sw_points_member] >>
  `sw_add_x r
      (r.prod.op (r.prod.exp beta 2) (sw_slope r r.sum.id x1 y1 x2 y2))
      (r.prod.op beta x1) (r.prod.op beta x2) =
     r.prod.op beta (sw_add_x r (sw_slope r r.sum.id x1 y1 x2 y2) x1 x2) /\
   sw_add_y r
      (r.prod.op (r.prod.exp beta 2) (sw_slope r r.sum.id x1 y1 x2 y2))
      (r.prod.op beta x1) y1
      (sw_add_x r
        (r.prod.op (r.prod.exp beta 2) (sw_slope r r.sum.id x1 y1 x2 y2))
        (r.prod.op beta x1) (r.prod.op beta x2)) =
     sw_add_y r (sw_slope r r.sum.id x1 y1 x2 y2) x1 y1
       (sw_add_x r (sw_slope r r.sum.id x1 y1 x2 y2) x1 x2)` by
    (mp_tac (Q.SPECL [`toRing r`, `beta`, `x1`, `x2`, `y1`,
      `sw_slope r r.sum.id x1 y1 x2 y2`] sw_cm_coordinates_algebra) >>
     ASM_SIMP_TAC bool_ss [listTheory.EVERY_DEF, LET_THM, ring_sub,
                          sw_ring_ops, sw_add_x_def, sw_add_y_def] >>
     metis_tac[]) >>
  ASM_SIMP_TAC bool_ss [sw_add_def, sw_cm_map_def, LET_THM] >>
  metis_tac[]
QED

Theorem sw_cm_map_group_homo:
  ShortWeierstrassCurve (r:'a field) r.sum.id b /\
  beta IN r.carrier /\ r.prod.exp beta 3 = r.prod.id ==>
  GroupHomo (sw_cm_map r beta) (sw_group r r.sum.id b) (sw_group r r.sum.id b)
Proof
  strip_tac >>
  simp_tac bool_ss [GroupHomo_def, sw_group_carrier, sw_group_op] >>
  metis_tac[sw_cm_map_points, sw_cm_map_add]
QED

Theorem sw_cm_map_group_endo:
  ShortWeierstrassCurve (r:'a field) r.sum.id b /\
  beta IN r.carrier /\ r.prod.exp beta 3 = r.prod.id ==>
  GroupEndo (sw_cm_map r beta) (sw_group r r.sum.id b)
Proof
  metis_tac[GroupEndo_def, sw_cm_map_group_homo]
QED

Theorem sw_cm_map_group_iso:
  ShortWeierstrassCurve (r:'a field) r.sum.id b /\
  beta IN r.carrier /\ r.prod.exp beta 3 = r.prod.id ==>
  GroupIso (sw_cm_map r beta) (sw_group r r.sum.id b) (sw_group r r.sum.id b)
Proof
  strip_tac >>
  `Field r` by metis_tac[ShortWeierstrassCurve_def] >>
  simp_tac bool_ss [GroupIso_def, sw_group_carrier] >>
  conj_tac >- metis_tac[sw_cm_map_group_homo] >>
  simp_tac bool_ss [BIJ_DEF, INJ_DEF, SURJ_DEF] >>
  rpt conj_tac >- metis_tac[sw_cm_map_points] >-
    metis_tac[sw_cm_map_third] >- metis_tac[sw_cm_map_points] >>
  rpt strip_tac >>
  rename1 `Q IN sw_points r r.sum.id b` >>
  qexists_tac `sw_cm_map r beta (sw_cm_map r beta Q)` >>
  metis_tac[sw_cm_map_points, sw_cm_map_third]
QED

Theorem sw_cm_map_scalar:
  ShortWeierstrassCurve (r:'a field) r.sum.id b /\
  beta IN r.carrier /\ r.prod.exp beta 3 = r.prod.id /\
  P IN sw_points r r.sum.id b ==>
  sw_cm_map r beta ((sw_group r r.sum.id b).exp P n) =
    (sw_group r r.sum.id b).exp (sw_cm_map r beta P) n
Proof
  metis_tac[sw_curve_endo_scalar, sw_cm_map_group_endo]
QED
