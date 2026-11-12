(* ------------------------------------------------------------------------- *)
(* The Short-Weierstrass Group Law                                           *)
(* ------------------------------------------------------------------------- *)
(*
   Documentation

   Chord-and-tangent addition on sw_point, packaged as an existing HOL group
   record, not a separate elliptic-curve algebra hierarchy.

   Definitions:
     sw_neg_def       Negate the y-coordinate; fix ECInfinity.
     sw_slope_def     Tangent or secant slope using field inverses.
     sw_add_x_def, sw_add_y_def, sw_add_def
                      Coordinate formulas, with infinity and inverse cases.
     sw_group_def     Carrier sw_points, identity ECInfinity, operation sw_add.

   Main results:
     short_weierstrass_group, short_weierstrass_abelian_group
                      ShortWeierstrassCurve r a b implies a (commutative) group.
     short_weierstrass_finite_group
                      FiniteField additionally gives FiniteAbelianGroup.
     sw_group_carrier, sw_group_id, sw_group_op, sw_group_inv
                      Connect record operations to the curve interface.
     sw_ring_ops, sw_field_prod_inv, sw_field_prod_inv_eq
                      Bridges used by coordinate and certificate proofs.

   Definitions are total; group laws and inverse facts require the curve and
   point-membership hypotheses in their statements. Scalar multiplication
   uses the existing group exponent (sw_group r a b).exp.
*)

Theory shortWeierstrassGroup
Ancestors
  shortWeierstrass
  ringLib
  swAssocAlgebra
Libs
  ringLib

open fieldTheory ringTheory ringLibTheory

Theorem sw_ring_model[local]:
  Field (r:'a field) ==> fromRing (toRing r) = r
Proof
  rw[from_toRing, field_is_ring]
QED

Theorem sw_ring_ops:
  Field (r:'a field) ==>
  (ring_carrier (toRing r) = r.carrier) /\
  (ring_0 (toRing r) = r.sum.id) /\
  (ring_1 (toRing r) = r.prod.id) /\
  (!x. ring_neg (toRing r) x = r.sum.inv x) /\
  (!x y. ring_add (toRing r) x y = r.sum.op x y) /\
  (!x y. ring_mul (toRing r) x y = r.prod.op x y) /\
  (!x n. ring_pow (toRing r) x n = r.prod.exp x n) /\
  (!n. ring_of_num (toRing r) n = r.sum.exp r.prod.id n)
Proof
  rw[ring_carrier_def, ring_0_def, ring_1_def, ring_neg_def,
     ring_add_def, ring_mul_def, ring_pow_def,
     ring_of_num_def, sw_ring_model]
QED

Theorem sw_toRing_carrier[local]:
  Field (r:'a field) ==> ring_carrier (toRing r) = r.carrier
Proof
  metis_tac[sw_ring_ops]
QED

Theorem sw_toRing_zero[local]:
  Field (r:'a field) ==> ring_0 (toRing r) = r.sum.id
Proof
  metis_tac[sw_ring_ops]
QED

Theorem sw_toRing_one[local]:
  Field (r:'a field) ==> ring_1 (toRing r) = r.prod.id
Proof
  metis_tac[sw_ring_ops]
QED

Theorem sw_toRing_neg[local]:
  Field (r:'a field) ==>
  !x. ring_neg (toRing r) x = r.sum.inv x
Proof
  metis_tac[sw_ring_ops]
QED

Theorem sw_toRing_add[local]:
  Field (r:'a field) ==>
  !x y. ring_add (toRing r) x y = r.sum.op x y
Proof
  metis_tac[sw_ring_ops]
QED

Theorem sw_toRing_mul[local]:
  Field (r:'a field) ==>
  !x y. ring_mul (toRing r) x y = r.prod.op x y
Proof
  metis_tac[sw_ring_ops]
QED

Theorem sw_toRing_pow[local]:
  Field (r:'a field) ==>
  !x n. ring_pow (toRing r) x n = r.prod.exp x n
Proof
  metis_tac[sw_ring_ops]
QED

Theorem sw_toRing_of_num[local]:
  Field (r:'a field) ==>
  !n. ring_of_num (toRing r) n = r.sum.exp r.prod.id n
Proof
  metis_tac[sw_ring_ops]
QED

Theorem sw_field_prod_inv:
  !(r:'a field) d.
  Field r /\ d IN r.carrier /\ d <> r.sum.id ==>
  r.prod.inv d IN r.carrier /\
  r.prod.op d (r.prod.inv d) = r.prod.id
Proof
  rpt strip_tac >>
  `d IN R+` by rw[field_nonzero_eq] >>
  `d IN monoid_invertibles r.prod` by
    metis_tac[field_nonzero_unit, monoidTheory.Invertibles_carrier] >>
  metis_tac[field_mult_monoid, monoidTheory.monoid_inv_def]
QED

Theorem sw_field_prod_inv_eq:
  Field (r:'a field) /\ d IN r.carrier /\ d <> r.sum.id ==>
  r.prod.inv d = (Invertibles r.prod).inv d
Proof
  rpt strip_tac >>
  `d IN R+` by rw[field_nonzero_eq] >>
  `d IN (Invertibles r.prod).carrier` by
    metis_tac[field_nonzero_unit] >>
  metis_tac[sw_field_prod_inv, field_is_ring, ring_unit_rinv_unique]
QED

Theorem sw_secant_comm_algebra[local]:
  !(r:'a Ring) x1 y1 x2 y2 di12 di21.
  x1 IN ring_carrier r /\
  y1 IN ring_carrier r /\
  x2 IN ring_carrier r /\
  y2 IN ring_carrier r /\
  di12 IN ring_carrier r /\
  di21 IN ring_carrier r /\
  ring_mul r (ring_add r x2 (ring_neg r x1)) di12 = ring_1 r /\
  ring_mul r (ring_add r x1 (ring_neg r x2)) di21 = ring_1 r ==>
  let m12 = ring_mul r (ring_add r y2 (ring_neg r y1)) di12;
      m21 = ring_mul r (ring_add r y1 (ring_neg r y2)) di21;
      x12 = ring_add r
        (ring_add r (ring_pow r m12 2) (ring_neg r x1)) (ring_neg r x2);
      x21 = ring_add r
        (ring_add r (ring_pow r m21 2) (ring_neg r x2)) (ring_neg r x1);
      y12 = ring_add r
        (ring_mul r m12 (ring_add r x1 (ring_neg r x12)))
        (ring_neg r y1);
      y21 = ring_add r
        (ring_mul r m21 (ring_add r x2 (ring_neg r x21)))
        (ring_neg r y2)
  in
    x12 = x21 /\ y12 = y21
Proof
  simp[LET_THM] >>
  ringLib.RING_TAC
QED

Theorem sw_tangent_neg_algebra[local]:
  !(r:'a Ring) x y a di dni.
  x IN ring_carrier r /\
  y IN ring_carrier r /\
  a IN ring_carrier r /\
  di IN ring_carrier r /\
  dni IN ring_carrier r /\
  ring_mul r (ring_mul r (ring_of_num r 2) y) di = ring_1 r /\
  ring_mul r (ring_mul r (ring_of_num r 2) (ring_neg r y)) dni =
    ring_1 r ==>
  let n = ring_add r
        (ring_mul r (ring_of_num r 3) (ring_pow r x 2)) a;
      m = ring_mul r n di;
      mn = ring_mul r n dni;
      x3 = ring_add r
        (ring_add r (ring_pow r m 2) (ring_neg r x)) (ring_neg r x);
      xn = ring_add r
        (ring_add r (ring_pow r mn 2) (ring_neg r x)) (ring_neg r x);
      y3 = ring_add r
        (ring_mul r m (ring_add r x (ring_neg r x3))) (ring_neg r y);
      yn = ring_add r
        (ring_mul r mn (ring_add r x (ring_neg r xn)))
        (ring_neg r (ring_neg r y))
  in
    xn = x3 /\ yn = ring_neg r y3
Proof
  simp[LET_THM] >>
  ringLib.RING_TAC
QED

Theorem sw_secant_neg_algebra[local]:
  !(r:'a Ring) x1 y1 x2 y2 di.
  x1 IN ring_carrier r /\
  y1 IN ring_carrier r /\
  x2 IN ring_carrier r /\
  y2 IN ring_carrier r /\
  di IN ring_carrier r ==>
  let m = ring_mul r (ring_add r y2 (ring_neg r y1)) di;
      mn = ring_mul r
        (ring_add r (ring_neg r y2) (ring_neg r (ring_neg r y1))) di;
      x3 = ring_add r
        (ring_add r (ring_pow r m 2) (ring_neg r x1)) (ring_neg r x2);
      xn = ring_add r
        (ring_add r (ring_pow r mn 2) (ring_neg r x1)) (ring_neg r x2);
      y3 = ring_add r
        (ring_mul r m (ring_add r x1 (ring_neg r x3)))
        (ring_neg r y1);
      yn = ring_add r
        (ring_mul r mn (ring_add r x1 (ring_neg r xn)))
        (ring_neg r (ring_neg r y1))
  in
    xn = x3 /\ yn = ring_neg r y3
Proof
  simp[LET_THM] >>
  ringLib.RING_TAC
QED



Theorem sw_square_factor[local]:
  x IN ring_carrier (r:'a Ring) /\
  y IN ring_carrier r /\
  ring_pow r x 2 = ring_pow r y 2 ==>
  ring_mul r (ring_add r y (ring_neg r x)) (ring_add r y x) =
  ring_0 r
Proof
  ringLib.RING_TAC
QED

Theorem sw_secant_closure_algebra[local]:
  !(r:'a Ring) x1 y1 x2 y2 a b di.
  x1 IN ring_carrier r /\
  y1 IN ring_carrier r /\
  x2 IN ring_carrier r /\
  y2 IN ring_carrier r /\
  a IN ring_carrier r /\
  b IN ring_carrier r /\
  di IN ring_carrier r /\
  ring_pow r y1 2 =
    ring_add r (ring_add r (ring_pow r x1 3) (ring_mul r a x1)) b /\
  ring_pow r y2 2 =
    ring_add r (ring_add r (ring_pow r x2 3) (ring_mul r a x2)) b /\
  ring_mul r (ring_add r x2 (ring_neg r x1)) di = ring_1 r ==>
  let m = ring_mul r (ring_add r y2 (ring_neg r y1)) di;
      x3 = ring_add r
        (ring_add r (ring_pow r m 2) (ring_neg r x1)) (ring_neg r x2);
      y3 = ring_add r
        (ring_mul r m (ring_add r x1 (ring_neg r x3))) (ring_neg r y1)
  in
    ring_pow r y3 2 =
    ring_add r (ring_add r (ring_pow r x3 3) (ring_mul r a x3)) b
Proof
  simp[LET_THM] >>
  ringLib.RING_TAC
QED

Theorem sw_tangent_closure_algebra[local]:
  !(r:'a Ring) x y a b di.
  x IN ring_carrier r /\
  y IN ring_carrier r /\
  a IN ring_carrier r /\
  b IN ring_carrier r /\
  di IN ring_carrier r /\
  ring_pow r y 2 =
    ring_add r (ring_add r (ring_pow r x 3) (ring_mul r a x)) b /\
  ring_mul r (ring_mul r (ring_of_num r 2) y) di = ring_1 r ==>
  let m = ring_mul r
    (ring_add r (ring_mul r (ring_of_num r 3) (ring_pow r x 2)) a) di;
      x3 = ring_add r
        (ring_add r (ring_pow r m 2) (ring_neg r x)) (ring_neg r x);
      y3 = ring_add r
        (ring_mul r m (ring_add r x (ring_neg r x3))) (ring_neg r y)
  in
    ring_pow r y3 2 =
    ring_add r (ring_add r (ring_pow r x3 3) (ring_mul r a x3)) b
Proof
  simp[LET_THM] >>
  ringLib.RING_TAC
QED



Definition sw_neg_def:
  (sw_neg (r:'a field) ECInfinity = ECInfinity) /\
  (sw_neg r (ECAffine x y) = ECAffine x (r.sum.inv y))
End

Definition sw_slope_def:
  sw_slope (r:'a field) a x1 y1 x2 y2 =
    if x1 = x2 then
      r.prod.op
        (r.sum.op
          (r.prod.op (r.sum.exp r.prod.id 3) (r.prod.exp x1 2)) a)
        (r.prod.inv (r.prod.op (r.sum.exp r.prod.id 2) y1))
    else
      r.prod.op (r.sum.op y2 (r.sum.inv y1))
        (r.prod.inv (r.sum.op x2 (r.sum.inv x1)))
End

Definition sw_add_x_def:
  sw_add_x (r:'a field) m x1 x2 =
    r.sum.op
      (r.sum.op (r.prod.exp m 2) (r.sum.inv x1))
      (r.sum.inv x2)
End

Definition sw_add_y_def:
  sw_add_y (r:'a field) m x1 y1 x3 =
    r.sum.op
      (r.prod.op m (r.sum.op x1 (r.sum.inv x3)))
      (r.sum.inv y1)
End

Definition sw_add_def:
  (sw_add (r:'a field) a b ECInfinity Q = Q) /\
  (sw_add r a b (ECAffine x y) ECInfinity = ECAffine x y) /\
  (sw_add r a b (ECAffine x1 y1) (ECAffine x2 y2) =
    if x1 = x2 /\ y1 = r.sum.inv y2 then ECInfinity
    else
      let m = sw_slope r a x1 y1 x2 y2;
          x3 = sw_add_x r m x1 x2
      in
        ECAffine x3 (sw_add_y r m x1 y1 x3))
End

Definition sw_group_def:
  sw_group (r:'a field) a b : 'a sw_point group =
    <| carrier := sw_points r a b;
       id := ECInfinity;
       op := sw_add r a b |>
End

Theorem sw_neg_infinity[simp]:
  sw_neg (r:'a field) ECInfinity = ECInfinity
Proof
  rw[sw_neg_def]
QED

Theorem sw_neg_affine[simp]:
  sw_neg (r:'a field) (ECAffine x y) = ECAffine x (r.sum.inv y)
Proof
  rw[sw_neg_def]
QED

Theorem sw_slope_tangent[simp]:
  sw_slope (r:'a field) a x y x y' =
    r.prod.op
      (r.sum.op
        (r.prod.op (r.sum.exp r.prod.id 3) (r.prod.exp x 2)) a)
      (r.prod.inv (r.prod.op (r.sum.exp r.prod.id 2) y))
Proof
  rw[sw_slope_def]
QED

Theorem sw_slope_secant:
  x1 <> x2 ==>
  sw_slope (r:'a field) a x1 y1 x2 y2 =
    r.prod.op (r.sum.op y2 (r.sum.inv y1))
      (r.prod.inv (r.sum.op x2 (r.sum.inv x1)))
Proof
  rw[sw_slope_def]
QED

Theorem sw_add_l_infinity[simp]:
  sw_add (r:'a field) a b ECInfinity P = P
Proof
  Cases_on `P` >> rw[sw_add_def]
QED

Theorem sw_add_r_infinity[simp]:
  sw_add (r:'a field) a b P ECInfinity = P
Proof
  Cases_on `P` >> rw[sw_add_def]
QED

Theorem sw_add_affine_vertical[simp]:
  y1 = r.sum.inv y2 ==>
  sw_add (r:'a field) a b (ECAffine x y1) (ECAffine x y2) = ECInfinity
Proof
  rw[sw_add_def]
QED

Theorem sw_add_affine_nonvertical:
  ~(x1 = x2 /\ y1 = r.sum.inv y2) ==>
  sw_add (r:'a field) a b (ECAffine x1 y1) (ECAffine x2 y2) =
    let m = sw_slope r a x1 y1 x2 y2;
        x3 = sw_add_x r m x1 x2
    in
      ECAffine x3 (sw_add_y r m x1 y1 x3)
Proof
  rw[sw_add_def]
QED

Theorem sw_group_carrier[simp]:
  (sw_group (r:'a field) a b).carrier = sw_points r a b
Proof
  rw[sw_group_def]
QED

Theorem sw_group_id[simp]:
  (sw_group (r:'a field) a b).id = ECInfinity
Proof
  rw[sw_group_def]
QED

Theorem sw_group_op[simp]:
  (sw_group (r:'a field) a b).op = sw_add r a b
Proof
  rw[sw_group_def]
QED

Theorem sw_infinity_mem[simp]:
  ECInfinity IN sw_points (r:'a field) a b
Proof
  rw[]
QED

Theorem sw_affine_mem[simp]:
  ECAffine x y IN sw_points (r:'a field) a b <=>
  x IN r.carrier /\ y IN r.carrier /\
  r.prod.exp y 2 = sw_curve_rhs r a b x
Proof
  rw[]
QED

Theorem sw_neg_affine_on_curve:
  ShortWeierstrassCurve (r:'a field) a b /\
  sw_on_curve r a b (ECAffine x y) ==>
  sw_on_curve r a b (sw_neg r (ECAffine x y))
Proof
  rw[ShortWeierstrassCurve_def, sw_on_curve_def, sw_neg_def] >>
  metis_tac[field_is_ring, ring_neg_element, ring_neg_square]
QED

Theorem sw_neg_on_curve:
  ShortWeierstrassCurve (r:'a field) a b /\ sw_on_curve r a b P ==>
  sw_on_curve r a b (sw_neg r P)
Proof
  Cases_on `P` >> rw[sw_neg_def] >>
  fs[ShortWeierstrassCurve_def] >>
  rw[ring_neg_square, field_is_ring]
QED

Theorem sw_neg_mem:
  ShortWeierstrassCurve (r:'a field) a b /\ P IN sw_points r a b ==>
  sw_neg r P IN sw_points r a b
Proof
  metis_tac[sw_points_member, sw_neg_on_curve]
QED

Theorem sw_neg_involutive:
  ShortWeierstrassCurve (r:'a field) a b /\ P IN sw_points r a b ==>
  sw_neg r (sw_neg r P) = P
Proof
  Cases_on `P` >>
  rw[sw_neg_def, sw_points_member, sw_on_curve_def,
     ShortWeierstrassCurve_def, field_neg_neg]
QED

Theorem sw_same_x_on_curve:
  ShortWeierstrassCurve (r:'a field) a b /\
  sw_on_curve r a b (ECAffine x y1) /\
  sw_on_curve r a b (ECAffine x y2) ==>
  y2 = y1 \/ y2 = r.sum.inv y1
Proof
  rpt strip_tac >>
  fs[ShortWeierstrassCurve_def, sw_on_curve_def] >>
  `r.prod.op (r.sum.op y2 (r.sum.inv y1)) (r.sum.op y2 y1) =
   r.sum.id` by
    metis_tac[sw_square_factor, sw_ring_ops] >>
  `r.sum.op y2 (r.sum.inv y1) IN r.carrier` by metis_tac [field_neg_element, field_add_element]  >>
  `r.sum.op y2 y1 IN r.carrier` by metis_tac [field_add_element]  >>
  `r.sum.op y2 (r.sum.inv y1) = r.sum.id \/
   r.sum.op y2 y1 = r.sum.id` by
    ( metis_tac [field_mult_eq_zero] ) >>
  metis_tac[field_add_eq_zero, field_neg_eq, field_neg_neg,
            field_neg_element]
QED

Theorem sw_add_same_x_distinct:
  ShortWeierstrassCurve (r:'a field) a b /\
  sw_on_curve r a b (ECAffine x y1) /\
  sw_on_curve r a b (ECAffine x y2) /\ y1 <> y2 ==>
  sw_add r a b (ECAffine x y1) (ECAffine x y2) = ECInfinity
Proof
  rpt strip_tac >>
  `y2 = r.sum.inv y1` by metis_tac[sw_same_x_on_curve] >>
  `y1 = r.sum.inv y2` by
    metis_tac[ShortWeierstrassCurve_def, sw_on_curve_ECAffine,
              field_neg_neg] >>
  rw[sw_add_def]
QED

Theorem sw_add_affine_double_on_curve[local]:
  ShortWeierstrassCurve (r:'a field) a b /\
  sw_on_curve r a b (ECAffine x y) /\ y <> r.sum.inv y ==>
  sw_on_curve r a b
    (sw_add r a b (ECAffine x y) (ECAffine x y))
Proof
  rpt strip_tac >>
  fs[ShortWeierstrassCurve_def, sw_on_curve_def] >>
  `r.prod.op (r.sum.exp r.prod.id 2) y IN r.carrier /\
   r.prod.op (r.sum.exp r.prod.id 2) y <> r.sum.id` by
    (conj_tac >-
       metis_tac[field_num_element, field_mult_element] >>
     `r.prod.op (r.sum.exp r.prod.id 2) y = r.sum.op y y` by
       rw[field_num_2, field_mult_ladd, field_mult_lone] >>
     metis_tac[field_add_eq_zero]) >>
  `r.prod.op (r.sum.exp r.prod.id 2) y IN R+` by
    rw[field_nonzero_eq] >>
  `r.prod.op (r.sum.exp r.prod.id 2) y IN
   monoid_invertibles r.prod` by
    metis_tac[field_nonzero_unit, monoidTheory.Invertibles_carrier] >>
  `r.prod.inv (r.prod.op (r.sum.exp r.prod.id 2) y) IN r.carrier /\
   r.prod.op (r.prod.op (r.sum.exp r.prod.id 2) y)
     (r.prod.inv (r.prod.op (r.sum.exp r.prod.id 2) y)) = r.prod.id` by
    metis_tac[field_mult_monoid, monoidTheory.monoid_inv_def] >>
  PURE_ASM_REWRITE_TAC [sw_add_def] >>
  ASM_SIMP_TAC bool_ss [] >>
  PURE_ASM_REWRITE_TAC
    [sw_on_curve_def, sw_add_x_def, sw_add_y_def, sw_slope_def, LET_THM] >>
  BETA_TAC >>
  PURE_REWRITE_TAC [sw_on_curve_def] >>
  rpt conj_tac >| [
    metis_tac[field_add_element, field_mult_element, field_exp_element,
              field_neg_element, field_num_element],
    metis_tac[field_add_element, field_mult_element, field_exp_element,
              field_neg_element, field_num_element],
    MP_TAC (Q.SPECL
      [`toRing r`, `x`, `y`, `a`, `b`,
       `r.prod.inv (r.prod.op (r.sum.exp r.prod.id 2) y)`]
      sw_tangent_closure_algebra) >>
    ASM_SIMP_TAC bool_ss [sw_ring_ops, LET_THM, sw_curve_rhs_def] >>
    FULL_SIMP_TAC bool_ss [sw_curve_rhs_def]
  ]
QED

Theorem sw_add_affine_same_x_on_curve[local]:
  ShortWeierstrassCurve (r:'a field) a b /\
  sw_on_curve r a b (ECAffine x y1) /\
  sw_on_curve r a b (ECAffine x y2) ==>
  sw_on_curve r a b
    (sw_add r a b (ECAffine x y1) (ECAffine x y2))
Proof
  rpt strip_tac >>
  `y2 = y1 \/ y2 = r.sum.inv y1` by
    metis_tac[sw_same_x_on_curve] >>
  Cases_on `y2 = y1` >-
    (gvs[] >>
     Cases_on `y1 = r.sum.inv y1` >-
       rw[sw_add_def] >>
     metis_tac[sw_add_affine_double_on_curve, sw_on_curve_def]) >>
  `y2 = r.sum.inv y1` by metis_tac[] >>
  `y1 = r.sum.inv y2` by
    metis_tac[ShortWeierstrassCurve_def, sw_on_curve_ECAffine,
              field_neg_neg] >>
  rw[sw_add_def]
QED


Theorem sw_add_affine_secant_on_curve[local]:
  ShortWeierstrassCurve (r:'a field) a b /\
  sw_on_curve r a b (ECAffine x1 y1) /\
  sw_on_curve r a b (ECAffine x2 y2) /\ x1 <> x2 ==>
  sw_on_curve r a b
    (sw_add r a b (ECAffine x1 y1) (ECAffine x2 y2))
Proof
  rpt strip_tac >>
  fs[ShortWeierstrassCurve_def, sw_on_curve_def] >>
  `r.sum.op x2 (r.sum.inv x1) IN r.carrier /\
   r.sum.op x2 (r.sum.inv x1) <> r.sum.id` by
    (conj_tac >-
       metis_tac[field_add_element, field_neg_element] >>
     spose_not_then strip_assume_tac >>
     `r.sum.inv x1 = r.sum.inv x2` by
       metis_tac[field_add_eq_zero, field_neg_element] >>
     metis_tac[field_neg_eq]) >>
  `r.sum.op x2 (r.sum.inv x1) IN R+` by
    rw[field_nonzero_eq] >>
  `r.sum.op x2 (r.sum.inv x1) IN monoid_invertibles r.prod` by
    metis_tac[field_nonzero_unit, monoidTheory.Invertibles_carrier] >>
  `r.prod.inv (r.sum.op x2 (r.sum.inv x1)) IN r.carrier /\
   r.prod.op (r.sum.op x2 (r.sum.inv x1))
     (r.prod.inv (r.sum.op x2 (r.sum.inv x1))) = r.prod.id` by
    metis_tac[field_mult_monoid, monoidTheory.monoid_inv_def] >>
  ASM_SIMP_TAC bool_ss [sw_add_def] >>
  ASM_SIMP_TAC bool_ss
    [sw_slope_def, sw_add_x_def, sw_add_y_def, sw_on_curve_def, LET_THM] >>
  rpt conj_tac >| [
    metis_tac[field_add_element, field_mult_element, field_exp_element,
              field_neg_element],
    metis_tac[field_add_element, field_mult_element, field_exp_element,
              field_neg_element],
    MP_TAC (Q.SPECL
      [`toRing r`, `x1`, `y1`, `x2`, `y2`, `a`, `b`,
       `r.prod.inv (r.sum.op x2 (r.sum.inv x1))`]
      sw_secant_closure_algebra) >>
    ASM_SIMP_TAC bool_ss
      [sw_toRing_carrier, sw_toRing_zero, sw_toRing_one,
       sw_toRing_neg, sw_toRing_add, sw_toRing_mul, sw_toRing_pow,
       LET_THM, sw_curve_rhs_def]
  ]
QED

Theorem sw_add_affine_on_curve:
  ShortWeierstrassCurve (r:'a field) a b /\
  sw_on_curve r a b (ECAffine x1 y1) /\
  sw_on_curve r a b (ECAffine x2 y2) ==>
  sw_on_curve r a b
    (sw_add r a b (ECAffine x1 y1) (ECAffine x2 y2))
Proof
  metis_tac[sw_add_affine_same_x_on_curve,
            sw_add_affine_secant_on_curve]
QED

Theorem sw_add_on_curve:
  ShortWeierstrassCurve (r:'a field) a b /\
  sw_on_curve r a b P /\ sw_on_curve r a b Q ==>
  sw_on_curve r a b (sw_add r a b P Q)
Proof
  Cases_on `P` >> Cases_on `Q` >| [
    rw[sw_add_def],
    rw[sw_add_def],
    rw[sw_add_def],
    metis_tac[sw_add_affine_on_curve]
  ]
QED

Theorem sw_add_mem:
  ShortWeierstrassCurve (r:'a field) a b /\
  P IN sw_points r a b /\ Q IN sw_points r a b ==>
  sw_add r a b P Q IN sw_points r a b
Proof
  metis_tac[sw_points_member, sw_add_on_curve]
QED

Theorem sw_add_affine_comm[local]:
  ShortWeierstrassCurve (r:'a field) a b /\
  sw_on_curve r a b (ECAffine x1 y1) /\
  sw_on_curve r a b (ECAffine x2 y2) ==>
  sw_add r a b (ECAffine x1 y1) (ECAffine x2 y2) =
  sw_add r a b (ECAffine x2 y2) (ECAffine x1 y1)
Proof
  rpt strip_tac >>
  Cases_on `x1 = x2` >-
    (Cases_on `y1 = y2` >-
       metis_tac[] >>
     `sw_add r a b (ECAffine x1 y1) (ECAffine x2 y2) =
      ECInfinity` by
       metis_tac[sw_add_same_x_distinct] >>
     `sw_add r a b (ECAffine x2 y2) (ECAffine x1 y1) =
      ECInfinity` by
       metis_tac[sw_add_same_x_distinct] >>
     rw[]) >>
  fs[ShortWeierstrassCurve_def, sw_on_curve_def] >>
  `r.sum.op x2 (r.sum.inv x1) IN r.carrier /\
   r.sum.op x2 (r.sum.inv x1) <> r.sum.id` by
    (conj_tac >-
       metis_tac[field_add_element, field_neg_element] >>
     spose_not_then strip_assume_tac >>
     `r.sum.inv x1 = r.sum.inv x2` by
       metis_tac[field_add_eq_zero, field_neg_element] >>
     metis_tac[field_neg_eq]) >>
  `r.sum.op x1 (r.sum.inv x2) IN r.carrier /\
   r.sum.op x1 (r.sum.inv x2) <> r.sum.id` by
    (conj_tac >-
       metis_tac[field_add_element, field_neg_element] >>
     spose_not_then strip_assume_tac >>
     `r.sum.inv x2 = r.sum.inv x1` by
       metis_tac[field_add_eq_zero, field_neg_element] >>
     metis_tac[field_neg_eq]) >>
  `r.prod.inv (r.sum.op x2 (r.sum.inv x1)) IN r.carrier /\
   r.prod.op (r.sum.op x2 (r.sum.inv x1))
     (r.prod.inv (r.sum.op x2 (r.sum.inv x1))) = r.prod.id` by
    metis_tac[sw_field_prod_inv] >>
  `r.prod.inv (r.sum.op x1 (r.sum.inv x2)) IN r.carrier /\
   r.prod.op (r.sum.op x1 (r.sum.inv x2))
     (r.prod.inv (r.sum.op x1 (r.sum.inv x2))) = r.prod.id` by
    metis_tac[sw_field_prod_inv] >>
  ASM_SIMP_TAC bool_ss
    [sw_add_def, sw_slope_def, sw_add_x_def, sw_add_y_def, LET_THM] >>
  MP_TAC (Q.SPECL
    [`toRing r`, `x1`, `y1`, `x2`, `y2`,
     `r.prod.inv (r.sum.op x2 (r.sum.inv x1))`,
     `r.prod.inv (r.sum.op x1 (r.sum.inv x2))`]
    sw_secant_comm_algebra) >>
  ASM_SIMP_TAC bool_ss
    [sw_toRing_carrier, sw_toRing_zero, sw_toRing_one,
     sw_toRing_neg, sw_toRing_add, sw_toRing_mul, sw_toRing_pow,
     LET_THM] >>
  metis_tac[]
QED

Theorem sw_add_comm:
  ShortWeierstrassCurve (r:'a field) a b /\
  P IN sw_points r a b /\ Q IN sw_points r a b ==>
  sw_add r a b P Q = sw_add r a b Q P
Proof
  Cases_on `P` >> Cases_on `Q` >| [
    rw[sw_add_def],
    rw[sw_add_def],
    rw[sw_add_def],
    metis_tac[sw_points_member, sw_add_affine_comm]
  ]
QED

Theorem sw_add_neg_l:
  ShortWeierstrassCurve (r:'a field) a b /\ P IN sw_points r a b ==>
  sw_add r a b (sw_neg r P) P = ECInfinity
Proof
  Cases_on `P` >-
    rw[] >>
  rw[sw_neg_def, sw_add_def, sw_points_member, sw_on_curve_def,
     ShortWeierstrassCurve_def, field_neg_neg]
QED

Theorem sw_add_neg_r:
  ShortWeierstrassCurve (r:'a field) a b /\ P IN sw_points r a b ==>
  sw_add r a b P (sw_neg r P) = ECInfinity
Proof
  metis_tac[sw_neg_mem, sw_add_comm, sw_add_neg_l]
QED

Theorem sw_symmetry_lemma[local]:
  !P eq add.
  (!x y:'a. P x /\ P y /\ eq x y ==> eq y x) /\
  (!x y. P x /\ P y ==> P (add x y)) /\
  (!x y. P x /\ P y ==> add x y = add y x) /\
  (!x y z. P x /\ P y /\ P z /\ (eq x y \/ eq (add x y) z) ==>
     add x (add y z) = add (add x y) z) /\
  (!x y z. P x /\ P y /\ P z /\
     ~eq x y /\ ~eq y z /\ ~eq x z /\
     ~eq (add x y) z /\ ~eq (add y z) x ==>
     add x (add y z) = add (add x y) z) ==>
  !x y z. P x /\ P y /\ P z ==>
    add x (add y z) = add (add x y) z
Proof
  rpt strip_tac >>
  Cases_on `eq x y` >-
    metis_tac[] >>
  Cases_on `eq y z` >-
    (`eq z y` by metis_tac[] >>
     `P (add y z) /\ P (add x y)` by metis_tac[] >>
     `add z (add y x) = add (add z y) x` by metis_tac[] >>
     `add x (add y z) = add (add y z) x` by metis_tac[] >>
     `add y z = add z y` by metis_tac[] >>
     `add y x = add x y` by metis_tac[] >>
     `add z (add x y) = add (add x y) z` by metis_tac[] >>
     ntac 5 (qpat_x_assum `!x. _` kall_tac) >>
     metis_tac[]) >>
  Cases_on `eq x z` >-
    (`eq z x` by metis_tac[] >>
     `P (add x y)` by metis_tac[] >>
     `add x (add z y) = add (add x z) y` by metis_tac[] >>
     `add z (add x y) = add (add z x) y` by metis_tac[] >>
     `add y z = add z y` by metis_tac[] >>
     `add x z = add z x` by metis_tac[] >>
     `add z (add x y) = add (add x y) z` by metis_tac[] >>
     ntac 5 (qpat_x_assum `!x. _` kall_tac) >>
     metis_tac[]) >>
  Cases_on `eq (add x y) z` >-
    metis_tac[] >>
  Cases_on `eq (add y z) x` >-
    (`eq (add z y) x` by metis_tac[] >>
     `P (add y z) /\ P (add x y)` by metis_tac[] >>
     `add z (add y x) = add (add z y) x` by metis_tac[] >>
     `add x (add y z) = add (add y z) x` by metis_tac[] >>
     `add y z = add z y` by metis_tac[] >>
     `add y x = add x y` by metis_tac[] >>
     `add z (add x y) = add (add x y) z` by metis_tac[] >>
     ntac 5 (qpat_x_assum `!x. _` kall_tac) >>
     metis_tac[]) >>
  qpat_x_assum
    `!x y z. P x /\ P y /\ P z /\ ~eq x y /\ _ ==> _`
    (qspecl_then [`x`, `y`, `z`] match_mp_tac) >>
  ASM_REWRITE_TAC []
QED

Theorem sw_associativity_lemma[local]:
  !P add neg (id:'a).
  P id /\
  (!x. P x ==> P (neg x)) /\
  (!x y. P x /\ P y ==> P (add x y)) /\
  (!x. P x ==> add id x = x) /\
  (!x. P x ==> add (neg x) x = id) /\
  (!x y. P x /\ P y ==> add x y = add y x) /\
  (!x. P x ==> neg (neg x) = x) /\
  (!x y. P x /\ P y ==> neg (add x y) = add (neg x) (neg y)) /\
  (!x y. P x /\ P y ==> add x (add x y) = add (add x x) y) /\
  (!x y. P x /\ P y ==> add (neg x) (add x y) = y) /\
  (!x y z u v.
     P x /\ P y /\ P z /\ P u /\ P v ==>
     x <> id /\ y <> id /\ z <> id /\ u <> id /\ v <> id /\
     ~(y = x \/ y = neg x) /\
     ~(z = y \/ z = neg y) /\
     ~(z = x \/ z = neg x) /\
     ~(z = u \/ z = neg u) /\
     ~(x = v \/ x = neg v) ==>
     add x y = u /\ add y z = v ==>
     add x v = add u z) ==>
  !x y z. P x /\ P y /\ P z ==>
    add x (add y z) = add (add x y) z
Proof
  rpt gen_tac >>
  strip_tac >>
  MATCH_MP_TAC (Q.SPECL
    [`P`, `\x y. y = x \/ y = neg x`, `add`]
    sw_symmetry_lemma) >>
  rpt conj_tac >| [
    rpt strip_tac >>
    metis_tac[],
    metis_tac[],
    metis_tac[],
    rpt strip_tac >>
    fs[] >>
    rpt strip_tac >>
    metis_tac[],
    rpt strip_tac >>
    Cases_on `x = id` >-
      (gvs[] >>
       metis_tac[]) >>
    Cases_on `y = id` >-
      (gvs[] >>
       metis_tac[]) >>
    Cases_on `z = id` >-
      (gvs[] >>
       metis_tac[]) >>
    qpat_x_assum `!x y z u v. _`
      (qspecl_then [`x`, `y`, `z`, `add x y`, `add y z`] mp_tac) >>
    metis_tac[]
  ]
QED

Theorem sw_neg_add_affine_law[local]:
  ShortWeierstrassCurve (r:'a field) a b /\
  sw_on_curve r a b (ECAffine x1 y1) /\
  sw_on_curve r a b (ECAffine x2 y2) ==>
  sw_neg r (sw_add r a b (ECAffine x1 y1) (ECAffine x2 y2)) =
  sw_add r a b (sw_neg r (ECAffine x1 y1))
    (sw_neg r (ECAffine x2 y2))
Proof
  rpt strip_tac >>
  `Field r` by metis_tac[ShortWeierstrassCurve_def] >>
  Cases_on `x1 = x2` >-
    (`y2 = y1 \/ y2 = r.sum.inv y1` by
       metis_tac[sw_same_x_on_curve] >>
     Cases_on `y2 = y1` >-
       (gvs[] >>
        `r.sum.inv (r.sum.inv y1) = y1` by
          metis_tac[sw_on_curve_ECAffine, field_neg_neg] >>
        Cases_on `y1 = r.sum.inv y1` >-
          ASM_SIMP_TAC bool_ss [sw_neg_def, sw_add_def] >>
        `r.sum.inv y1 <> y1` by metis_tac[] >>
        `r.prod.op (r.sum.exp r.prod.id 2) y1 IN r.carrier /\
         r.prod.op (r.sum.exp r.prod.id 2) y1 <> r.sum.id` by
          (conj_tac >-
             metis_tac[sw_on_curve_ECAffine, field_num_element,
                       field_mult_element] >>
           `r.prod.op (r.sum.exp r.prod.id 2) y1 =
            r.sum.op y1 y1` by
             rw[field_num_2, field_mult_ladd, field_mult_lone] >>
           metis_tac[sw_on_curve_ECAffine, field_add_eq_zero]) >>
        `r.prod.op (r.sum.exp r.prod.id 2) (r.sum.inv y1) =
         r.sum.inv (r.prod.op (r.sum.exp r.prod.id 2) y1)` by
          metis_tac[sw_on_curve_ECAffine, field_num_element,
                    field_mult_rneg] >>
        `r.prod.op (r.sum.exp r.prod.id 2) (r.sum.inv y1) IN r.carrier /\
         r.prod.op (r.sum.exp r.prod.id 2) (r.sum.inv y1) <>
           r.sum.id` by
          metis_tac[field_neg_element, field_neg_eq_zero] >>
        `r.prod.inv (r.prod.op (r.sum.exp r.prod.id 2) y1) IN r.carrier /\
         r.prod.op (r.prod.op (r.sum.exp r.prod.id 2) y1)
           (r.prod.inv (r.prod.op (r.sum.exp r.prod.id 2) y1)) =
           r.prod.id` by
          metis_tac[sw_field_prod_inv] >>
        `r.prod.inv
           (r.prod.op (r.sum.exp r.prod.id 2) (r.sum.inv y1)) IN
           r.carrier /\
         r.prod.op
           (r.prod.op (r.sum.exp r.prod.id 2) (r.sum.inv y1))
           (r.prod.inv
             (r.prod.op (r.sum.exp r.prod.id 2) (r.sum.inv y1))) =
           r.prod.id` by
          metis_tac[sw_field_prod_inv] >>
        `a IN r.carrier` by
          metis_tac[ShortWeierstrassCurve_def] >>
        `r.prod.inv
           (r.sum.inv (r.prod.op (r.sum.exp r.prod.id 2) y1)) IN
           r.carrier /\
         r.prod.op
           (r.sum.inv (r.prod.op (r.sum.exp r.prod.id 2) y1))
           (r.prod.inv
             (r.sum.inv (r.prod.op (r.sum.exp r.prod.id 2) y1))) =
           r.prod.id` by
          metis_tac[] >>
        ASM_SIMP_TAC bool_ss
          [sw_neg_def, sw_add_def, sw_slope_def, sw_add_x_def,
           sw_add_y_def, LET_THM] >>
        MP_TAC (Q.SPECL
          [`toRing r`, `x1`, `y1`, `a`,
           `r.prod.inv (r.prod.op (r.sum.exp r.prod.id 2) y1)`,
           `r.prod.inv
             (r.prod.op (r.sum.exp r.prod.id 2) (r.sum.inv y1))`]
          sw_tangent_neg_algebra) >>
        ASM_SIMP_TAC bool_ss
          [sw_toRing_carrier, sw_toRing_zero, sw_toRing_one,
           sw_toRing_neg, sw_toRing_add, sw_toRing_mul, sw_toRing_pow,
           sw_toRing_of_num, LET_THM] >>
        metis_tac[]) >>
     `y2 = r.sum.inv y1` by metis_tac[] >>
     `r.sum.inv y2 = y1` by
       metis_tac[sw_on_curve_ECAffine, field_neg_neg] >>
     ASM_SIMP_TAC bool_ss [sw_neg_def, sw_add_def]) >>
  `x1 IN r.carrier /\ y1 IN r.carrier /\
   x2 IN r.carrier /\ y2 IN r.carrier` by
    metis_tac[sw_on_curve_ECAffine] >>
  `r.sum.op x2 (r.sum.inv x1) IN r.carrier /\
   r.sum.op x2 (r.sum.inv x1) <> r.sum.id` by
    (conj_tac >-
       metis_tac[field_add_element, field_neg_element] >>
     spose_not_then strip_assume_tac >>
     `r.sum.inv x1 = r.sum.inv x2` by
       metis_tac[field_add_eq_zero, field_neg_element] >>
     metis_tac[field_neg_eq]) >>
  `r.prod.inv (r.sum.op x2 (r.sum.inv x1)) IN r.carrier /\
   r.prod.op (r.sum.op x2 (r.sum.inv x1))
     (r.prod.inv (r.sum.op x2 (r.sum.inv x1))) = r.prod.id` by
    metis_tac[sw_field_prod_inv] >>
  `r.sum.inv (r.sum.inv y1) = y1 /\
   r.sum.inv (r.sum.inv y2) = y2` by
    metis_tac[field_neg_neg] >>
  ASM_SIMP_TAC bool_ss
    [sw_neg_def, sw_add_def, sw_slope_def, sw_add_x_def,
     sw_add_y_def, LET_THM] >>
  MP_TAC (Q.SPECL
    [`toRing r`, `x1`, `y1`, `x2`, `y2`,
     `r.prod.inv (r.sum.op x2 (r.sum.inv x1))`]
    sw_secant_neg_algebra) >>
  ASM_SIMP_TAC bool_ss
    [sw_toRing_carrier, sw_toRing_zero, sw_toRing_one,
     sw_toRing_neg, sw_toRing_add, sw_toRing_mul, sw_toRing_pow,
     LET_THM] >>
  metis_tac[]
QED

Theorem sw_neg_add_law[local]:
  ShortWeierstrassCurve (r:'a field) a b /\
  P IN sw_points r a b /\ Q IN sw_points r a b ==>
  sw_neg r (sw_add r a b P Q) =
  sw_add r a b (sw_neg r P) (sw_neg r Q)
Proof
  Cases_on `P` >> Cases_on `Q` >| [
    rw[sw_neg_def, sw_add_def],
    rw[sw_neg_def, sw_add_def],
    rw[sw_neg_def, sw_add_def],
    metis_tac[sw_points_member, sw_neg_add_affine_law]
  ]
QED

Theorem sw_slope_equations[local]:
  ShortWeierstrassCurve (r:'a field) a b /\
  sw_on_curve r a b (ECAffine x1 y1) /\
  sw_on_curve r a b (ECAffine x2 y2) /\
  ~(x1 = x2 /\ y1 = r.sum.inv y2) ==>
  let m = sw_slope r a x1 y1 x2 y2
  in m IN r.carrier /\
     r.sum.op y2 (r.sum.inv y1) =
       r.prod.op m (r.sum.op x2 (r.sum.inv x1)) /\
     r.prod.op m (r.sum.op y1 y2) =
       r.sum.op
         (r.sum.op (r.sum.op (r.prod.exp x1 2) (r.prod.op x1 x2))
           (r.prod.exp x2 2)) a
Proof
  simp[LET_THM] >> strip_tac >>
  `Field r /\ a IN r.carrier /\ b IN r.carrier /\
   x1 IN r.carrier /\ y1 IN r.carrier /\
   x2 IN r.carrier /\ y2 IN r.carrier` by
    metis_tac[ShortWeierstrassCurve_def, sw_on_curve_ECAffine] >>
  Cases_on `x1 = x2` >-
    (`y2 = y1` by
       metis_tac[sw_same_x_on_curve, field_neg_neg,
                 sw_on_curve_ECAffine] >>
     gvs[] >>
     `r.prod.op (r.sum.exp r.prod.id 2) y1 IN r.carrier /\
      r.prod.op (r.sum.exp r.prod.id 2) y1 <> r.sum.id` by
       (conj_tac >-
          metis_tac[field_num_element, field_mult_element] >>
        `r.prod.op (r.sum.exp r.prod.id 2) y1 = r.sum.op y1 y1` by
          rw[field_num_2, field_mult_ladd, field_mult_lone] >>
        metis_tac[field_add_eq_zero]) >>
     drule_all sw_field_prod_inv >> strip_tac >>
     `r.prod.op
        (r.sum.op
          (r.prod.op (r.sum.exp r.prod.id 3) (r.prod.exp x1 2)) a)
        (r.prod.inv (r.prod.op (r.sum.exp r.prod.id 2) y1))
        IN r.carrier` by
       metis_tac[field_mult_element, field_add_element,
                 field_num_element, field_exp_element] >>
     ASM_SIMP_TAC bool_ss [] >>
     MP_TAC (Q.SPECL
       [`toRing r`, `x1`, `y1`, `a`,
        `r.prod.inv (r.prod.op (r.sum.exp r.prod.id 2) y1)`,
        `r.prod.op
          (r.sum.op
            (r.prod.op (r.sum.exp r.prod.id 3) (r.prod.exp x1 2)) a)
          (r.prod.inv (r.prod.op (r.sum.exp r.prod.id 2) y1))`]
       sw_tangent_equations_algebra) >>
     ASM_SIMP_TAC bool_ss
       [listTheory.EVERY_DEF, ringLibTheory.ring_sub, sw_ring_ops,
        field_add_rneg, field_mult_rzero]) >>
  `r.sum.op x2 (r.sum.inv x1) IN r.carrier /\
   r.sum.op x2 (r.sum.inv x1) <> r.sum.id` by
    (conj_tac >-
       metis_tac[field_add_element, field_neg_element] >>
     spose_not_then strip_assume_tac >>
     `r.sum.inv x1 = r.sum.inv x2` by
       metis_tac[field_add_eq_zero, field_neg_element] >>
     metis_tac[field_neg_eq]) >>
  drule_all sw_field_prod_inv >> strip_tac >>
  ASM_SIMP_TAC bool_ss [sw_slope_def] >>
  `r.prod.op (r.sum.op y2 (r.sum.inv y1))
     (r.prod.inv (r.sum.op x2 (r.sum.inv x1))) IN r.carrier` by
    metis_tac[field_add_element, field_neg_element, field_mult_element] >>
  ASM_SIMP_TAC bool_ss [] >>
  MP_TAC (Q.SPECL
    [`toRing r`, `x1`, `y1`, `x2`, `y2`, `a`, `b`,
     `r.prod.inv (r.sum.op x2 (r.sum.inv x1))`,
     `r.prod.op (r.sum.op y2 (r.sum.inv y1))
       (r.prod.inv (r.sum.op x2 (r.sum.inv x1)))`]
    sw_secant_equations_algebra) >>
  ASM_SIMP_TAC bool_ss
    [listTheory.EVERY_DEF, ringLibTheory.ring_sub, sw_ring_ops,
     sw_curve_rhs_def]
QED

Theorem sw_reverse_secant_slope_algebra[local]:
  !(r:'a Ring) x y s t m di.
  x IN ring_carrier r /\ y IN ring_carrier r /\
  s IN ring_carrier r /\ t IN ring_carrier r /\
  m IN ring_carrier r /\ di IN ring_carrier r /\
  t = ring_add r (ring_mul r m (ring_add r x (ring_neg r s)))
        (ring_neg r y) /\
  ring_mul r (ring_add r s (ring_neg r x)) di = ring_1 r ==>
  ring_mul r (ring_add r t y) di = ring_neg r m
Proof
  ringLib.RING_TAC
QED

Theorem sw_reverse_tangent_slope_algebra[local]:
  !(r:'a Ring) x y u v a m di.
  x IN ring_carrier r /\ y IN ring_carrier r /\
  u IN ring_carrier r /\ v IN ring_carrier r /\
  a IN ring_carrier r /\ m IN ring_carrier r /\
  di IN ring_carrier r /\
  ring_add r v (ring_neg r y) =
    ring_mul r m (ring_add r u (ring_neg r x)) /\
  ring_mul r m (ring_add r y v) =
    ring_add r
      (ring_add r (ring_add r (ring_pow r x 2) (ring_mul r x u))
        (ring_pow r u 2)) a /\
  ring_add r (ring_add r (ring_pow r m 2) (ring_neg r x))
    (ring_neg r u) = x /\
  ring_mul r (ring_mul r (ring_of_num r 2) (ring_neg r y)) di =
    ring_1 r ==>
  ring_mul r
    (ring_add r (ring_mul r (ring_of_num r 3) (ring_pow r x 2)) a) di =
    ring_neg r m
Proof
  ringLib.RING_TAC
QED

Theorem sw_singular_algebra[local]:
  !(r:'a Ring) x y a b.
  x IN ring_carrier r /\ y IN ring_carrier r /\
  a IN ring_carrier r /\ b IN ring_carrier r /\
  ring_pow r y 2 =
    ring_add r (ring_add r (ring_pow r x 3) (ring_mul r a x)) b /\
  y = ring_neg r y /\
  ring_add r (ring_mul r (ring_of_num r 3) (ring_pow r x 2)) a =
    ring_0 r ==>
  ring_neg r
    (ring_mul r (ring_of_num r 16)
      (ring_add r (ring_mul r (ring_of_num r 4) (ring_pow r a 3))
        (ring_mul r (ring_of_num r 27) (ring_pow r b 2)))) = ring_0 r
Proof
  ringLib.RING_TAC
QED

Theorem sw_reverse_coordinates_algebra[local]:
  !(r:'a Ring) x y u v s m.
  x IN ring_carrier r /\ y IN ring_carrier r /\
  u IN ring_carrier r /\ v IN ring_carrier r /\
  s IN ring_carrier r /\ m IN ring_carrier r /\
  ring_add r v (ring_neg r y) =
    ring_mul r m (ring_add r u (ring_neg r x)) /\
  s = ring_add r (ring_add r (ring_pow r m 2) (ring_neg r x))
        (ring_neg r u) ==>
  ring_add r
    (ring_add r (ring_pow r (ring_neg r m) 2) (ring_neg r x))
    (ring_neg r s) = u /\
  ring_add r
    (ring_mul r (ring_neg r m) (ring_add r x (ring_neg r u))) y = v
Proof
  rpt strip_tac >| [
    qpat_x_assum `ring_add r v _ = _` kall_tac >> ringLib.RING_TAC,
    qpat_x_assum `s = _` kall_tac >> ringLib.RING_TAC
  ]
QED

Theorem sw_tangent_numerator_algebra[local]:
  !(r:'a Ring) x y u v a m.
  x IN ring_carrier r /\ y IN ring_carrier r /\
  u IN ring_carrier r /\ v IN ring_carrier r /\
  a IN ring_carrier r /\ m IN ring_carrier r /\
  ring_add r v (ring_neg r y) =
    ring_mul r m (ring_add r u (ring_neg r x)) /\
  ring_mul r m (ring_add r y v) =
    ring_add r
      (ring_add r (ring_add r (ring_pow r x 2) (ring_mul r x u))
        (ring_pow r u 2)) a /\
  ring_add r (ring_add r (ring_pow r m 2) (ring_neg r x))
    (ring_neg r u) = x ==>
  ring_add r (ring_mul r (ring_of_num r 3) (ring_pow r x 2)) a =
    ring_mul r (ring_mul r (ring_of_num r 2) y) m
Proof
  ringLib.RING_TAC
QED

Theorem sw_add_neg_cancel_affine[local]:
  ShortWeierstrassCurve (r:'a field) a b /\
  sw_on_curve r a b (ECAffine x y) /\
  sw_on_curve r a b (ECAffine u v) ==>
  sw_add r a b (sw_neg r (ECAffine x y))
    (sw_add r a b (ECAffine x y) (ECAffine u v)) = ECAffine u v
Proof
  strip_tac >>
  `Field r /\ a IN r.carrier /\ b IN r.carrier /\
   x IN r.carrier /\ y IN r.carrier /\
   u IN r.carrier /\ v IN r.carrier` by
    metis_tac[ShortWeierstrassCurve_def, sw_on_curve_ECAffine] >>
  Cases_on `x = u /\ y = r.sum.inv v` >-
    (`v = r.sum.inv y` by metis_tac[field_neg_neg] >>
     fs[sw_add_def, sw_neg_def]) >>
  MP_TAC (Q.INST
    [`x1` |-> `x`, `y1` |-> `y`, `x2` |-> `u`, `y2` |-> `v`]
    sw_slope_equations) >>
  ASM_SIMP_TAC bool_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `m = sw_slope r a x y u v` >>
  `m IN r.carrier /\
   r.sum.op v (r.sum.inv y) =
     r.prod.op m (r.sum.op u (r.sum.inv x)) /\
   r.prod.op m (r.sum.op y v) =
     r.sum.op
       (r.sum.op (r.sum.op (r.prod.exp x 2) (r.prod.op x u))
         (r.prod.exp u 2)) a` by metis_tac[] >>
  qabbrev_tac `s = sw_add_x r m x u` >>
  qabbrev_tac `t = sw_add_y r m x y s` >>
  `s IN r.carrier /\ t IN r.carrier` by
    (MAP_EVERY qunabbrev_tac [`s`, `t`] >>
     rw[sw_add_x_def, sw_add_y_def] >>
     metis_tac[field_add_element, field_mult_element,
               field_exp_element, field_neg_element]) >>
  `sw_add r a b (ECAffine x y) (ECAffine u v) = ECAffine s t` by
    rw[sw_add_def, Abbr `m`, Abbr `s`, Abbr `t`] >>
  ASM_REWRITE_TAC [sw_neg_def] >>
  `sw_add_x r (r.sum.inv m) x s = u /\
   r.sum.op
     (r.prod.op (r.sum.inv m) (r.sum.op x (r.sum.inv u))) y = v` by
    (`s = r.sum.op
       (r.sum.op (r.prod.exp m 2) (r.sum.inv x)) (r.sum.inv u)` by
       (qunabbrev_tac `s` >> REWRITE_TAC [sw_add_x_def]) >>
     MP_TAC (Q.SPECL [`toRing r`, `x`, `y`, `u`, `v`, `s`, `m`]
       sw_reverse_coordinates_algebra) >>
     ASM_SIMP_TAC bool_ss [sw_ring_ops, sw_add_x_def] >>
     DISCH_THEN MATCH_MP_TAC >>
     metis_tac[field_add_element, field_exp_element, field_neg_element]) >>
  `~(x = s /\ r.sum.inv y = r.sum.inv t) /\
   sw_slope r a x (r.sum.inv y) s t = r.sum.inv m` by
    (Cases_on `s = x` >-
       (`r.sum.op
           (r.prod.op (r.sum.exp r.prod.id 3) (r.prod.exp x 2)) a =
         r.prod.op (r.prod.op (r.sum.exp r.prod.id 2) y) m` by
          (MP_TAC (Q.SPECL [`toRing r`, `x`, `y`, `u`, `v`, `a`, `m`]
             sw_tangent_numerator_algebra) >>
           ASM_SIMP_TAC bool_ss [sw_ring_ops] >>
           DISCH_THEN MATCH_MP_TAC >>
           qunabbrev_tac `s` >>
           qpat_x_assum `sw_add_x r m x u = x`
             (mp_tac o REWRITE_RULE [sw_add_x_def]) >>
           REWRITE_TAC []) >>
        `y <> r.sum.inv y` by
          (spose_not_then strip_assume_tac >>
           `r.sum.op y y = r.sum.id` by metis_tac[field_add_eq_zero] >>
           `r.prod.op (r.sum.exp r.prod.id 2) y = r.sum.id` by
             rw[field_num_2, field_mult_ladd, field_mult_lone] >>
           `r.sum.op
              (r.prod.op (r.sum.exp r.prod.id 3) (r.prod.exp x 2)) a =
            r.sum.id` by metis_tac[field_mult_lzero] >>
           MP_TAC (Q.SPECL [`toRing r`, `x`, `y`, `a`, `b`]
             sw_singular_algebra) >>
           ASM_SIMP_TAC bool_ss [sw_ring_ops] >>
           fs[ShortWeierstrassCurve_def, sw_on_curve_def,
              sw_curve_rhs_def, sw_discriminant_def]) >>
        `t = r.sum.inv y` by
          ASM_SIMP_TAC bool_ss
            [Abbr `t`, sw_add_y_def, field_add_rneg, field_mult_rzero,
             field_add_lzero, field_neg_element] >>
        `r.sum.inv y IN r.carrier` by metis_tac[field_neg_element] >>
        `r.prod.op (r.sum.exp r.prod.id 2) (r.sum.inv y) IN r.carrier`
          by metis_tac[field_num_element, field_mult_element] >>
        `r.prod.op (r.sum.exp r.prod.id 2) (r.sum.inv y) <> r.sum.id`
          by
            (`r.prod.op (r.sum.exp r.prod.id 2) (r.sum.inv y) =
              r.sum.op (r.sum.inv y) (r.sum.inv y)` by
               ASM_SIMP_TAC bool_ss
                 [field_num_2, field_mult_ladd, field_mult_lone,
                  field_one_element] >>
             metis_tac[field_add_eq_zero, field_neg_neg]) >>
        drule_all sw_field_prod_inv >> strip_tac >>
        conj_tac >- metis_tac[field_neg_neg] >>
        MP_TAC (Q.SPECL
          [`toRing r`, `x`, `y`, `u`, `v`, `a`, `m`,
           `r.prod.inv
             (r.prod.op (r.sum.exp r.prod.id 2) (r.sum.inv y))`]
          sw_reverse_tangent_slope_algebra) >>
        ASM_SIMP_TAC bool_ss [sw_ring_ops] >>
        PURE_ONCE_REWRITE_TAC [sw_slope_tangent] >>
        ASM_REWRITE_TAC [] >>
        DISCH_THEN MATCH_MP_TAC >>
        qunabbrev_tac `s` >>
        qpat_x_assum `sw_add_x r m x u = x`
          (mp_tac o REWRITE_RULE [sw_add_x_def]) >>
        REWRITE_TAC []) >>
     `x <> s` by metis_tac[] >>
     `r.sum.op s (r.sum.inv x) IN r.carrier /\
      r.sum.op s (r.sum.inv x) <> r.sum.id` by
       (conj_tac >-
          metis_tac[field_add_element, field_neg_element] >>
        spose_not_then strip_assume_tac >>
        `r.sum.inv x = r.sum.inv s` by
          metis_tac[field_add_eq_zero, field_neg_element] >>
        metis_tac[field_neg_eq]) >>
     drule_all sw_field_prod_inv >> strip_tac >>
     conj_tac >- metis_tac[] >>
     `t = r.sum.op
        (r.prod.op m (r.sum.op x (r.sum.inv s))) (r.sum.inv y)` by
       (qunabbrev_tac `t` >> REWRITE_TAC [sw_add_y_def]) >>
     MP_TAC (Q.SPECL
       [`toRing r`, `x`, `y`, `s`, `t`, `m`,
        `r.prod.inv (r.sum.op s (r.sum.inv x))`]
       sw_reverse_secant_slope_algebra) >>
     ASM_SIMP_TAC bool_ss [sw_ring_ops, sw_slope_def, field_neg_neg] >>
     DISCH_THEN MATCH_MP_TAC >>
     metis_tac[field_add_element, field_mult_element, field_neg_element]) >>
  ASM_SIMP_TAC bool_ss
    [sw_add_def, sw_add_y_def, field_neg_neg, LET_THM]
QED

(* In P + (P + 2P) = 2P + 2P the right outer secant degenerates.
   Its tangent equation replaces the missing denominator inverse. *)
Overload "+"[local] = ``ring_add (r:'a Ring)``
Overload "-"[local] = ``ring_sub (r:'a Ring)``
Overload "*"[local] = ``ring_mul (r:'a Ring)``
Overload "**"[local] = ``ring_pow (r:'a Ring)``

Theorem sw_quadruple_tangent_cut_algebra[local]:
  !(r:'a Ring) x y X Y a m n l d.
  EVERY (\z. z IN ring_carrier r) [x; y; X; Y; a; m; n; l; d] /\
  d = X - x /\
  m ** 2 = X + x + x /\
  Y = ring_neg r (m * d) - y /\
  n * d = Y - y /\
  n * (y + Y) = x ** 2 + x * X + X ** 2 + a /\
  l * (Y + Y) = X ** 2 + X * X + X ** 2 + a ==>
  ((m - n) * (m + l) - x + X) * d = ring_0 r
Proof
  simp[listTheory.EVERY_DEF] >> ringLib.RING_TAC
QED

Theorem sw_quadruple_secant_cut_algebra[local]:
  !(r:'a Ring) x y X Y m n v w k d.
  EVERY (\z. z IN ring_carrier r) [x; y; X; Y; m; n; v; w; k; d] /\
  d = X - x /\
  m ** 2 = X + x + x /\
  Y = ring_neg r (m * d) - y /\
  n * d = Y - y /\
  v = n ** 2 - x - X /\
  w = n * (x - v) - y /\
  k * (v - x) = w - y ==>
  v - x = (n - m) * (n + m) /\
  (k + n) * (v - x) = (m + n) * d
Proof
  rpt gen_tac >>
  PURE_REWRITE_TAC [listTheory.EVERY_DEF] >> BETA_TAC >> strip_tac >>
  conj_tac >-
    (qpat_x_assum `d = _` kall_tac >>
     qpat_x_assum `Y = _` kall_tac >>
     qpat_x_assum `n * d = _` kall_tac >>
     qpat_x_assum `w = _` kall_tac >>
     qpat_x_assum `k * (v - x) = _` kall_tac >>
     ringLib.RING_TAC) >>
  qpat_x_assum `d = _` kall_tac >>
  qpat_x_assum `m ** 2 = _` kall_tac >>
  qpat_x_assum `v = _` kall_tac >>
  ringLib.RING_TAC
QED

Theorem sw_quadruple_slope_cut_algebra[local]:
  !(r:'a Ring) m n k l d A ia.
  EVERY (\z. z IN ring_carrier r) [m; n; k; l; d; A; ia] /\
  (m - n) * (m + l) = ring_neg r d /\
  A = (n - m) * (n + m) /\
  (k + n) * A = (m + n) * d /\
  A * ia = ring_1 r ==>
  k - l = m - n
Proof
  simp[listTheory.EVERY_DEF] >> ringLib.RING_TAC
QED

fun sw_ring_using equations (asl, goal) =
  ringLib.RING_TAC
    (List.filter
       (fn tm => not (is_eq tm) orelse
                 List.exists (fn eq => aconv tm eq) equations) asl,
     goal)

Theorem sw_quadruple_coordinates_algebra[local]:
  !(r:'a Ring) x y X Y a m n v w k l d id ia.
  EVERY (\z. z IN ring_carrier r)
    [x; y; X; Y; a; m; n; v; w; k; l; d; id; ia] /\
  d = X - x /\ X = m ** 2 - x - x /\
  Y = m * (x - X) - y /\
  n * d = Y - y /\
  n * (y + Y) = x ** 2 + x * X + X ** 2 + a /\
  v = n ** 2 - x - X /\ w = n * (x - v) - y /\
  k * (v - x) = w - y /\
  l * (Y + Y) = X ** 2 + X * X + X ** 2 + a /\
  d * id = ring_1 r /\ (v - x) * ia = ring_1 r ==>
  let xl = k ** 2 - x - v;
      xr = l ** 2 - X - X
  in xl = xr /\ k * (x - xl) - y = l * (X - xr) - Y
Proof
  rpt gen_tac >>
  PURE_REWRITE_TAC [listTheory.EVERY_DEF, LET_THM] >>
  BETA_TAC >> strip_tac >>
  `m ** 2 = X + x + x` by sw_ring_using [``X = m ** 2 - x - x``] >>
  `Y = ring_neg r (m * d) - y` by
    sw_ring_using [``Y = m * (x - X) - y``, ``d = X - x``] >>
  `((m - n) * (m + l) - x + X) * d = ring_0 r` by
    (MATCH_MP_TAC (Q.SPECL
       [`r`, `x`, `y`, `X`, `Y`, `a`, `m`, `n`, `l`, `d`]
       sw_quadruple_tangent_cut_algebra) >>
     PURE_REWRITE_TAC [listTheory.EVERY_DEF] >> BETA_TAC >>
     rpt conj_tac >>
     FIRST [FIRST_ASSUM ACCEPT_TAC, ACCEPT_TAC TRUTH]) >>
  `(m - n) * (m + l) = x - X` by
    sw_ring_using
      [``((m - n) * (m + l) - x + X) * d = ring_0 (r:'a Ring)``,
       ``d * id = ring_1 (r:'a Ring)``] >>
  `v - x = (n - m) * (n + m) /\
   (k + n) * (v - x) = (m + n) * d` by
    (MATCH_MP_TAC (Q.SPECL
       [`r`, `x`, `y`, `X`, `Y`, `m`, `n`, `v`, `w`, `k`, `d`]
       sw_quadruple_secant_cut_algebra) >>
     PURE_REWRITE_TAC [listTheory.EVERY_DEF] >> BETA_TAC >>
     rpt conj_tac >>
     FIRST [FIRST_ASSUM ACCEPT_TAC, ACCEPT_TAC TRUTH]) >>
  `(m - n) * (m + l) = ring_neg r d` by
    sw_ring_using
      [``(m - n) * (m + l) = x - X``, ``d = X - x``] >>
  `k - l = m - n` by
    (MATCH_MP_TAC (Q.SPECL
       [`r`, `m`, `n`, `k`, `l`, `d`, `v - x`, `ia`]
       sw_quadruple_slope_cut_algebra) >>
     PURE_REWRITE_TAC [listTheory.EVERY_DEF] >> BETA_TAC >>
     rpt conj_tac >>
     FIRST [FIRST_ASSUM ACCEPT_TAC, ACCEPT_TAC TRUTH,
            MATCH_MP_TAC RING_SUB >> ASM_REWRITE_TAC []]) >>
  MATCH_MP_TAC (BETA_RULE (REWRITE_RULE [LET_THM]
    (Q.SPECL
       [`r`, `x`, `y`, `x`, `y`, `X`, `m`, `n`, `X`, `Y`,
        `v`, `w`, `k`, `l`]
       sw_assoc_outputs_algebra))) >>
  PURE_REWRITE_TAC [listTheory.EVERY_DEF] >> BETA_TAC >>
  rpt conj_tac >>
  FIRST [FIRST_ASSUM ACCEPT_TAC, ACCEPT_TAC TRUTH, sw_ring_using []]
QED

Theorem sw_assoc_affine_nonvertical[local]:
  ShortWeierstrassCurve (r:'a field) a b /\
  sw_on_curve r a b (ECAffine x1 y1) /\
  sw_on_curve r a b (ECAffine x2 y2) /\
  sw_on_curve r a b (ECAffine x3 y3) /\
  sw_on_curve r a b (ECAffine ux uy) /\
  sw_on_curve r a b (ECAffine vx vy) /\
  sw_add r a b (ECAffine x1 y1) (ECAffine x2 y2) = ECAffine ux uy /\
  sw_add r a b (ECAffine x2 y2) (ECAffine x3 y3) = ECAffine vx vy /\
  x1 <> vx /\ ux <> x3 ==>
  sw_add r a b (ECAffine x1 y1) (ECAffine vx vy) =
  sw_add r a b (ECAffine ux uy) (ECAffine x3 y3)
Proof
  strip_tac >>
  `Field r /\ a IN r.carrier /\ b IN r.carrier /\
   x1 IN r.carrier /\ y1 IN r.carrier /\
   x2 IN r.carrier /\ y2 IN r.carrier /\
   x3 IN r.carrier /\ y3 IN r.carrier /\
   ux IN r.carrier /\ uy IN r.carrier /\
   vx IN r.carrier /\ vy IN r.carrier` by
    metis_tac[ShortWeierstrassCurve_def, sw_on_curve_ECAffine] >>
  `~(x1 = x2 /\ y1 = r.sum.inv y2) /\
   ~(x2 = x3 /\ y2 = r.sum.inv y3)` by
    (conj_tac >> spose_not_then strip_assume_tac >> fs[sw_add_def]) >>
  MP_TAC sw_slope_equations >>
  impl_tac >- metis_tac[] >>
  REWRITE_TAC [LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  MP_TAC (Q.INST
    [`x1` |-> `x2`, `y1` |-> `y2`, `x2` |-> `x3`, `y2` |-> `y3`]
    sw_slope_equations) >>
  impl_tac >- metis_tac[] >>
  REWRITE_TAC [LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  MP_TAC (Q.INST [`x2` |-> `vx`, `y2` |-> `vy`] sw_slope_equations) >>
  impl_tac >- metis_tac[] >>
  REWRITE_TAC [LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  MP_TAC (Q.INST
    [`x1` |-> `ux`, `y1` |-> `uy`, `x2` |-> `x3`, `y2` |-> `y3`]
    sw_slope_equations) >>
  impl_tac >- metis_tac[] >>
  REWRITE_TAC [LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  ASM_REWRITE_TAC [sw_add_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> REWRITE_TAC [sw_point_11] >>
  qabbrev_tac `m = sw_slope r a x1 y1 x2 y2` >>
  qabbrev_tac `n = sw_slope r a x2 y2 x3 y3` >>
  qabbrev_tac `k = sw_slope r a x1 y1 vx vy` >>
  qabbrev_tac `l = sw_slope r a ux uy x3 y3` >>
  `ux = sw_add_x r m x1 x2 /\
   uy = sw_add_y r m x1 y1 ux /\
   vx = sw_add_x r n x2 x3 /\
   vy = sw_add_y r n x2 y2 vx` by
    (Cases_on `x1 = x2` >> Cases_on `x2 = x3` >>
     fs[sw_add_def, LET_THM, Abbr `m`, Abbr `n`] >> metis_tac[]) >>
  qabbrev_tac `ia = r.prod.inv (r.sum.op vx (r.sum.inv x1))` >>
  qabbrev_tac `ib = r.prod.inv (r.sum.op x3 (r.sum.inv ux))` >>
  `ia IN r.carrier /\
   r.prod.op (r.sum.op vx (r.sum.inv x1)) ia = r.prod.id` by
    (qunabbrev_tac `ia` >> irule sw_field_prod_inv >>
     metis_tac[field_add_element, field_neg_element, field_add_eq_zero,
               field_neg_eq]) >>
  `ib IN r.carrier /\
   r.prod.op (r.sum.op x3 (r.sum.inv ux)) ib = r.prod.id` by
    (qunabbrev_tac `ib` >> irule sw_field_prod_inv >>
     metis_tac[field_add_element, field_neg_element, field_add_eq_zero,
               field_neg_eq]) >>
  `k = r.prod.op (r.sum.op vy (r.sum.inv y1)) ia /\
   l = r.prod.op (r.sum.op y3 (r.sum.inv uy)) ib` by
    SIMP_TAC bool_ss
      [Abbr `k`, Abbr `l`, Abbr `ia`, Abbr `ib`, sw_slope_def,
       ASSUME ``x1 <> vx``, ASSUME ``ux <> x3``] >>
  REWRITE_TAC [sw_add_x_def, sw_add_y_def] >>
  MATCH_MP_TAC (BETA_RULE (REWRITE_RULE
    [listTheory.EVERY_DEF, LET_THM, ringLibTheory.ring_sub,
     MATCH_MP sw_ring_ops (ASSUME ``Field (r:'a field)``)]
    (Q.SPECL
      [`toRing r`, `x1`, `y1`, `x2`, `y2`, `x3`, `y3`, `a`,
       `m`, `n`, `ux`, `uy`, `vx`, `vy`, `k`, `l`, `ia`, `ib`]
      sw_assoc_coordinates_algebra))) >>
  RULE_ASSUM_TAC (REWRITE_RULE [sw_add_x_def, sw_add_y_def]) >>
  rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC
QED

Theorem sw_quadruple_affine_nonvertical[local]:
  ShortWeierstrassCurve (r:'a field) a b /\
  sw_on_curve r a b (ECAffine x y) /\
  sw_on_curve r a b (ECAffine X Y) /\
  sw_on_curve r a b (ECAffine v w) /\
  sw_add r a b (ECAffine x y) (ECAffine x y) = ECAffine X Y /\
  sw_add r a b (ECAffine x y) (ECAffine X Y) = ECAffine v w /\
  x <> X /\ x <> v /\ Y <> r.sum.inv Y ==>
  sw_add r a b (ECAffine x y) (ECAffine v w) =
  sw_add r a b (ECAffine X Y) (ECAffine X Y)
Proof
  strip_tac >>
  `Field r /\ a IN r.carrier /\
   x IN r.carrier /\ y IN r.carrier /\
   X IN r.carrier /\ Y IN r.carrier /\
   v IN r.carrier /\ w IN r.carrier` by
    metis_tac[ShortWeierstrassCurve_def, sw_on_curve_ECAffine] >>
  `y <> r.sum.inv y` by
    (spose_not_then strip_assume_tac >> fs[sw_add_def]) >>
  MP_TAC (Q.INST
    [`x1` |-> `x`, `y1` |-> `y`, `x2` |-> `x`, `y2` |-> `y`]
    sw_slope_equations) >>
  impl_tac >- metis_tac[] >>
  REWRITE_TAC [LET_THM] >> BETA_TAC >> strip_tac >>
  MP_TAC (Q.INST
    [`x1` |-> `x`, `y1` |-> `y`, `x2` |-> `X`, `y2` |-> `Y`]
    sw_slope_equations) >>
  impl_tac >- metis_tac[] >>
  REWRITE_TAC [LET_THM] >> BETA_TAC >> strip_tac >>
  MP_TAC (Q.INST
    [`x1` |-> `x`, `y1` |-> `y`, `x2` |-> `v`, `y2` |-> `w`]
    sw_slope_equations) >>
  impl_tac >- metis_tac[] >>
  REWRITE_TAC [LET_THM] >> BETA_TAC >> strip_tac >>
  MP_TAC (Q.INST
    [`x1` |-> `X`, `y1` |-> `Y`, `x2` |-> `X`, `y2` |-> `Y`]
    sw_slope_equations) >>
  impl_tac >- metis_tac[] >>
  REWRITE_TAC [LET_THM] >> BETA_TAC >> strip_tac >>
  ASM_REWRITE_TAC [sw_add_def, LET_THM] >>
  BETA_TAC >> REWRITE_TAC [sw_point_11] >>
  qabbrev_tac `m = sw_slope r a x y x y` >>
  qabbrev_tac `n = sw_slope r a x y X Y` >>
  qabbrev_tac `k = sw_slope r a x y v w` >>
  qabbrev_tac `l = sw_slope r a X Y X Y` >>
  `X = sw_add_x r m x x /\ Y = sw_add_y r m x y X /\
   v = sw_add_x r n x X /\ w = sw_add_y r n x y v` by
    (fs[sw_add_def, LET_THM, Abbr `m`, Abbr `n`] >> metis_tac[]) >>
  `r.sum.op X (r.sum.inv x) IN r.carrier` by
    metis_tac[field_add_element, field_neg_element] >>
  qabbrev_tac `di = r.prod.inv (r.sum.op X (r.sum.inv x))` >>
  qabbrev_tac `ia = r.prod.inv (r.sum.op v (r.sum.inv x))` >>
  `di IN r.carrier /\
   r.prod.op (r.sum.op X (r.sum.inv x)) di = r.prod.id` by
    (qunabbrev_tac `di` >> irule sw_field_prod_inv >>
     metis_tac[field_add_element, field_neg_element, field_add_eq_zero,
               field_neg_eq]) >>
  `ia IN r.carrier /\
   r.prod.op (r.sum.op v (r.sum.inv x)) ia = r.prod.id` by
    (qunabbrev_tac `ia` >> irule sw_field_prod_inv >>
     metis_tac[field_add_element, field_neg_element, field_add_eq_zero,
               field_neg_eq]) >>
  REWRITE_TAC [sw_add_x_def, sw_add_y_def] >>
  MATCH_MP_TAC (BETA_RULE (REWRITE_RULE
    [listTheory.EVERY_DEF, LET_THM, ringLibTheory.ring_sub,
     MATCH_MP sw_ring_ops (ASSUME ``Field (r:'a field)``)]
    (Q.SPECL
      [`toRing r`, `x`, `y`, `X`, `Y`, `a`, `m`, `n`, `v`, `w`,
       `k`, `l`, `r.sum.op X (r.sum.inv x)`, `di`, `ia`]
      sw_quadruple_coordinates_algebra))) >>
  RULE_ASSUM_TAC (REWRITE_RULE [sw_add_x_def, sw_add_y_def]) >>
  rpt conj_tac >>
  FIRST [FIRST_ASSUM ACCEPT_TAC, FIRST_ASSUM (ACCEPT_TAC o SYM), REFL_TAC]
QED

Theorem sw_add_neg_cancel_law[local]:
  ShortWeierstrassCurve (r:'a field) a b /\
  P IN sw_points r a b /\ Q IN sw_points r a b ==>
  sw_add r a b (sw_neg r P) (sw_add r a b P Q) = Q
Proof
  Cases_on `P` >> Cases_on `Q` >| [
    rw[],
    rw[],
    metis_tac[sw_add_r_infinity, sw_add_neg_l],
    metis_tac[sw_points_member, sw_add_neg_cancel_affine]
  ]
QED

Theorem sw_add_self_assoc_law[local]:
  ShortWeierstrassCurve (r:'a field) a b /\
  P IN sw_points r a b /\ Q IN sw_points r a b ==>
  sw_add r a b P (sw_add r a b P Q) =
  sw_add r a b (sw_add r a b P P) Q
Proof
  strip_tac >>
  Cases_on `P = ECInfinity` >-
    ASM_SIMP_TAC bool_ss [sw_add_l_infinity] >>
  Cases_on `Q = ECInfinity` >-
    ASM_SIMP_TAC bool_ss [sw_add_r_infinity] >>
  Cases_on `Q = P` >-
    metis_tac[sw_add_comm, sw_add_mem] >>
  qabbrev_tac `U = sw_add r a b P P` >>
  qabbrev_tac `V = sw_add r a b P Q` >>
  `U IN sw_points r a b /\ V IN sw_points r a b` by
    metis_tac[sw_add_mem, Abbr `U`, Abbr `V`] >>
  Cases_on `U = ECInfinity` >-
    (`sw_neg r P = P` by
       metis_tac[sw_add_neg_cancel_law, sw_add_r_infinity, Abbr `U`] >>
     metis_tac[sw_add_neg_cancel_law, sw_add_l_infinity, Abbr `V`]) >>
  Cases_on `V = ECInfinity` >-
    (`Q = sw_neg r P` by
       metis_tac[sw_add_neg_cancel_law, sw_add_r_infinity, Abbr `V`] >>
     metis_tac[sw_add_neg_cancel_law, sw_add_comm, sw_neg_mem,
               sw_add_r_infinity, Abbr `U`]) >>
  Cases_on `V = P` >-
    (`Q = ECInfinity` by
       metis_tac[sw_add_neg_cancel_law, sw_add_neg_l, Abbr `V`] >>
     metis_tac[]) >>
  `sw_neg r U = sw_add r a b (sw_neg r P) (sw_neg r P)` by
    metis_tac[sw_neg_add_law, Abbr `U`] >>
  Cases_on `V = sw_neg r P` >-
    (`Q = sw_neg r U` by
       metis_tac[sw_add_neg_cancel_law, Abbr `V`] >>
     metis_tac[sw_add_neg_r]) >>
  Cases_on `Q = sw_neg r U` >-
    (`sw_neg r P IN sw_points r a b` by metis_tac[sw_neg_mem] >>
     `sw_add r a b P (sw_neg r U) = sw_neg r P` by
       metis_tac[sw_add_neg_cancel_law, sw_neg_involutive] >>
     `V = sw_neg r P` by metis_tac[Abbr `V`] >>
     metis_tac[]) >>
  `U = sw_add r a b P P /\ V = sw_add r a b P Q` by
    metis_tac[Abbr `U`, Abbr `V`] >>
  qpat_x_assum `Abbrev (U = _)` kall_tac >>
  qpat_x_assum `Abbrev (V = _)` kall_tac >>
  Cases_on `P` >- metis_tac[] >>
  rename1 `sw_add r a b (ECAffine x y) V` >>
  Cases_on `Q` >- metis_tac[] >>
  rename1 `sw_add r a b U (ECAffine u z)` >>
  Cases_on `U` >- metis_tac[] >>
  rename1 `sw_add r a b (ECAffine X Y) (ECAffine u z)` >>
  Cases_on `V` >- metis_tac[] >>
  rename1 `sw_add r a b (ECAffine x y) (ECAffine v w)` >>
  `x <> v` by
    (spose_not_then strip_assume_tac >>
     metis_tac[sw_same_x_on_curve, sw_points_member, sw_neg_def]) >>
  Cases_on `X = u` >-
    (`ECAffine u z = ECAffine X Y` by
       metis_tac[sw_same_x_on_curve, sw_points_member, sw_neg_def] >>
     `x <> X` by
       (spose_not_then strip_assume_tac >>
        `ECAffine X Y = ECAffine x y \/
         ECAffine X Y = sw_neg r (ECAffine x y)` by
          metis_tac[sw_same_x_on_curve, sw_points_member, sw_neg_def] >>
        metis_tac[sw_add_neg_r, sw_add_neg_cancel_law]) >>
     `Y <> r.sum.inv Y` by
       (spose_not_then strip_assume_tac >>
        `ECAffine u z = sw_neg r (ECAffine X Y)` by
          metis_tac[sw_neg_def] >>
        metis_tac[]) >>
     metis_tac[sw_quadruple_affine_nonvertical, sw_points_member]) >>
  metis_tac[sw_assoc_affine_nonvertical, sw_points_member]
QED

Theorem sw_assoc_distinct_affine_coordinates[local]:
  ShortWeierstrassCurve (r:'a field) a b /\
  p IN sw_points r a b /\ q IN sw_points r a b /\
  t IN sw_points r a b /\ u IN sw_points r a b /\
  v IN sw_points r a b /\
  p <> ECInfinity /\ q <> ECInfinity /\ t <> ECInfinity /\
  u <> ECInfinity /\ v <> ECInfinity /\
  ~(q = p \/ q = sw_neg r p) /\
  ~(t = q \/ t = sw_neg r q) /\
  ~(t = p \/ t = sw_neg r p) /\
  ~(t = u \/ t = sw_neg r u) /\
  ~(p = v \/ p = sw_neg r v) /\
  sw_add r a b p q = u /\ sw_add r a b q t = v ==>
  sw_add r a b p v = sw_add r a b u t
Proof
  strip_tac >>
  Cases_on `p` >- metis_tac[] >>
  rename1 `sw_add r a b (ECAffine x1 y1) q = u` >>
  Cases_on `q` >- metis_tac[] >>
  rename1 `sw_add r a b (ECAffine x1 y1) (ECAffine x2 y2) = u` >>
  Cases_on `t` >- metis_tac[] >>
  rename1 `sw_add r a b (ECAffine x2 y2) (ECAffine x3 y3) = v` >>
  Cases_on `u` >- metis_tac[] >>
  rename1 `sw_add r a b (ECAffine x1 y1) (ECAffine x2 y2) = ECAffine ux uy` >>
  Cases_on `v` >- metis_tac[] >>
  rename1 `sw_add r a b (ECAffine x2 y2) (ECAffine x3 y3) = ECAffine vx vy` >>
  `Field r /\
   sw_on_curve r a b (ECAffine x1 y1) /\
   sw_on_curve r a b (ECAffine x2 y2) /\
   sw_on_curve r a b (ECAffine x3 y3) /\
   sw_on_curve r a b (ECAffine ux uy) /\
   sw_on_curve r a b (ECAffine vx vy)` by
    metis_tac[ShortWeierstrassCurve_def, sw_points_member] >>
  `x1 <> vx /\ ux <> x3` by
    metis_tac[sw_same_x_on_curve, sw_neg_def, field_neg_neg,
              sw_on_curve_ECAffine] >>
  MP_TAC sw_assoc_affine_nonvertical >>
  ASM_REWRITE_TAC []
QED

Theorem sw_add_assoc:
  ShortWeierstrassCurve (r:'a field) a b /\
  p IN sw_points r a b /\ q IN sw_points r a b /\
  t IN sw_points r a b ==>
  sw_add r a b (sw_add r a b p q) t =
  sw_add r a b p (sw_add r a b q t)
Proof
  rpt strip_tac >>
  MATCH_MP_TAC EQ_SYM >>
  qsuff_tac
    `!x y z.
       x IN sw_points r a b /\ y IN sw_points r a b /\
       z IN sw_points r a b ==>
       sw_add r a b x (sw_add r a b y z) =
       sw_add r a b (sw_add r a b x y) z` >- metis_tac[] >>
  MATCH_MP_TAC (BETA_RULE (Q.ISPECL
    [`\P. P IN sw_points r a b`, `sw_add r a b`,
     `sw_neg r`, `ECInfinity`] sw_associativity_lemma)) >>
  rpt conj_tac >| [
    rw[],
    metis_tac[sw_neg_mem],
    metis_tac[sw_add_mem],
    rw[],
    metis_tac[sw_add_neg_l],
    metis_tac[sw_add_comm],
    metis_tac[sw_neg_involutive],
    metis_tac[sw_neg_add_law],
    metis_tac[sw_add_self_assoc_law],
    metis_tac[sw_add_neg_cancel_law],
    metis_tac[sw_assoc_distinct_affine_coordinates]
  ]
QED

Theorem sw_add_affine_assoc:
  ShortWeierstrassCurve (r:'a field) a b /\
  sw_on_curve r a b (ECAffine x1 y1) /\
  sw_on_curve r a b (ECAffine x2 y2) /\
  sw_on_curve r a b (ECAffine x3 y3) ==>
  sw_add r a b
    (sw_add r a b (ECAffine x1 y1) (ECAffine x2 y2))
    (ECAffine x3 y3) =
  sw_add r a b (ECAffine x1 y1)
    (sw_add r a b (ECAffine x2 y2) (ECAffine x3 y3))
Proof
  metis_tac[sw_add_assoc, sw_points_member]
QED

Theorem sw_points_subset_coordinates:
  sw_points (r:'a field) a b SUBSET
    {ECInfinity} UNION
    IMAGE (\(x,y). ECAffine x y) (r.carrier CROSS r.carrier)
Proof
  rw[pred_setTheory.SUBSET_DEF] >>
  Cases_on `x` >>
  fs[sw_points_member, sw_on_curve_def] >>
  simp[pairTheory.EXISTS_PROD]
QED

Theorem sw_points_finite:
  FiniteField (r:'a field) ==> FINITE (sw_points r a b)
Proof
  strip_tac >>
  `FINITE r.carrier` by metis_tac[FiniteField_def] >>
  `FINITE
    ({ECInfinity} UNION
     IMAGE (\(x,y). ECAffine x y) (r.carrier CROSS r.carrier))` by
    metis_tac[pred_setTheory.FINITE_SING, pred_setTheory.FINITE_CROSS,
              pred_setTheory.IMAGE_FINITE, pred_setTheory.FINITE_UNION] >>
  metis_tac[sw_points_subset_coordinates, pred_setTheory.SUBSET_FINITE]
QED

Theorem short_weierstrass_group:
  ShortWeierstrassCurve (r:'a field) a b ==>
  Group (sw_group r a b)
Proof
  strip_tac >>
  rw[groupTheory.group_def_alt, sw_group_def] >| [
    metis_tac[sw_add_on_curve],
    metis_tac[sw_add_assoc, sw_points_member],
    qexists_tac `sw_neg r x` >>
    metis_tac[sw_neg_on_curve, sw_add_neg_l, sw_points_member]
  ]
QED

Theorem sw_group_inv:
  ShortWeierstrassCurve (r:'a field) a b /\
  P IN sw_points r a b ==>
  (sw_group r a b).inv P = sw_neg r P
Proof
  metis_tac[groupTheory.group_linv_unique, short_weierstrass_group,
            sw_group_carrier, sw_group_id, sw_group_op,
            sw_neg_on_curve, sw_add_neg_l, sw_points_member]
QED

Theorem short_weierstrass_abelian_group:
  ShortWeierstrassCurve (r:'a field) a b ==>
  AbelianGroup (sw_group r a b)
Proof
  strip_tac >>
  rw[groupTheory.AbelianGroup_def] >-
    rw[short_weierstrass_group] >>
  rw[sw_group_def] >>
  metis_tac[sw_add_comm, sw_points_member]
QED

Theorem short_weierstrass_finite_group:
  FiniteField (r:'a field) /\ ShortWeierstrassCurve r a b ==>
  FiniteAbelianGroup (sw_group r a b)
Proof
  rw[groupTheory.FiniteAbelianGroup_def,
     short_weierstrass_abelian_group, sw_group_def, sw_points_finite]
QED
