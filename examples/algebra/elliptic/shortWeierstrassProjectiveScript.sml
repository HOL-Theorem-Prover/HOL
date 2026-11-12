(* ------------------------------------------------------------------------- *)
(* Homogeneous Coordinates for Short-Weierstrass Curves                       *)
(* ------------------------------------------------------------------------- *)
(*
   Documentation

   Ordinary homogeneous triples (X,Y,Z), with affine coordinates (X/Z,Y/Z);
   these are not Jacobian coordinates. Equivalence is common nonzero scaling.
   sw_projective_valid excludes the zero triple, but does not assert the
   curve equation. sw_projective_rep relates a valid curve representative to
   an sw_point; infinity representatives have X = Z = 0 and Y <> 0.

   Definitions:
     sw_projective_valid_def, sw_projective_scale_def, sw_projective_equiv_def.
     sw_point_to_projective_def, sw_projective_to_point_def.
     sw_projective_rep_def, sw_projective_on_curve_def.

   Main results (with the stated field/carrier hypotheses):
     sw_point_projective_roundtrip    Decode an embedded curve point.
     sw_projective_equiv_refl, sw_projective_equiv_sym,
       sw_projective_equiv_trans      Equivalence on valid triples.
     sw_projective_equiv_iff_to_point Equal decoding, with infinity guards.
     sw_projective_rep_infinity, sw_projective_rep_affine,
       sw_projective_rep_scale       Representation and scaling.

   The total decoder is not a validity test: it maps every Z = 0 triple to
   ECInfinity, including triples that are not curve representatives.
*)

Theory shortWeierstrassProjective
Ancestors
  shortWeierstrass
  shortWeierstrassGroup
Libs
  ringLib

open fieldTheory ringTheory

(* Nonzero homogeneous triples. Off-curve points at infinity remain valid
   projective-space points, but are deliberately not curve representatives. *)
Definition sw_projective_valid_def:
  sw_projective_valid (r:'a field) (X,Y,Z) <=>
    X IN r.carrier /\ Y IN r.carrier /\ Z IN r.carrier /\
    ~(X = r.sum.id /\ Y = r.sum.id /\ Z = r.sum.id)
End

Definition sw_projective_scale_def:
  sw_projective_scale (r:'a field) k (X,Y,Z) =
    (r.prod.op k X, r.prod.op k Y, r.prod.op k Z)
End

Definition sw_projective_equiv_def:
  sw_projective_equiv (r:'a field) p q <=>
    sw_projective_valid r p /\ sw_projective_valid r q /\
    ?k. k IN r.carrier /\ k <> r.sum.id /\
        q = sw_projective_scale r k p
End

Definition sw_point_to_projective_def:
  (sw_point_to_projective (r:'a field) ECInfinity =
    (r.sum.id,r.prod.id,r.sum.id)) /\
  (sw_point_to_projective r (ECAffine x y) = (x,y,r.prod.id))
End

(* Total decoding is convenient, but only sw_projective_rep specifies valid
   curve representations; in particular (1,1,0) is not an infinity sentinel. *)
Definition sw_projective_to_point_def:
  sw_projective_to_point (r:'a field) (X,Y,Z) =
    if Z = r.sum.id then ECInfinity
    else ECAffine (r.prod.op X ((Invertibles r.prod).inv Z))
                  (r.prod.op Y ((Invertibles r.prod).inv Z))
End

Definition sw_projective_rep_def:
  sw_projective_rep (r:'a field) a b (X,Y,Z) P <=>
    sw_projective_valid r (X,Y,Z) /\
    (Z = r.sum.id ==> X = r.sum.id) /\
    sw_on_curve r a b P /\
    sw_projective_to_point r (X,Y,Z) = P
End

Definition sw_projective_on_curve_def:
  sw_projective_on_curve (r:'a field) a b (X,Y,Z) <=>
    sw_projective_valid r (X,Y,Z) /\
    r.prod.op (r.prod.exp Y 2) Z =
      r.sum.op
        (r.sum.op (r.prod.exp X 3)
          (r.prod.op (r.prod.op a X) (r.prod.exp Z 2)))
        (r.prod.op b (r.prod.exp Z 3))
End

Theorem sw_projective_rep_unique:
  sw_projective_rep (r:'a field) a b p P /\
  sw_projective_rep r a b p Q ==> P = Q
Proof
  PairCases_on `p` >> rw[sw_projective_rep_def] >> metis_tac[]
QED

Theorem sw_projective_rep_member:
  sw_projective_rep (r:'a field) a b p P ==> P IN sw_points r a b
Proof
  PairCases_on `p` >> simp[sw_projective_rep_def]
QED

Theorem sw_point_to_projective_valid:
  Field (r:'a field) /\ P IN sw_points r a b ==>
  sw_projective_valid r (sw_point_to_projective r P)
Proof
  Cases_on `P` >> rw[sw_point_to_projective_def, sw_projective_valid_def] >>
  metis_tac[field_zero_element, field_one_element, field_one_ne_zero]
QED

Theorem sw_point_projective_roundtrip:
  Field (r:'a field) /\ P IN sw_points r a b ==>
  sw_projective_to_point r (sw_point_to_projective r P) = P
Proof
  Cases_on `P` >>
  rw[sw_point_to_projective_def, sw_projective_to_point_def,
     field_inv_one, field_mult_rone, field_one_ne_zero]
QED

Theorem sw_point_to_projective_rep:
  Field (r:'a field) /\ P IN sw_points r a b ==>
  sw_projective_rep r a b (sw_point_to_projective r P) P
Proof
  Cases_on `P` >>
  rw[sw_point_to_projective_def, sw_projective_rep_def,
     sw_projective_valid_def, sw_projective_to_point_def,
     field_inv_one, field_mult_rone, field_one_ne_zero] >>
  metis_tac[field_zero_element, field_one_element, field_one_ne_zero]
QED

Theorem sw_projective_scale_valid:
  Field (r:'a field) /\ k IN r.carrier /\ k <> r.sum.id /\
  sw_projective_valid r p ==>
  sw_projective_valid r (sw_projective_scale r k p)
Proof
  PairCases_on `p` >>
  rw[sw_projective_valid_def, sw_projective_scale_def] >>
  metis_tac[field_mult_element, field_mult_eq_zero]
QED

Theorem sw_projective_scale_one[local]:
  Field (r:'a field) /\ sw_projective_valid r p ==>
  sw_projective_scale r r.prod.id p = p
Proof
  PairCases_on `p` >>
  simp[sw_projective_valid_def, sw_projective_scale_def, field_mult_lone]
QED

Theorem sw_projective_scale_compose[local]:
  Field (r:'a field) /\ sw_projective_valid r p /\
  k IN r.carrier /\ l IN r.carrier ==>
  sw_projective_scale r l (sw_projective_scale r k p) =
  sw_projective_scale r (r.prod.op l k) p
Proof
  PairCases_on `p` >>
  simp[sw_projective_valid_def, sw_projective_scale_def, field_mult_assoc]
QED

Theorem sw_projective_equiv_refl:
  Field (r:'a field) /\ sw_projective_valid r p ==>
  sw_projective_equiv r p p
Proof
  rw[sw_projective_equiv_def] >>
  qexists_tac `r.prod.id` >>
  simp[field_one_element, field_one_ne_zero, sw_projective_scale_one]
QED

Theorem sw_projective_equiv_sym:
  Field (r:'a field) /\ sw_projective_equiv r p q ==>
  sw_projective_equiv r q p
Proof
  rw[sw_projective_equiv_def] >>
  qexists_tac `(Invertibles r.prod).inv k` >>
  `k IN R+` by simp[field_nonzero_eq] >>
  simp[field_inv_element, field_inv_not_zero] >>
  metis_tac[sw_projective_scale_compose, sw_projective_scale_one,
            field_mult_linv, field_inv_element]
QED

Theorem sw_projective_equiv_trans:
  Field (r:'a field) /\ sw_projective_equiv r p q /\
  sw_projective_equiv r q s ==> sw_projective_equiv r p s
Proof
  rw[sw_projective_equiv_def] >>
  qexists_tac `r.prod.op k' k` >>
  metis_tac[field_mult_element, field_mult_eq_zero,
            sw_projective_scale_compose]
QED

Theorem sw_projective_ratio_scale[local]:
  Field (r:'a field) /\ x IN r.carrier /\ z IN r.carrier /\
  z <> r.sum.id /\ k IN r.carrier /\ k <> r.sum.id ==>
  r.prod.op (r.prod.op k x) ((Invertibles r.prod).inv (r.prod.op k z)) =
  r.prod.op x ((Invertibles r.prod).inv z)
Proof
  rpt strip_tac >>
  `k IN R+ /\ z IN R+` by simp[field_nonzero_eq] >>
  metis_tac[field_div_cancel, field_div_def]
QED

Theorem sw_projective_to_point_scale:
  Field (r:'a field) /\ sw_projective_valid r p /\
  k IN r.carrier /\ k <> r.sum.id ==>
  sw_projective_to_point r (sw_projective_scale r k p) =
  sw_projective_to_point r p
Proof
  PairCases_on `p` >>
  rw[sw_projective_valid_def, sw_projective_scale_def,
     sw_projective_to_point_def] >>
  metis_tac[field_mult_eq_zero, sw_projective_ratio_scale]
QED

Theorem sw_projective_mult_shuffle[local]:
  Field (r:'a field) /\ x IN r.carrier /\ t IN r.carrier /\
  w IN r.carrier ==>
  r.prod.op (r.prod.op x t) w = r.prod.op (r.prod.op w t) x
Proof
  rpt strip_tac >>
  simp[field_mult_assoc, field_mult_comm, field_mult_assoc_comm,
       field_mult_element]
QED

Theorem sw_projective_ratio_recover[local]:
  Field (r:'a field) /\
  x IN r.carrier /\ z IN r.carrier /\ z <> r.sum.id /\
  u IN r.carrier /\ w IN r.carrier /\ w <> r.sum.id /\
  r.prod.op x ((Invertibles r.prod).inv z) =
  r.prod.op u ((Invertibles r.prod).inv w) ==>
  u = r.prod.op (r.prod.op w ((Invertibles r.prod).inv z)) x
Proof
  rpt strip_tac >>
  `z IN R+ /\ w IN R+` by simp[field_nonzero_eq] >>
  `(Invertibles r.prod).inv z IN r.carrier` by
    metis_tac[field_inv_element] >>
  `r.prod.op x ((Invertibles r.prod).inv z) IN r.carrier` by
    metis_tac[field_mult_element] >>
  `u = r.prod.op (r.prod.op x ((Invertibles r.prod).inv z)) w` by
    metis_tac[field_mult_rinv_eqn] >>
  metis_tac[sw_projective_mult_shuffle]
QED

Theorem sw_projective_equiv_iff_to_point:
  !(r:'a field) x y z u v w.
  Field r /\
  sw_projective_valid r (x,y,z) /\
  sw_projective_valid r (u,v,w) /\
  (z = r.sum.id ==> x = r.sum.id) /\
  (w = r.sum.id ==> u = r.sum.id) ==>
  (sw_projective_equiv r (x,y,z) (u,v,w) <=>
   sw_projective_to_point r (x,y,z) =
   sw_projective_to_point r (u,v,w))
Proof
  rpt strip_tac >> eq_tac
  >- (rw[sw_projective_equiv_def] >>
      metis_tac[sw_projective_to_point_scale]) >>
  strip_tac >>
  Cases_on `z = r.sum.id`
  >- (
    `w = r.sum.id` by
      (Cases_on `w = r.sum.id` >> fs[sw_projective_to_point_def]) >>
    `x = r.sum.id /\ u = r.sum.id` by simp[] >>
    fs[sw_projective_valid_def] >>
    rw[sw_projective_equiv_def, sw_projective_valid_def] >>
    qexists_tac `r.prod.op v ((Invertibles r.prod).inv y)` >>
    `y IN R+` by simp[field_nonzero_eq] >>
    `(Invertibles r.prod).inv y IN r.carrier /\
     (Invertibles r.prod).inv y <> r.sum.id` by
      metis_tac[field_inv_element, field_inv_not_zero] >>
    simp[sw_projective_scale_def, field_mult_element,
         field_mult_eq_zero, field_mult_rzero] >>
    metis_tac[field_mult_rinv_assoc, field_mult_comm]) >>
  `w <> r.sum.id` by
    (Cases_on `w = r.sum.id` >> fs[sw_projective_to_point_def]) >>
  fs[sw_projective_to_point_def, sw_projective_valid_def] >>
  rw[sw_projective_equiv_def, sw_projective_valid_def] >>
  qexists_tac `r.prod.op w ((Invertibles r.prod).inv z)` >>
  `z IN R+` by simp[field_nonzero_eq] >>
  `(Invertibles r.prod).inv z IN r.carrier /\
   (Invertibles r.prod).inv z <> r.sum.id` by
    metis_tac[field_inv_element, field_inv_not_zero] >>
  simp[sw_projective_scale_def, field_mult_element, field_mult_eq_zero] >>
  rpt conj_tac >| [
    irule sw_projective_ratio_recover >> ASM_REWRITE_TAC [],
    irule sw_projective_ratio_recover >> ASM_REWRITE_TAC [],
    metis_tac[field_mult_rinv_assoc]
  ]
QED

Theorem sw_projective_rep_infinity:
  Field (r:'a field) ==>
  (sw_projective_rep r a b (x,y,z) ECInfinity <=>
   x = r.sum.id /\ z = r.sum.id /\
   y IN r.carrier /\ y <> r.sum.id)
Proof
  strip_tac >> Cases_on `z = r.sum.id` >>
  simp[sw_projective_rep_def, sw_projective_valid_def,
       sw_projective_to_point_def] >>
  metis_tac[field_zero_element]
QED

Theorem sw_projective_rep_affine:
  sw_projective_rep (r:'a field) a b (x,y,z) (ECAffine u v) <=>
  x IN r.carrier /\ y IN r.carrier /\ z IN r.carrier /\
  z <> r.sum.id /\ sw_on_curve r a b (ECAffine u v) /\
  u = r.prod.op x ((Invertibles r.prod).inv z) /\
  v = r.prod.op y ((Invertibles r.prod).inv z)
Proof
  Cases_on `z = r.sum.id` >>
  simp[sw_projective_rep_def, sw_projective_valid_def,
       sw_projective_to_point_def] >>
  metis_tac[]
QED

Theorem sw_projective_rep_scale:
  Field (r:'a field) /\ k IN r.carrier /\ k <> r.sum.id /\
  sw_projective_rep r a b p P ==>
  sw_projective_rep r a b (sw_projective_scale r k p) P
Proof
  PairCases_on `p` >> strip_tac >>
  `sw_projective_valid r (p0,p1,p2)` by fs[sw_projective_rep_def] >>
  `sw_projective_valid r (sw_projective_scale r k (p0,p1,p2))` by
    metis_tac[sw_projective_scale_valid] >>
  `sw_projective_to_point r (sw_projective_scale r k (p0,p1,p2)) =
   sw_projective_to_point r (p0,p1,p2)` by
    metis_tac[sw_projective_to_point_scale] >>
  fs[sw_projective_rep_def, sw_projective_scale_def,
     sw_projective_valid_def] >>
  metis_tac[field_mult_eq_zero, field_mult_rzero]
QED

Theorem sw_projective_rep_equiv:
  Field (r:'a field) /\ sw_projective_equiv r p q /\
  sw_projective_rep r a b p P ==> sw_projective_rep r a b q P
Proof
  rw[sw_projective_equiv_def] >> metis_tac[sw_projective_rep_scale]
QED

Theorem sw_projective_reps_equiv:
  Field (r:'a field) /\
  sw_projective_rep r a b p P /\ sw_projective_rep r a b q Q ==>
  (sw_projective_equiv r p q <=> P = Q)
Proof
  PairCases_on `p` >> PairCases_on `q` >>
  rw[sw_projective_rep_def] >>
  metis_tac[sw_projective_equiv_iff_to_point]
QED

Theorem sw_projective_point_roundtrip:
  Field (r:'a field) /\ sw_projective_rep r a b p P ==>
  sw_projective_equiv r p (sw_point_to_projective r P)
Proof
  metis_tac[sw_projective_reps_equiv, sw_point_to_projective_rep,
            sw_projective_rep_member]
QED

Theorem sw_projective_chart_algebra[local]:
  !(r:'a Ring) a b X Y Z i.
    a IN ring_carrier r /\ b IN ring_carrier r /\
    X IN ring_carrier r /\ Y IN ring_carrier r /\
    Z IN ring_carrier r /\ i IN ring_carrier r /\
    ring_mul r Z i = ring_1 r ==>
    (ring_mul r (ring_pow r Y 2) Z =
       ring_add r (ring_add r (ring_pow r X 3)
         (ring_mul r (ring_mul r a X) (ring_pow r Z 2)))
         (ring_mul r b (ring_pow r Z 3)) <=>
     ring_pow r (ring_mul r Y i) 2 =
       ring_add r (ring_add r (ring_pow r (ring_mul r X i) 3)
         (ring_mul r a (ring_mul r X i))) b)
Proof
  rpt strip_tac >> eq_tac >> strip_tac >> ringLib.RING_TAC
QED

Theorem sw_projective_finite_chart:
  !(r:'a field) a b x y z.
  Field (r:'a field) /\
  a IN r.carrier /\ b IN r.carrier /\
  x IN r.carrier /\ y IN r.carrier /\ z IN r.carrier /\
  z <> r.sum.id ==>
  (sw_projective_on_curve r a b (x,y,z) <=>
   sw_on_curve r a b (sw_projective_to_point r (x,y,z)))
Proof
  rpt strip_tac >>
  `z IN R+` by simp[field_nonzero_eq] >>
  `(Invertibles r.prod).inv z IN r.carrier` by
    metis_tac[field_inv_element] >>
  `r.prod.op z ((Invertibles r.prod).inv z) = r.prod.id` by
    metis_tac[field_mult_rinv] >>
  mp_tac (Q.SPECL [`toRing r`,`a`,`b`,`x`,`y`,`z`,
                  `(Invertibles r.prod).inv z`]
    sw_projective_chart_algebra) >>
  asm_simp_tac std_ss [sw_ring_ops] >>
  simp[sw_projective_on_curve_def, sw_projective_valid_def,
       sw_projective_to_point_def, sw_on_curve_def, sw_curve_rhs_def,
       field_mult_element]
QED

Theorem sw_projective_zero_chart:
  !(r:'a field) a b x y.
  Field (r:'a field) /\ a IN r.carrier /\ b IN r.carrier ==>
  (sw_projective_on_curve r a b (x,y,r.sum.id) <=>
   x = r.sum.id /\ y IN r.carrier /\ y <> r.sum.id)
Proof
  rpt strip_tac >>
  simp[sw_projective_on_curve_def, sw_projective_valid_def] >>
  eq_tac
  >- (rpt strip_tac >>
      `r.prod.exp x 3 = r.sum.id` by
        (qpat_x_assum `r.prod.op _ _ = _` mp_tac >>
         asm_simp_tac std_ss [field_mult_rzero, field_zero_exp,
           field_add_rzero, field_exp_element, field_mult_element] >>
         metis_tac[]) >>
      `x = r.sum.id` by
        metis_tac[field_exp_eq_zero, DECIDE ``(3:num) <> 0``] >>
      fs[]) >>
  strip_tac >> fs[field_zero_element,
    field_zero_exp, field_mult_rzero, field_mult_lzero,
    field_add_lzero, field_add_rzero, field_exp_element]
QED

Theorem sw_projective_curve_iff_rep:
  Field (r:'a field) /\ a IN r.carrier /\ b IN r.carrier ==>
  (sw_projective_on_curve r a b p <=>
   sw_projective_rep r a b p (sw_projective_to_point r p))
Proof
  rpt strip_tac >>
  PairCases_on `p` >>
  Cases_on `p2 = r.sum.id`
  >- (fs[sw_projective_zero_chart, sw_projective_rep_def,
         sw_projective_valid_def, sw_projective_to_point_def,
         sw_on_curve_def, field_zero_element] >>
      metis_tac[field_zero_element]) >>
  simp[sw_projective_rep_def] >>
  eq_tac
  >- (strip_tac >>
      `sw_projective_valid r (p0,p1,p2)` by
        fs[sw_projective_on_curve_def] >>
      fs[sw_projective_valid_def] >>
      metis_tac[sw_projective_finite_chart]) >>
  strip_tac >>
  fs[sw_projective_valid_def] >>
  metis_tac[sw_projective_finite_chart]
QED

Theorem sw_projective_rep_iff_curve:
  Field (r:'a field) /\ a IN r.carrier /\ b IN r.carrier ==>
  (sw_projective_rep r a b p P <=>
   sw_projective_on_curve r a b p /\ sw_projective_to_point r p = P)
Proof
  rpt strip_tac >>
  PairCases_on `p` >>
  mp_tac (Q.INST [`p` |-> `(p0,p1,p2)`] sw_projective_curve_iff_rep) >>
  asm_simp_tac std_ss [sw_projective_rep_def] >>
  metis_tac[]
QED

Theorem sw_projective_rep_exists:
  Field (r:'a field) /\ a IN r.carrier /\ b IN r.carrier ==>
  ((?P. sw_projective_rep r a b p P) <=> sw_projective_on_curve r a b p)
Proof
  metis_tac[sw_projective_curve_iff_rep, sw_projective_rep_iff_curve]
QED

Theorem sw_projective_on_curve_equiv:
  Field (r:'a field) /\ a IN r.carrier /\ b IN r.carrier /\
  sw_projective_equiv r p q ==>
  (sw_projective_on_curve r a b p <=> sw_projective_on_curve r a b q)
Proof
  rpt strip_tac >> eq_tac >> strip_tac >>
  metis_tac[sw_projective_curve_iff_rep, sw_projective_rep_iff_curve,
            sw_projective_rep_equiv, sw_projective_equiv_sym]
QED

Theorem sw_projective_on_curve_scale:
  Field (r:'a field) /\ a IN r.carrier /\ b IN r.carrier /\
  sw_projective_valid r p /\ k IN r.carrier /\ k <> r.sum.id ==>
  (sw_projective_on_curve r a b (sw_projective_scale r k p) <=>
   sw_projective_on_curve r a b p)
Proof
  strip_tac >>
  `sw_projective_equiv r p (sw_projective_scale r k p)` by
    (simp[sw_projective_equiv_def, sw_projective_scale_valid] >>
     qexists_tac `k` >> simp[]) >>
  metis_tac[sw_projective_on_curve_equiv]
QED
