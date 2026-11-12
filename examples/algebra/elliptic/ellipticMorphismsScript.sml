(* ------------------------------------------------------------------------- *)
(* Curve Maps Induced by Field Maps                                          *)
(* ------------------------------------------------------------------------- *)
(*
   Documentation

   sw_map_point_def applies a coefficient-field map to both affine coordinates
   and fixes ECInfinity. Field homomorphisms transport the curve with
   coefficients a,b to the curve with coefficients f a,f b.

   Field-map transport:
     sw_field_homo_curve, sw_field_homo_points, sw_field_homo_add,
       sw_field_homo_group.
     sw_field_iso_points_bij, sw_field_iso_group.
     sw_field_endo_group        Coefficient-fixing field endomorphisms.
   Group-map consequences:
     sw_curve_homo_scalar, sw_curve_endo_scalar, sw_curve_iso_order.
     sw_curve_homo_torsion, sw_curve_iso_torsion, sw_field_iso_torsion.

   Theorems carry the source curve and target field hypotheses explicitly.
   A field inclusion need not cover all rational points over the larger
   field; the group-isomorphism results require FieldIso, not just FieldHomo.
*)

Theory ellipticMorphisms
Ancestors
  shortWeierstrass shortWeierstrassGroup ellipticTorsion fieldMap

open fieldTheory fieldMapTheory ringTheory groupTheory pred_setTheory

Definition sw_map_point_def:
  (sw_map_point f ECInfinity = ECInfinity) /\
  (sw_map_point f (ECAffine x y) = ECAffine (f x) (f y))
End

Theorem sw_map_point_id[simp]:
  sw_map_point I P = P
Proof
  Cases_on `P` >> simp[sw_map_point_def]
QED

Theorem sw_map_point_comp:
  sw_map_point (g o f) P = sw_map_point g (sw_map_point f P)
Proof
  Cases_on `P` >> simp[sw_map_point_def]
QED

Theorem sw_map_point_inj:
  INJ f r.carrier s.carrier ==>
  !P Q. P IN sw_points r a b /\ Q IN sw_points r a b ==>
    (sw_map_point f P = sw_map_point f Q <=> P = Q)
Proof
  strip_tac >> Cases_on `P` >> Cases_on `Q` >>
  simp[sw_map_point_def, sw_points_member, sw_on_curve_def] >>
  fs[INJ_DEF] >> metis_tac[]
QED

Theorem sw_field_homo_char[local]:
  Field (r:'a field) /\ Field (s:'b field) /\ FieldHomo f r s ==>
  char s = char r
Proof
  metis_tac[field_homo_image_iso, ring_homo_image_field,
            field_iso_char_eq, field_homo_subfield, subfield_char]
QED

Theorem sw_field_homo_operations[local]:
  Field (r:'a field) /\ Field (s:'b field) /\ FieldHomo f r s ==>
  (!x y. x IN r.carrier /\ y IN r.carrier ==>
    f (r.sum.op x y) = s.sum.op (f x) (f y)) /\
  (!x y. x IN r.carrier /\ y IN r.carrier ==>
    f (r.prod.op x y) = s.prod.op (f x) (f y)) /\
  (!x. x IN r.carrier ==> f (r.sum.inv x) = s.sum.inv (f x)) /\
  (!x n. x IN r.carrier ==> f (r.prod.exp x n) = s.prod.exp (f x) n) /\
  (!n. f (r.sum.exp r.prod.id n) = s.sum.exp s.prod.id n)
Proof
  strip_tac >>
  map_every (assume_tac o Q.SPECL [`r`, `s`, `f`])
    [field_homo_add, field_homo_mult, field_homo_neg,
     field_homo_exp, field_homo_num] >>
  fs[]
QED

Theorem sw_field_homo_rhs:
  Field (r:'a field) /\ Field (s:'b field) /\ FieldHomo f r s /\
  a IN r.carrier /\ b IN r.carrier /\ x IN r.carrier ==>
  f (sw_curve_rhs r a b x) = sw_curve_rhs s (f a) (f b) (f x)
Proof
  strip_tac >> drule_all sw_field_homo_operations >> strip_tac >>
  rw[sw_curve_rhs_def, field_add_element, field_mult_element,
     field_exp_element]
QED

Theorem sw_field_homo_discriminant:
  Field (r:'a field) /\ Field (s:'b field) /\ FieldHomo f r s /\
  a IN r.carrier /\ b IN r.carrier ==>
  f (sw_discriminant r a b) = sw_discriminant s (f a) (f b)
Proof
  strip_tac >> drule_all sw_field_homo_operations >> strip_tac >>
  `r.prod.op (r.sum.exp r.prod.id 16)
     (r.sum.op (r.prod.op (r.sum.exp r.prod.id 4) (r.prod.exp a 3))
       (r.prod.op (r.sum.exp r.prod.id 27) (r.prod.exp b 2)))
     IN r.carrier` by
    ASM_SIMP_TAC bool_ss [field_add_element, field_mult_element,
                         field_exp_element, field_num_element] >>
  ASM_SIMP_TAC bool_ss
    [sw_discriminant_def, field_add_element, field_mult_element,
     field_exp_element, field_num_element]
QED

Theorem sw_field_homo_curve:
  ShortWeierstrassCurve (r:'a field) a b /\ Field (s:'b field) /\
  FieldHomo f r s ==> ShortWeierstrassCurve s (f a) (f b)
Proof
  rw[ShortWeierstrassCurve_def] >-
    metis_tac[field_homo_element] >-
    metis_tac[field_homo_element] >-
    metis_tac[sw_field_homo_char] >-
    metis_tac[sw_field_homo_char] >>
  `sw_discriminant r a b IN r.carrier` by
    (simp_tac bool_ss [sw_discriminant_def] >>
     irule field_neg_element >>
     ASM_SIMP_TAC bool_ss [field_mult_element, field_add_element,
                          field_num_element, field_exp_element]) >>
  metis_tac[sw_field_homo_discriminant, field_homo_eq_zero]
QED

Theorem sw_field_iso_curve:
  ShortWeierstrassCurve (r:'a field) a b /\ Field (s:'b field) /\
  FieldIso f r s ==> ShortWeierstrassCurve s (f a) (f b)
Proof
  metis_tac[FieldIso_def, sw_field_homo_curve]
QED

Theorem sw_field_homo_on_curve:
  Field (r:'a field) /\ Field (s:'b field) /\ FieldHomo f r s /\
  a IN r.carrier /\ b IN r.carrier /\ sw_on_curve r a b P ==>
  sw_on_curve s (f a) (f b) (sw_map_point f P)
Proof
  Cases_on `P` >- simp[sw_map_point_def, sw_on_curve_def] >>
  rename1 `sw_on_curve r a b (ECAffine x y)` >>
  rw[sw_map_point_def, sw_on_curve_def] >-
    metis_tac[field_homo_element] >-
    metis_tac[field_homo_element] >>
  `f (r.prod.exp y 2) = s.prod.exp (f y) 2` by
    (mp_tac (Q.SPECL [`r`, `s`, `f`] field_homo_exp) >> simp[]) >>
  `f (sw_curve_rhs r a b x) = sw_curve_rhs s (f a) (f b) (f x)` by
    (irule sw_field_homo_rhs >> simp[]) >>
  metis_tac[]
QED

Theorem sw_field_homo_points:
  ShortWeierstrassCurve (r:'a field) a b /\ Field (s:'b field) /\
  FieldHomo f r s /\ P IN sw_points r a b ==>
  sw_map_point f P IN sw_points s (f a) (f b)
Proof
  metis_tac[ShortWeierstrassCurve_def, sw_points_member,
            sw_field_homo_on_curve]
QED

Theorem sw_field_homo_neg:
  Field (r:'a field) /\ Field (s:'b field) /\ FieldHomo f r s /\
  P IN sw_points r a b ==>
  sw_map_point f (sw_neg r P) = sw_neg s (sw_map_point f P)
Proof
  Cases_on `P` >> rw[sw_map_point_def, sw_neg_def] >>
  fs[sw_points_member, sw_on_curve_def] >>
  metis_tac[field_homo_neg]
QED

Theorem sw_field_homo_prod_inv[local]:
  Field (r:'a field) /\ Field (s:'b field) /\ FieldHomo f r s /\
  x IN r.carrier /\ x <> r.sum.id ==>
  f (r.prod.inv x) = s.prod.inv (f x)
Proof
  rpt strip_tac >>
  `f x IN s.carrier /\ f x <> s.sum.id` by
    metis_tac[field_homo_element, field_homo_eq_zero] >>
  `x IN R+` by rw[field_nonzero_eq] >>
  metis_tac[sw_field_prod_inv_eq, field_homo_inv]
QED

Theorem sw_field_homo_add_x[local]:
  Field (r:'a field) /\ Field (s:'b field) /\ FieldHomo f r s /\
  m IN r.carrier /\ x IN r.carrier /\ z IN r.carrier ==>
  f (sw_add_x r m x z) = sw_add_x s (f m) (f x) (f z)
Proof
  strip_tac >> drule_all sw_field_homo_operations >> strip_tac >>
  rw[sw_add_x_def, field_add_element, field_neg_element,
     field_exp_element]
QED

Theorem sw_field_homo_add_y[local]:
  Field (r:'a field) /\ Field (s:'b field) /\ FieldHomo f r s /\
  m IN r.carrier /\ x IN r.carrier /\ y IN r.carrier /\
  z IN r.carrier ==>
  f (sw_add_y r m x y z) = sw_add_y s (f m) (f x) (f y) (f z)
Proof
  strip_tac >> drule_all sw_field_homo_operations >> strip_tac >>
  `r.prod.op m (r.sum.op x (r.sum.inv z)) IN r.carrier` by
    ASM_SIMP_TAC bool_ss
      [field_add_element, field_neg_element, field_mult_element] >>
  ASM_SIMP_TAC bool_ss
    [sw_add_y_def, field_add_element, field_neg_element, field_mult_element]
QED

Theorem sw_field_homo_slope[local]:
  ShortWeierstrassCurve (r:'a field) a b /\ Field (s:'b field) /\
  FieldHomo f r s /\
  sw_on_curve r a b (ECAffine x1 y1) /\
  sw_on_curve r a b (ECAffine x2 y2) /\
  ~(x1 = x2 /\ y1 = r.sum.inv y2) ==>
  sw_slope r a x1 y1 x2 y2 IN r.carrier /\
  f (sw_slope r a x1 y1 x2 y2) =
    sw_slope s (f a) (f x1) (f y1) (f x2) (f y2)
Proof
  strip_tac >>
  `Field r /\ a IN r.carrier /\ b IN r.carrier /\
   x1 IN r.carrier /\ y1 IN r.carrier /\
   x2 IN r.carrier /\ y2 IN r.carrier` by
    metis_tac[ShortWeierstrassCurve_def, sw_on_curve_def] >>
  `f x1 = f x2 <=> x1 = x2` by
    metis_tac[field_homo_map_inj, INJ_DEF] >>
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
    `r.sum.op
       (r.prod.op (r.sum.exp r.prod.id 3) (r.prod.exp x1 2)) a
       IN r.carrier` by
      ASM_SIMP_TAC bool_ss [field_add_element, field_mult_element,
                           field_num_element, field_exp_element] >>
    drule_all sw_field_prod_inv >> strip_tac >>
    drule_all sw_field_homo_prod_inv >> strip_tac >>
    drule_all sw_field_homo_operations >> strip_tac >>
    ASM_SIMP_TAC bool_ss
      [sw_slope_def, field_mult_element, field_add_element,
       field_num_element, field_exp_element],
    `r.sum.op x2 (r.sum.inv x1) IN r.carrier /\
     r.sum.op x2 (r.sum.inv x1) <> r.sum.id` by
      metis_tac[field_add_element, field_neg_element,
                field_add_eq_zero, field_neg_neg] >>
    drule_all sw_field_prod_inv >> strip_tac >>
    drule_all sw_field_homo_prod_inv >> strip_tac >>
    drule_all sw_field_homo_operations >> strip_tac >>
    ASM_SIMP_TAC bool_ss
      [sw_slope_def, field_mult_element, field_add_element,
       field_neg_element]
  ]
QED

Theorem sw_field_homo_add:
  ShortWeierstrassCurve (r:'a field) a b /\ Field (s:'b field) /\
  FieldHomo f r s /\ P IN sw_points r a b /\ Q IN sw_points r a b ==>
  sw_map_point f (sw_add r a b P Q) =
    sw_add s (f a) (f b) (sw_map_point f P) (sw_map_point f Q)
Proof
  Cases_on `P` >- simp[sw_map_point_def, sw_add_def] >>
  Cases_on `Q` >- simp[sw_map_point_def, sw_add_def] >>
  rename1 `sw_add r a b (ECAffine x1 y1) (ECAffine x2 y2)` >>
  strip_tac >>
  `Field r /\ a IN r.carrier /\ b IN r.carrier /\
   x1 IN r.carrier /\ y1 IN r.carrier /\
   x2 IN r.carrier /\ y2 IN r.carrier` by
    metis_tac[ShortWeierstrassCurve_def, sw_points_member, sw_on_curve_def] >>
  `INJ f r.carrier s.carrier` by metis_tac[field_homo_map_inj] >>
  `r.sum.inv y2 IN r.carrier /\
   f (r.sum.inv y2) = s.sum.inv (f y2)` by
    metis_tac[field_neg_element, field_homo_neg] >>
  `(f x1 = f x2 /\ f y1 = s.sum.inv (f y2)) <=>
   (x1 = x2 /\ y1 = r.sum.inv y2)` by
    (fs[INJ_DEF] >> metis_tac[]) >>
  Cases_on `x1 = x2 /\ y1 = r.sum.inv y2` >-
    (`f x1 = f x2 /\ f y1 = s.sum.inv (f y2)` by metis_tac[] >>
     ASM_SIMP_TAC bool_ss [sw_add_def, sw_map_point_def]) >>
  `~(f x1 = f x2 /\ f y1 = s.sum.inv (f y2))` by metis_tac[] >>
  `sw_slope r a x1 y1 x2 y2 IN r.carrier /\
   f (sw_slope r a x1 y1 x2 y2) =
   sw_slope s (f a) (f x1) (f y1) (f x2) (f y2)` by
    (mp_tac sw_field_homo_slope >> fs[sw_points_member]) >>
  `sw_add_x r (sw_slope r a x1 y1 x2 y2) x1 x2 IN r.carrier` by
    rw[sw_add_x_def, field_add_element, field_neg_element,
       field_exp_element] >>
  `f (sw_add_x r (sw_slope r a x1 y1 x2 y2) x1 x2) =
   sw_add_x s (f (sw_slope r a x1 y1 x2 y2)) (f x1) (f x2)` by
    (irule sw_field_homo_add_x >> simp[]) >>
  `f (sw_add_y r (sw_slope r a x1 y1 x2 y2) x1 y1
       (sw_add_x r (sw_slope r a x1 y1 x2 y2) x1 x2)) =
   sw_add_y s (f (sw_slope r a x1 y1 x2 y2)) (f x1) (f y1)
     (f (sw_add_x r (sw_slope r a x1 y1 x2 y2) x1 x2))` by
    (irule sw_field_homo_add_y >> simp[]) >>
  ASM_SIMP_TAC bool_ss [sw_add_def, sw_map_point_def, LET_THM]
QED

Theorem sw_field_homo_group:
  ShortWeierstrassCurve (r:'a field) a b /\ Field (s:'b field) /\
  FieldHomo f r s ==>
  GroupHomo (sw_map_point f) (sw_group r a b) (sw_group s (f a) (f b))
Proof
  strip_tac >>
  simp_tac bool_ss [GroupHomo_def, sw_group_carrier, sw_group_op] >>
  conj_tac >- metis_tac[sw_field_homo_points] >>
  rpt strip_tac >> irule sw_field_homo_add >> ASM_SIMP_TAC bool_ss []
QED

Theorem sw_field_homo_affine_iff:
  Field (r:'a field) /\ Field (s:'b field) /\ FieldHomo f r s /\
  a IN r.carrier /\ b IN r.carrier /\
  x IN r.carrier /\ y IN r.carrier ==>
  (sw_on_curve s (f a) (f b) (ECAffine (f x) (f y)) <=>
   sw_on_curve r a b (ECAffine x y))
Proof
  strip_tac >>
  `f x IN s.carrier /\ f y IN s.carrier` by
    metis_tac[field_homo_element] >>
  `sw_curve_rhs r a b x IN r.carrier /\ r.prod.exp y 2 IN r.carrier` by
    rw[sw_curve_rhs_def, field_add_element, field_mult_element,
       field_exp_element] >>
  `f (r.prod.exp y 2) = s.prod.exp (f y) 2` by
    (mp_tac (Q.SPECL [`r`, `s`, `f`] field_homo_exp) >> simp[]) >>
  `f (sw_curve_rhs r a b x) = sw_curve_rhs s (f a) (f b) (f x)` by
    (irule sw_field_homo_rhs >> simp[]) >>
  rw[sw_on_curve_def] >>
  metis_tac[field_homo_map_inj, INJ_DEF]
QED

Theorem sw_field_iso_points_bij:
  ShortWeierstrassCurve (r:'a field) a b /\ Field (s:'b field) /\
  FieldIso f r s ==>
  BIJ (sw_map_point f) (sw_points r a b) (sw_points s (f a) (f b))
Proof
  strip_tac >>
  `Field r /\ a IN r.carrier /\ b IN r.carrier /\ FieldHomo f r s` by
    metis_tac[ShortWeierstrassCurve_def, FieldIso_def] >>
  simp_tac bool_ss [BIJ_DEF, INJ_DEF, SURJ_DEF] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >-
    metis_tac[sw_field_homo_points] >-
    metis_tac[sw_map_point_inj, field_homo_map_inj] >-
    metis_tac[sw_field_homo_points] >>
  rename1 `Q IN sw_points s (f a) (f b)` >>
  Cases_on `Q` >-
    (qexists_tac `ECInfinity` >> simp[sw_map_point_def]) >>
  rename1 `ECAffine u v` >>
  `u IN s.carrier /\ v IN s.carrier` by
    metis_tac[sw_points_member, sw_on_curve_def] >>
  `?x. x IN r.carrier /\ u = f x` by metis_tac[field_iso_inverse] >>
  `?y. y IN r.carrier /\ v = f y` by metis_tac[field_iso_inverse] >>
  qexists_tac `ECAffine x y` >>
  ASM_SIMP_TAC bool_ss [sw_map_point_def] >>
  mp_tac sw_field_homo_affine_iff >> fs[sw_points_member]
QED

Theorem sw_field_iso_group:
  ShortWeierstrassCurve (r:'a field) a b /\ Field (s:'b field) /\
  FieldIso f r s ==>
  GroupIso (sw_map_point f) (sw_group r a b) (sw_group s (f a) (f b))
Proof
  rw[GroupIso_def, sw_group_carrier] >-
    metis_tac[sw_field_homo_group, FieldIso_def] >>
  metis_tac[sw_field_iso_points_bij]
QED

Theorem sw_curve_homo_scalar:
  ShortWeierstrassCurve (r:'a field) a b /\
  ShortWeierstrassCurve (s:'b field) c d /\
  GroupHomo h (sw_group r a b) (sw_group s c d) /\
  P IN sw_points r a b ==>
  h ((sw_group r a b).exp P n) = (sw_group s c d).exp (h P) n
Proof
  metis_tac[short_weierstrass_group, group_homo_exp, sw_group_carrier]
QED

Theorem sw_curve_iso_order:
  ShortWeierstrassCurve (r:'a field) a b /\
  ShortWeierstrassCurve (s:'b field) c d /\
  GroupIso h (sw_group r a b) (sw_group s c d) /\
  P IN sw_points r a b ==>
  order (sw_group s c d) (h P) = order (sw_group r a b) P
Proof
  metis_tac[short_weierstrass_group, group_iso_order, sw_group_carrier]
QED

Theorem sw_field_endo_group:
  ShortWeierstrassCurve (r:'a field) a b /\
  FieldEndo f r /\ f a = a /\ f b = b ==>
  GroupEndo (sw_map_point f) (sw_group r a b)
Proof
  metis_tac[FieldEndo_def, GroupEndo_def, ShortWeierstrassCurve_def,
            sw_field_homo_group]
QED

Theorem sw_curve_endo_scalar:
  ShortWeierstrassCurve (r:'a field) a b /\
  GroupEndo h (sw_group r a b) /\ P IN sw_points r a b ==>
  h ((sw_group r a b).exp P n) = (sw_group r a b).exp (h P) n
Proof
  metis_tac[GroupEndo_def, sw_curve_homo_scalar]
QED

Theorem sw_curve_homo_torsion:
  ShortWeierstrassCurve (r:'a field) a b /\
  ShortWeierstrassCurve (s:'b field) c d /\
  GroupHomo f (sw_group r a b) (sw_group s c d) ==>
  GroupHomo f (sw_torsion_group r a b n) (sw_torsion_group s c d n)
Proof
  strip_tac >>
  `Group (sw_group r a b) /\ Group (sw_group s c d)` by
    metis_tac[short_weierstrass_group] >>
  `f ECInfinity = ECInfinity` by
    metis_tac[group_homo_id, sw_group_id] >>
  SIMP_TAC bool_ss [GroupHomo_def, sw_torsion_member, sw_torsion_op] >>
  conj_tac >-
    metis_tac[group_homo_element, group_homo_exp, sw_group_carrier] >>
  rpt strip_tac >>
  FULL_SIMP_TAC bool_ss [GroupHomo_def, sw_group_carrier, sw_group_op]
QED

Theorem sw_curve_iso_torsion_reflect[local]:
  ShortWeierstrassCurve (r:'a field) a b /\
  ShortWeierstrassCurve (s:'b field) c d /\
  GroupIso f (sw_group r a b) (sw_group s c d) /\
  P IN sw_points r a b ==>
  (f P IN (sw_torsion_group s c d n).carrier <=>
   P IN (sw_torsion_group r a b n).carrier)
Proof
  strip_tac >>
  `f P IN sw_points s c d` by
    metis_tac[group_homo_element, GroupIso_def, sw_group_carrier] >>
  metis_tac[sw_curve_iso_order, sw_torsion_order]
QED

Theorem sw_curve_iso_torsion:
  ShortWeierstrassCurve (r:'a field) a b /\
  ShortWeierstrassCurve (s:'b field) c d /\
  GroupIso f (sw_group r a b) (sw_group s c d) ==>
  GroupIso f (sw_torsion_group r a b n) (sw_torsion_group s c d n)
Proof
  strip_tac >>
  `GroupHomo f (sw_group r a b) (sw_group s c d) /\
   BIJ f (sw_points r a b) (sw_points s c d)` by
    metis_tac[GroupIso_def, sw_group_carrier] >>
  SIMP_TAC bool_ss [GroupIso_def] >>
  conj_tac >- metis_tac[sw_curve_homo_torsion] >>
  FULL_SIMP_TAC bool_ss [BIJ_DEF, INJ_DEF, SURJ_DEF] >>
  metis_tac[sw_curve_iso_torsion_reflect, sw_torsion_member]
QED

Theorem sw_field_iso_torsion:
  ShortWeierstrassCurve (r:'a field) a b /\ Field (s:'b field) /\
  FieldIso f r s ==>
  GroupIso (sw_map_point f)
    (sw_torsion_group r a b n) (sw_torsion_group s (f a) (f b) n)
Proof
  strip_tac >> irule sw_curve_iso_torsion >>
  metis_tac[sw_field_iso_curve, sw_field_iso_group]
QED
