(* Injective twist embeddings into the degree-12 curve groups.

   Documentation
   A quadratic-to-degree-12 field inclusion is followed by Weierstrass
   coordinate scaling: by w for BN254 and inverse w for BLS12-381.
   The targets are y^2 = x^3 + 3 and y^2 = x^3 + 4 over the respective
   fp12 fields. Field and degree-12 certificate theories supply the
   algebraic premises for these concrete specializations.

   Definitions: bn254_fp12_curve_group_def, bls12381_fp12_curve_group_def,
   bn254_twist_embedding_def, bls12381_twist_embedding_def.
   For each prefix bn254_twist and bls12381_twist:
   Structure: *_embedding_group_homo, *_embedding_inj.
   On source-carrier points: *_embedding_scalar, *_embedding_order.
   Standard generators: *_embedded_generator_order.
   Target curves: bn254_fp12_curve, bls12381_fp12_curve.

   These maps are injective group homomorphisms, not surjections onto
   all extension-field rational points. No pairing function is defined. *)

Theory pairingTwistMorphisms
Ancestors
  namedPrimes
  namedPrimeFields fieldInstances pairingQuadraticFields pairingDegree12Fields
  bn254Degree12Certificate bls12381Degree12Certificate
  pairingFieldEmbeddings pairingTwistInstances ellipticScaling
  ellipticMorphisms polyMonic
Libs
  polynomialCertificateLib pairingFieldCertificateLib

open fieldTheory fieldMapTheory ringTheory groupTheory pred_setTheory
     polyModuloRingTheory shortWeierstrassTheory shortWeierstrassGroupTheory
     ellipticMorphismsTheory ellipticScalingTheory

Theorem injective_group_homo_order[local]:
  Group (g:'a group) /\ Group (h:'b group) /\ GroupHomo f g h /\
  INJ f g.carrier h.carrier /\ P IN g.carrier ==>
  order h (f P) = order g P
Proof
  strip_tac >>
  `f P IN h.carrier` by metis_tac[group_homo_element] >>
  `!n. h.exp (f P) n = h.id <=> g.exp P n = g.id` by
    (fs[INJ_DEF] >> metis_tac[group_homo_exp, group_homo_id,
                             group_exp_element, group_id_element]) >>
  irule dividesTheory.DIVIDES_ANTISYM >>
  metis_tac[group_order_divides_exp, monoidTheory.order_property]
QED

(* A field inclusion followed by a change of Weierstrass coordinates is a
   monomorphism, not a surjection onto all extension-field rational points. *)
Theorem sw_field_scale_monomorphism[local]:
  ShortWeierstrassCurve (r:'a field) a b /\ Field (s:'b field) /\
  FieldHomo f r s /\ u IN s.carrier /\ u <> s.sum.id /\
  c = s.prod.op (s.prod.exp u 4) (f a) /\
  d = s.prod.op (s.prod.exp u 6) (f b) ==>
  ShortWeierstrassCurve s c d /\
  GroupHomo (sw_scale_point s u o sw_map_point f)
    (sw_group r a b) (sw_group s c d) /\
  INJ (sw_scale_point s u o sw_map_point f)
    (sw_points r a b) (sw_points s c d)
Proof
  strip_tac >>
  `ShortWeierstrassCurve s (f a) (f b)` by
    metis_tac[sw_field_homo_curve] >>
  `ShortWeierstrassCurve s c d` by metis_tac[sw_scale_curve] >>
  `GroupHomo (sw_scale_point s u o sw_map_point f)
    (sw_group r a b) (sw_group s c d)` by
    metis_tac[sw_scale_group_homo, sw_field_homo_group, group_homo_compose] >>
  simp[] >>
  `Field r /\ INJ f r.carrier s.carrier` by
    metis_tac[ShortWeierstrassCurve_def, field_homo_map_inj] >>
  PURE_REWRITE_TAC [INJ_DEF] >> CONJ_TAC >-
    (rpt strip_tac >> metis_tac[group_homo_element, sw_group_carrier]) >>
  rpt strip_tac >>
  `sw_map_point f x IN sw_points s (f a) (f b) /\
   sw_map_point f y IN sw_points s (f a) (f b)` by
    metis_tac[sw_field_homo_points] >>
  `sw_map_point f x = sw_map_point f y` by
    metis_tac[sw_scale_inverse, combinTheory.o_THM] >>
  metis_tac[sw_map_point_inj]
QED

Definition bn254_fp12_curve_group_def:
  bn254_fp12_curve_group = sw_group bn254_fp12 [] [3]
End
Definition bls12381_fp12_curve_group_def:
  bls12381_fp12_curve_group = sw_group bls12381_fp12 [] [4]
End

Definition bn254_twist_embedding_def:
  bn254_twist_embedding =
    sw_scale_point bn254_fp12 bn254_fp12_w o
    sw_map_point bn254_fp2_to_fp12
End
Definition bls12381_twist_embedding_def:
  bls12381_twist_embedding =
    sw_scale_point bls12381_fp12 (bls12381_fp12.prod.inv bls12381_fp12_w) o
    sw_map_point bls12381_fp2_to_fp12
End

Theorem pairing_extension_fields[local]:
  Field bn254_fp2 /\ Field bn254_fp12 /\
  Field bls12381_fp2 /\ Field bls12381_fp12
Proof
  metis_tac[FiniteField_def, bn254_fp2_finite_field, bn254_fp12_finite_field,
            bls12381_fp2_finite_field, bls12381_fp12_finite_field]
QED

Theorem bn254_twist_a_image[local]:
  bn254_fp2_to_fp12 bn254_g2_a = bn254_fp12.sum.id
Proof
  REWRITE_TAC [bn254_g2_a_def, bn254_fp12_def,
               poly_mod_ring_ids, polynomialTheory.poly_zero] >>
  mp_tac (SPEC ``0n`` bn254_fp2_to_fp12_constant) >>
  simp[bn254_p_def]
QED
Theorem bls12381_twist_a_image[local]:
  bls12381_fp2_to_fp12 bls12381_g2_a = bls12381_fp12.sum.id
Proof
  REWRITE_TAC [bls12381_g2_a_def, bls12381_fp12_def,
               poly_mod_ring_ids, polynomialTheory.poly_zero] >>
  mp_tac (SPEC ``0n`` bls12381_fp2_to_fp12_constant) >>
  simp[bls12381_p_def]
QED

(* Multiplication of the embedded twist coefficient by w^6 is exactly 3.
   This checks the actual normalized 3/(9+i) constant of the curve theory. *)
Theorem bn254_twist_b_scaled:
  bn254_fp12.prod.op (bn254_fp12.prod.exp bn254_fp12_w 6)
    (bn254_fp2_to_fp12 bn254_g2_b) = [3]
Proof
  REWRITE_TAC [bn254_fp12_w_sixth, bn254_fp2_to_fp12_def,
               bn254_g2_b_def, bn254_fp12_i_def, bn254_fp12_def,
               bn254_fp12_poly_def, bn254_p_def] >>
  CONV_TAC (pairingFieldCertificateLib.QUOTIENT_CONV
    (REWRITE_RULE [bn254_p_def] bn254_p_prime)
    (rhs (concl (EVAL ``bn254_fp12_poly``))))
QED

Theorem bls12381_twist_b_image:
  bls12381_fp2_to_fp12 bls12381_g2_b =
    bls12381_fp12.prod.op (bls12381_fp12.prod.exp bls12381_fp12_w 6) [4]
Proof
  REWRITE_TAC [bls12381_fp12_w_sixth, bls12381_fp2_to_fp12_def,
               bls12381_g2_b_def, bls12381_fp12_i_def, bls12381_fp12_def,
               bls12381_fp12_poly_def, bls12381_p_def] >>
  CONV_TAC (pairingFieldCertificateLib.QUOTIENT_CONV
    (REWRITE_RULE [bls12381_p_def] bls12381_p_prime)
    (rhs (concl (EVAL ``bls12381_fp12_poly``))))
QED

Theorem bls12381_twist_b_scaled:
  bls12381_fp12.prod.op
    (bls12381_fp12.prod.exp (bls12381_fp12.prod.inv bls12381_fp12_w) 6)
    (bls12381_fp2_to_fp12 bls12381_g2_b) = [4]
Proof
  REWRITE_TAC [bls12381_twist_b_image] >>
  irule sw_scale_inverse_power >>
  simp[pairing_extension_fields, bls12381_fp12_w_member] >>
  REWRITE_TAC [bls12381_fp12_def, bls12381_fp12_poly_def,
               bls12381_p_def, poly_mod_ring_element] >>
  CONV_TAC polynomialCertificateLib.ARITH_CONV
QED

Theorem bls12381_fp12_inverse_w_member[local]:
  bls12381_fp12.prod.inv bls12381_fp12_w IN bls12381_fp12.carrier /\
  bls12381_fp12.prod.inv bls12381_fp12_w <> bls12381_fp12.sum.id
Proof
  `Field bls12381_fp12` by metis_tac[pairing_extension_fields] >>
  `bls12381_fp12.prod.inv bls12381_fp12_w IN bls12381_fp12.carrier /\
   bls12381_fp12.prod.op bls12381_fp12_w
      (bls12381_fp12.prod.inv bls12381_fp12_w) = bls12381_fp12.prod.id`
    by metis_tac[sw_field_prod_inv, bls12381_fp12_w_member] >>
  metis_tac[field_mult_rzero, field_one_ne_zero, bls12381_fp12_w_member]
QED

Theorem bn254_twist_monomorphism[local]:
  ShortWeierstrassCurve bn254_fp12 [] [3] /\
  GroupHomo bn254_twist_embedding bn254_g2_group bn254_fp12_curve_group /\
  INJ bn254_twist_embedding
    (sw_points bn254_fp2 bn254_g2_a bn254_g2_b)
    (sw_points bn254_fp12 [] [3])
Proof
  REWRITE_TAC [bn254_twist_embedding_def, bn254_g2_group_def,
               bn254_fp12_curve_group_def] >>
  irule sw_field_scale_monomorphism >>
  simp[pairing_extension_fields, bn254_g2_curve,
       bn254_fp2_to_fp12_field_homo, bn254_fp12_w_member,
       bn254_twist_a_image, bn254_twist_b_scaled,
       field_exp_element, field_mult_rzero] >>
  simp[bn254_fp12_def, poly_mod_ring_ids]
QED
Theorem bls12381_twist_monomorphism[local]:
  ShortWeierstrassCurve bls12381_fp12 [] [4] /\
  GroupHomo bls12381_twist_embedding bls12381_g2_group bls12381_fp12_curve_group /\
  INJ bls12381_twist_embedding
    (sw_points bls12381_fp2 bls12381_g2_a bls12381_g2_b)
    (sw_points bls12381_fp12 [] [4])
Proof
  REWRITE_TAC [bls12381_twist_embedding_def, bls12381_g2_group_def,
               bls12381_fp12_curve_group_def] >>
  irule sw_field_scale_monomorphism >>
  simp[pairing_extension_fields, bls12381_g2_curve,
       bls12381_fp2_to_fp12_field_homo, bls12381_fp12_inverse_w_member,
       bls12381_twist_a_image, bls12381_twist_b_scaled,
       field_exp_element, field_mult_rzero] >>
  simp[bls12381_fp12_def, poly_mod_ring_ids]
QED

Theorem bn254_fp12_curve:
  ShortWeierstrassCurve bn254_fp12 [] [3]
Proof
  metis_tac[bn254_twist_monomorphism]
QED
Theorem bls12381_fp12_curve:
  ShortWeierstrassCurve bls12381_fp12 [] [4]
Proof
  metis_tac[bls12381_twist_monomorphism]
QED
Theorem bn254_twist_embedding_group_homo:
  GroupHomo bn254_twist_embedding bn254_g2_group bn254_fp12_curve_group
Proof
  metis_tac[bn254_twist_monomorphism]
QED
Theorem bls12381_twist_embedding_group_homo:
  GroupHomo bls12381_twist_embedding bls12381_g2_group bls12381_fp12_curve_group
Proof
  metis_tac[bls12381_twist_monomorphism]
QED
Theorem bn254_twist_embedding_inj:
  INJ bn254_twist_embedding bn254_g2_group.carrier bn254_fp12_curve_group.carrier
Proof
  simp[bn254_g2_group_def, bn254_fp12_curve_group_def, sw_group_carrier] >>
  metis_tac[bn254_twist_monomorphism]
QED
Theorem bls12381_twist_embedding_inj:
  INJ bls12381_twist_embedding bls12381_g2_group.carrier bls12381_fp12_curve_group.carrier
Proof
  simp[bls12381_g2_group_def, bls12381_fp12_curve_group_def, sw_group_carrier] >>
  metis_tac[bls12381_twist_monomorphism]
QED

Theorem bn254_twist_embedding_scalar:
  !P n. P IN bn254_g2_group.carrier ==>
    bn254_twist_embedding (bn254_g2_group.exp P n) =
      bn254_fp12_curve_group.exp (bn254_twist_embedding P) n
Proof
  rpt strip_tac >> irule group_homo_exp >>
  metis_tac[bn254_twist_embedding_group_homo, short_weierstrass_group,
    bn254_g2_group_def, bn254_fp12_curve_group_def, bn254_g2_curve, bn254_fp12_curve]
QED
Theorem bls12381_twist_embedding_scalar:
  !P n. P IN bls12381_g2_group.carrier ==>
    bls12381_twist_embedding (bls12381_g2_group.exp P n) =
      bls12381_fp12_curve_group.exp (bls12381_twist_embedding P) n
Proof
  rpt strip_tac >> irule group_homo_exp >>
  metis_tac[bls12381_twist_embedding_group_homo, short_weierstrass_group,
    bls12381_g2_group_def, bls12381_fp12_curve_group_def,
    bls12381_g2_curve, bls12381_fp12_curve]
QED

Theorem bn254_twist_embedding_order:
  !P. P IN bn254_g2_group.carrier ==>
    order bn254_fp12_curve_group (bn254_twist_embedding P) = order bn254_g2_group P
Proof
  rpt strip_tac >> irule injective_group_homo_order >>
  metis_tac[bn254_twist_embedding_group_homo, bn254_twist_embedding_inj,
    short_weierstrass_group, bn254_g2_group_def, bn254_fp12_curve_group_def,
    bn254_g2_curve, bn254_fp12_curve]
QED
Theorem bls12381_twist_embedding_order:
  !P. P IN bls12381_g2_group.carrier ==>
    order bls12381_fp12_curve_group (bls12381_twist_embedding P) = order bls12381_g2_group P
Proof
  rpt strip_tac >> irule injective_group_homo_order >>
  metis_tac[bls12381_twist_embedding_group_homo, bls12381_twist_embedding_inj,
    short_weierstrass_group, bls12381_g2_group_def, bls12381_fp12_curve_group_def,
    bls12381_g2_curve, bls12381_fp12_curve]
QED

Theorem bn254_twist_embedded_generator_order:
  order bn254_fp12_curve_group (bn254_twist_embedding bn254_g2_generator) = bn254_n
Proof
  metis_tac[bn254_twist_embedding_order, bn254_g2_generator_order,
    bn254_g2_generator_member, bn254_g2_group_def, sw_group_carrier]
QED
Theorem bls12381_twist_embedded_generator_order:
  order bls12381_fp12_curve_group (bls12381_twist_embedding bls12381_g2_generator) = bls12381_n
Proof
  metis_tac[bls12381_twist_embedding_order, bls12381_g2_generator_order,
    bls12381_g2_generator_member, bls12381_g2_group_def, sw_group_carrier]
QED

