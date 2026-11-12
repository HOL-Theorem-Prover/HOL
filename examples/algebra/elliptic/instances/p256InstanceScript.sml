(* P-256: affine curve and standard prime-order generator.

   Documentation
   Coordinates are natural-number residues in p256_base_field; ECAffine
   and ECInfinity represent the points. The coefficient a = p256_p - 3
   represents -3. namedPrimeFields supplies the base and scalar fields.

   Definitions: p256_a_def, p256_b_def, p256_generator_def,
   p256_group_def (all rational points), p256_subgroup_def (Generated
   by the standard generator).

   Curve and membership: p256_curve, p256_generator_member,
   p256_finite_group.
   Generator and subgroup: p256_generator_annihilated,
   p256_generator_order, p256_subgroup_is_subgroup,
   p256_subgroup_cyclic, p256_subgroup_card.

   Full-group cardinality is separate: cofactorOneInstances supplies
   p256_card and p256_generated_full_group. *)

Theory p256Instance
Ancestors
  namedPrimes
  namedPrimeFields ellipticCertificates ellipticTorsion fieldInstances
  shortWeierstrass shortWeierstrassGroup
Libs
  ellipticCertificateLib

(* Standard affine parameters; no executable Verifereum arithmetic is imported. *)
Definition p256_a_def:
  p256_a :num = p256_p - 3
End

Definition p256_b_def:
  p256_b :num = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
End

Definition p256_generator_def:
  p256_generator = ECAffine (0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296:num) (0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5:num)
End

Definition p256_group_def:
  p256_group = sw_group p256_base_field p256_a p256_b
End

Definition p256_subgroup_def:
  p256_subgroup = Generated p256_group p256_generator
End

Theorem p256_curve:
  ShortWeierstrassCurve p256_base_field p256_a p256_b
Proof
  REWRITE_TAC [ShortWeierstrassCurve_def] >>
  REWRITE_TAC [p256_base_field_field, p256_base_field_char] >>
  REWRITE_TAC [p256_base_field_def, p256_a_def,
    p256_b_def, p256_p_def, sw_discriminant_def,
    GF_eval, GF_sum_inv, monoidTheory.monoid_exp_def] >>
  CONV_TAC (certificateComputeLib.EVAL_CONV ())
QED

Theorem p256_generator_member:
  p256_generator IN sw_points p256_base_field p256_a p256_b
Proof
  REWRITE_TAC [sw_points_member, sw_on_curve_def, sw_curve_rhs_def,
    p256_base_field_def, p256_p_def, p256_a_def,
    p256_b_def, p256_generator_def, GF_eval,
    monoidTheory.monoid_exp_def] >>
  CONV_TAC (certificateComputeLib.EVAL_CONV ())
QED

Theorem p256_finite_group:
  FiniteAbelianGroup p256_group
Proof
  rw[p256_group_def] >>
  irule short_weierstrass_finite_group >>
  simp[p256_curve, p256_base_field_finite_field]
QED

local
    val definitions = [p256_group_def, p256_base_field_def, p256_p_def, p256_a_def, p256_b_def, p256_generator_def, p256_n_def]
    fun numeric th = CONV_RULE certificateComputeLib.NAT_CONV
      (REWRITE_RULE definitions th)
    val prime = numeric p256_p_prime
    val curve = numeric p256_curve
    val member = numeric p256_generator_member
    val step = ellipticCertificateLib.SCALAR_STEP_TAC prime curve member
in
  val p256_scalar_normalize = CONV_TAC (LAND_CONV
    (REWRITE_CONV definitions THENC certificateComputeLib.NAT_CONV))
  val p256_scalar_certificate =
    ellipticCertificateLib.SCALAR_CERTIFICATE_TAC 4 prime curve member
  val p256_scalar_step = step
end

Theorem p256_generator_annihilated:
  p256_group.exp p256_generator p256_n = ECInfinity
Proof
  p256_scalar_normalize >>
  p256_scalar_certificate
  >| [p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step,
      p256_scalar_step, p256_scalar_step]
QED

Theorem p256_generator_order:
  order p256_group p256_generator = p256_n
Proof
  rw[p256_group_def] >>
  irule sw_prime_generator_order >>
  simp[p256_curve, p256_generator_member, p256_n_prime,
       p256_generator_def,
       REWRITE_RULE [p256_group_def] p256_generator_annihilated]
QED

Theorem p256_subgroup_is_subgroup:
  Subgroup p256_subgroup p256_group
Proof
  rw[p256_subgroup_def, p256_group_def] >>
  irule sw_generated_subgroup >>
  simp[p256_curve, p256_generator_member, p256_base_field_finite_field]
QED

Theorem p256_subgroup_cyclic:
  cyclic p256_subgroup
Proof
  rw[p256_subgroup_def, p256_group_def] >>
  irule sw_generated_cyclic >>
  simp[p256_curve, p256_generator_member, p256_base_field_finite_field]
QED

Theorem p256_subgroup_card:
  CARD p256_subgroup.carrier = p256_n
Proof
  rw[p256_subgroup_def] >>
  `0 < p256_n` by metis_tac[p256_n_prime, dividesTheory.ONE_LT_PRIME,
                                      arithmeticTheory.LESS_TRANS, DECIDE ``(0:num) < 1``] >>
  metis_tac[sw_generator_card, p256_curve, p256_generator_member,
            p256_group_def, p256_generator_order]
QED

