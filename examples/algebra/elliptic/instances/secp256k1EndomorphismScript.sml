(* secp256k1 complex multiplication and its scalar eigenvalue.

   Documentation
   secp256k1_endo_def specializes sw_cm_map: multiply an affine x-coordinate
   by the nontrivial cube root secp256k1_beta and preserve infinity.
   secp256k1_lambda is the matching scalar-field cube root.

   Constants: secp256k1_beta_def, secp256k1_lambda_def.
   Certificates: secp256k1_beta_certificate, secp256k1_lambda_certificate.
   Structure and scalar compatibility: secp256k1_endo_group,
   secp256k1_endo_scalar.
   Eigenvalue: secp256k1_endo_generator, secp256k1_endo_is_lambda_scalar.

   The last result applies to every point in sw_points, using the
   cofactor-one full-group identification, not just to the generator.
   Both scalar-compatibility results require point membership. *)

Theory secp256k1Endomorphism
Ancestors
  namedPrimes
  secp256k1Instance cofactorOneInstances ellipticCMMap ellipticMorphisms
  ellipticCertificates ellipticTorsion namedPrimeFields fieldInstances
  shortWeierstrass shortWeierstrassGroup
Libs
  ellipticCertificateLib

(* The standard nontrivial cube root and its matching generator eigenvalue. *)
Definition secp256k1_beta_def:
  secp256k1_beta :num =
    0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
End

Definition secp256k1_lambda_def:
  secp256k1_lambda :num =
    0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72
End

Definition secp256k1_endo_def:
  secp256k1_endo = sw_cm_map secp256k1_base_field secp256k1_beta
End

Theorem secp256k1_beta_certificate:
  secp256k1_beta IN secp256k1_base_field.carrier /\
  secp256k1_base_field.prod.exp secp256k1_beta 3 =
    secp256k1_base_field.prod.id /\
  secp256k1_beta <> secp256k1_base_field.prod.id
Proof
  REWRITE_TAC [secp256k1_beta_def, secp256k1_base_field_def, secp256k1_p_def,
    GF_eval, monoidTheory.monoid_exp_def] >>
  CONV_TAC (certificateComputeLib.EVAL_CONV ())
QED

Theorem secp256k1_lambda_certificate:
  secp256k1_lambda IN secp256k1_scalar_field.carrier /\
  secp256k1_scalar_field.prod.exp secp256k1_lambda 3 =
    secp256k1_scalar_field.prod.id /\
  secp256k1_lambda <> secp256k1_scalar_field.prod.id
Proof
  REWRITE_TAC [secp256k1_lambda_def, secp256k1_scalar_field_def, secp256k1_n_def,
    GF_eval, monoidTheory.monoid_exp_def] >>
  CONV_TAC (certificateComputeLib.EVAL_CONV ())
QED

Theorem secp256k1_endo_group:
  GroupEndo secp256k1_endo secp256k1_group
Proof
  REWRITE_TAC [secp256k1_endo_def, secp256k1_group_def] >>
  `secp256k1_base_field.sum.id = secp256k1_a` by
    REWRITE_TAC [secp256k1_base_field_def, secp256k1_a_def, GF_eval] >>
  metis_tac[sw_cm_map_group_endo, secp256k1_beta_certificate, secp256k1_curve]
QED

Theorem secp256k1_endo_scalar:
  P IN sw_points secp256k1_base_field secp256k1_a secp256k1_b ==>
  secp256k1_endo (secp256k1_group.exp P n) =
    secp256k1_group.exp (secp256k1_endo P) n
Proof
  metis_tac[sw_curve_endo_scalar, secp256k1_curve,
            secp256k1_endo_group, secp256k1_group_def]
QED

local
    val definitions = [secp256k1_group_def, secp256k1_base_field_def,
      secp256k1_p_def, secp256k1_a_def, secp256k1_b_def,
      secp256k1_generator_def, secp256k1_lambda_def]
    fun numeric th = CONV_RULE certificateComputeLib.NAT_CONV
      (REWRITE_RULE definitions th)
    val prime = numeric secp256k1_p_prime
    val curve = numeric secp256k1_curve
    val member = numeric secp256k1_generator_member
    val step = ellipticCertificateLib.SCALAR_STEP_TAC prime curve member
in
  val secp256k1_endo_scalar_normalize = CONV_TAC (RAND_CONV
    (REWRITE_CONV definitions THENC certificateComputeLib.NAT_CONV))
  val secp256k1_endo_scalar_certificate =
    ellipticCertificateLib.SCALAR_CERTIFICATE_TAC 4 prime curve member
  val secp256k1_endo_scalar_step = step
end

Theorem secp256k1_endo_generator:
  secp256k1_endo secp256k1_generator =
    secp256k1_group.exp secp256k1_generator secp256k1_lambda
Proof
  secp256k1_endo_scalar_normalize >>
  secp256k1_endo_scalar_certificate
  >| [secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      secp256k1_endo_scalar_step, secp256k1_endo_scalar_step,
      REWRITE_TAC [secp256k1_endo_def, sw_cm_map_def, secp256k1_beta_def,
        secp256k1_generator_def, secp256k1_base_field_def,
        secp256k1_p_def, GF_eval] >>
      CONV_TAC (certificateComputeLib.EVAL_CONV ())]
QED

Theorem secp256k1_endo_is_lambda_scalar:
  P IN sw_points secp256k1_base_field secp256k1_a secp256k1_b ==>
  secp256k1_endo P = secp256k1_group.exp P secp256k1_lambda
Proof
  strip_tac >>
  `P IN secp256k1_subgroup.carrier` by
    metis_tac[secp256k1_generated_full_group, secp256k1_group_def,
              sw_group_carrier] >>
  `?k. P = secp256k1_group.exp secp256k1_generator k` by
    metis_tac[secp256k1_subgroup_def, secp256k1_group_def,
              sw_generated_member] >>
  metis_tac[secp256k1_endo_scalar, secp256k1_endo_generator,
            secp256k1_generator_member, secp256k1_curve,
            sw_scalar_mult, secp256k1_group_def, arithmeticTheory.MULT_COMM]
QED

