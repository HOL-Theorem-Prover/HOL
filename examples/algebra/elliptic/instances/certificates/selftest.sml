open HolKernel boolLib bossLib testutils;
open shortWeierstrassTheory shortWeierstrassGroupTheory
     shortWeierstrassSmallTheory ellipticCertificatesTheory
     fieldInstancesTheory;

val _ = new_theory "scratch";
val failures = ref 0;
val _ = diemode := Remember failures;

val prime = groupTheory.PRIME_5;
val curve = sw_GF5_curve;
val member = prove
  (``ECAffine 2 2 IN sw_points (GF 5) 0 1``,
   SIMP_TAC bool_ss
     [sw_GF5_points, pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]);
val inverses = prove
  (``(GF 5).prod.inv 1 = 1 /\ (GF 5).prod.inv 2 = 3 /\
     (GF 5).prod.inv 3 = 2 /\ (GF 5).prod.inv 4 = 4``,
   rpt conj_tac THEN irule sw_GF_prod_inv_witness THEN simp[prime]);
val addition = SIMP_CONV (srw_ss())
  [sw_add_def, sw_slope_def, sw_add_x_def, sw_add_y_def,
   GF_eval, GF_sum_inv, inverses, monoidTheory.monoid_exp_def,
   numeralTheory.numeral_funpow] THENC EVAL;
fun candidate tm = rhs (concl (addition tm));
val step = ellipticCertificateLib.BINARY_SCALAR_STEP_TAC addition curve member;

fun proof_test name tactic goal =
  (tprint name;
   require_msg
     (check_result (fn th => null (hyp th) andalso aconv (concl th) goal))
     thm_to_string (fn tm => prove (tm,tactic)) goal);

val _ = proof_test "Prime-field scalar under a field power"
  (DISCH_TAC THEN
   ellipticCertificateLib.SCALAR_CERTIFICATE_TAC 2 prime curve member THENL
     [ellipticCertificateLib.SCALAR_STEP_TAC prime curve member,
      asm_rewrite_tac []])
  ``(GF 5).prod.exp (f (ECAffine 4 0)) 2 = c ==>
    (GF 5).prod.exp (f ((sw_group (GF 5) 0 1).exp (ECAffine 2 2) 3)) 2 = c``;

val _ = proof_test "Scalar window skips an earlier unrelated field power"
  (DISCH_TAC THEN
   ellipticCertificateLib.BINARY_SCALAR_CERTIFICATE_TAC
     2 candidate curve member THENL [step, asm_rewrite_tac []])
  ``(GF 5).prod.exp 2 3 = c /\ f (ECAffine 0 4) ==>
    (GF 5).prod.exp 2 3 = c /\
    f ((sw_group (GF 5) 0 1).exp (ECAffine 2 2) 2)``;

val operation = ellipticCertificateLib.BINARY_SCALAR_OPERATION_CERTIFICATE_TAC
  1 candidate curve member;
val _ = proof_test "Scalar operations retain residuals across chunks"
  (DISCH_TAC THEN operation THENL
     [step, step, operation THENL [step, step, asm_rewrite_tac []]])
  ``(GF 5).prod.exp (f (ECAffine 4 0)) 2 = c ==>
    (GF 5).prod.exp (f ((sw_group (GF 5) 0 1).exp (ECAffine 2 2) 3)) 2 = c``;

(* F_7[i], i^2 = -1. Expected values below are fixed arithmetic answers,
   not results obtained from the converters under test. *)
val quadratic_prime = groupTheory.PRIME_7;
val quadratic = ``PolyModRing (GF 7) [1n;0;1]``;
val quadratic_field = prove
  (``Field ^quadratic``,
   metis_tac
     [fieldTheory.FiniteField_def,
      polyFieldModuloTheory.poly_mod_irreducible_finite_field,
      GF_finite_field, quadratic_prime,
      pairingQuadraticFieldsTheory.prime_3mod4_quadratic_irreducible,
      EQT_ELIM (EVAL ``7 MOD 4 = 3``)]);
val quadratic_arithmetic =
  pairingCurveCertificateLib.FIELD_CONV quadratic_prime quadratic_field;
val quadratic_char = prove
  (``ring$char ^quadratic = 7``,
   simp[polyFieldModuloTheory.poly_mod_ring_char_alt, GF_field,
        quadratic_prime, GF_prime_char,
        pairingQuadraticFieldsTheory.prime_3mod4_quadratic_monic,
        pairingQuadraticFieldsTheory.prime_3mod4_quadratic_degree]);
val quadratic_curve = prove
  (``ShortWeierstrassCurve ^quadratic [] [1n]``,
   SIMP_TAC bool_ss
     [ShortWeierstrassCurve_def, quadratic_field, quadratic_char] THEN
   CONV_TAC (REWRITE_CONV [sw_discriminant_def] THENC
     quadratic_arithmetic));
val quadratic_member = prove
  (``ECAffine [0n;1] [3n;1] IN sw_points ^quadratic [] [1n]``,
   CONV_TAC (REWRITE_CONV
     [sw_points_member, sw_on_curve_def, sw_curve_rhs_def] THENC
     quadratic_arithmetic));

val _ = proof_test "Quadratic inverse has a nonzero imaginary component"
  (CONV_TAC quadratic_arithmetic)
  ``^quadratic.prod.inv [1n;1] = [4n;3]``;

val quadratic_scalar =
  pairingCurveCertificateLib.SCALAR_CERTIFICATE_TAC
    quadratic_prime quadratic_field quadratic_curve quadratic_member;
val quadratic_step =
  pairingCurveCertificateLib.SCALAR_STEP_TAC
    quadratic_prime quadratic_field quadratic_curve quadratic_member;
(* 65537 has seventeen bits: the first chunk checks zero, one and fifteen
   doublings; the second checks a doubling and an addition, then a residual. *)
val _ = proof_test "Quadratic scalar resumes and retains its residual"
  (DISCH_TAC THEN quadratic_scalar THENL
    (List.tabulate (17, K quadratic_step) @
     [quadratic_scalar THENL
       [quadratic_step, quadratic_step, asm_rewrite_tac []]]))
  ``f (ECAffine [4n;2] [5n;6]) ==>
    f ((sw_group ^quadratic [] [1n]).exp (ECAffine [0n;1] [3n;1]) 65537)``;

val quadratic_power =
  pairingCurveCertificateLib.POWER_CERTIFICATE_TAC
    quadratic_prime quadratic_field;
val quadratic_power_step =
  pairingCurveCertificateLib.POWER_STEP_TAC
    quadratic_prime quadratic_field;
val _ = proof_test "Quadratic power resumes and retains its residual"
  (DISCH_TAC THEN quadratic_power THENL
    (List.tabulate (17, K quadratic_power_step) @
     [quadratic_power THENL
       [quadratic_power_step, quadratic_power_step, asm_rewrite_tac []]]))
  ``f [4n;4] ==> f (^quadratic.prod.exp [1n;1] 65537)``;

val _ = exit_count0 failures;
