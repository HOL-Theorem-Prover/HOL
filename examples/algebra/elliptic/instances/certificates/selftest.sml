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

val _ = exit_count0 failures;
