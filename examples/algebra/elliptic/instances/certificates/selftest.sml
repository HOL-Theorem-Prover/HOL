open HolKernel boolLib bossLib testutils;
open shortWeierstrassTheory shortWeierstrassGroupTheory
     shortWeierstrassSmallTheory ellipticCertificatesTheory
     fieldInstancesTheory ellipticCertificateFixturesTheory;

val _ = new_theory "scratch";
val failures = ref 0;
val _ = diemode := Remember failures;

val prime = groupTheory.PRIME_5;
val curve = sw_GF5_curve;
val member = certificate_GF5_member;
val inverses = sw_GF5_prod_inv_table;
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
  (DISCH_TAC THEN
   pairingCurveCertificateLib.CERTIFICATE_CHUNKS_TAC
     operation step [2, 2] [asm_rewrite_tac []])
  ``(GF 5).prod.exp (f (ECAffine 4 0)) 2 = c ==>
    (GF 5).prod.exp (f ((sw_group (GF 5) 0 1).exp (ECAffine 2 2) 3)) 2 = c``;

val _ = proof_test "Zero scalar closes without operation branches"
  operation
  ``(sw_group (GF 5) 0 1).exp (ECAffine 2 2) 0 = ECInfinity``;

val _ = proof_test "Completed scalar prefix rewrites only the residual"
  (STRIP_TAC THEN operation THEN ASM_REWRITE_TAC [])
  ``(sw_group (GF 5) 0 1).exp (ECAffine 2 2) 3 = ECAffine 4 0 /\
    f (ECAffine 4 0) ==>
    f ((sw_group (GF 5) 0 1).exp (ECAffine 2 2) 3)``;

val _ =
  let
    val curve = ASSUME (concl curve)
    val member = ASSUME (concl member)
    val certificate =
      ellipticCertificateLib.BINARY_SCALAR_OPERATION_CERTIFICATE_TAC
        1 candidate curve member
    val step = ellipticCertificateLib.BINARY_SCALAR_STEP_TAC
      addition curve member
    val goal =
      ``(sw_group (GF 5) 0 1).exp (ECAffine 2 2) 1 = ECAffine 2 2``
    fun check th =
      aconv (concl th) goal andalso length (hyp th) = 2 andalso
      List.all (fn tm => List.exists (aconv tm) (hyp th))
        [concl curve, concl member]
  in
    tprint "Scalar milestones retain supplied theorem hypotheses";
    require_msg (check_result check) thm_to_string
      (fn tm => prove (tm, certificate THENL [step, step])) goal
  end;

(* F_7[i], i^2 = -1. Expected values below are fixed arithmetic answers,
   not results obtained from the converters under test. *)
val quadratic_prime = groupTheory.PRIME_7;
val quadratic = ``PolyModRing (GF 7) [1n;0;1]``;
val quadratic_field = certificate_GF49_field;

(* Rebind algebra names before constructing the converters. In particular,
   initialize the quadratic arithmetic cache here, not before the rebinding. *)
val _ =
  let
    val grammars = Parse.current_grammars ()
    val scalar_goal =
      ``(sw_group (GF 5) 0 1).exp (ECAffine 2 2) 3 = ECAffine 4 0``
    val certificate_goal =
      ``f (ECAffine 4 0) ==>
        f ((sw_group (GF 5) 0 1).exp (ECAffine 2 2) 3)``
    val inverse_goal = ``^quadratic.prod.inv [1n;1] = [4n;3]``
    val quadratic_goal =
      ``(sw_group ^quadratic [] [1n]).exp (ECAffine [0n;1] [3n;1]) 2 =
        ECAffine [2n] [3n]``
    val quadratic_certificate_goal =
      ``f (ECAffine [2n] [3n]) ==>
        f ((sw_group ^quadratic [] [1n]).exp (ECAffine [0n;1] [3n;1]) 2)``
    fun run () =
      let
        val _ = List.app
          (fn name =>
            (Parse.temp_clear_overloads_on name;
             Parse.temp_overload_on (name,boolSyntax.T)))
          ["GF", "Field", "PolyModRing", "poly_monic", "poly_deg",
           "Poly", "poly_mod", "prime", "ECInfinity", "ECAffine",
           "sw_group", "sw_add", "sw_points", "ShortWeierstrassCurve"]
        val scalar = ellipticCertificateLib.SCALAR_CONV prime curve member
        val _ = proof_test "Prime scalar with rebound algebra syntax"
          (CONV_TAC (LAND_CONV scalar) THEN REFL_TAC) scalar_goal
        val _ = proof_test "Prime milestones with rebound algebra syntax"
          (DISCH_TAC THEN
           ellipticCertificateLib.SCALAR_CERTIFICATE_TAC
             2 prime curve member THENL
             [ellipticCertificateLib.SCALAR_STEP_TAC prime curve member,
              asm_rewrite_tac []]) certificate_goal
        val arithmetic =
          pairingCurveCertificateLib.FIELD_CONV quadratic_prime quadratic_field
        val _ = proof_test "Quadratic inverse with rebound algebra syntax"
          (CONV_TAC arithmetic) inverse_goal
        val scalar = pairingCurveCertificateLib.SCALAR_CONV
          quadratic_prime quadratic_field
          certificate_GF49_curve certificate_GF49_member
        val _ = proof_test "Quadratic scalar with rebound algebra syntax"
          (CONV_TAC (LAND_CONV scalar) THEN REFL_TAC) quadratic_goal
        val step = pairingCurveCertificateLib.SCALAR_STEP_TAC
          quadratic_prime quadratic_field
          certificate_GF49_curve certificate_GF49_member
      in
        proof_test "Quadratic milestones with rebound algebra syntax"
          (DISCH_TAC THEN
           pairingCurveCertificateLib.SCALAR_CERTIFICATE_TAC
             quadratic_prime quadratic_field
             certificate_GF49_curve certificate_GF49_member THENL
             [step, step, step, asm_rewrite_tac []])
          quadratic_certificate_goal
      end
  in
    (run () handle e => (Parse.temp_set_grammars grammars; raise e));
    Parse.temp_set_grammars grammars
  end;

val quadratic_arithmetic =
  pairingCurveCertificateLib.FIELD_CONV quadratic_prime quadratic_field;
val quadratic_curve = certificate_GF49_curve;
val quadratic_member = certificate_GF49_member;

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
  (DISCH_TAC THEN
   pairingCurveCertificateLib.CERTIFICATE_CHUNKS_TAC
     quadratic_scalar quadratic_step [17, 2] [asm_rewrite_tac []])
  ``f (ECAffine [4n;2] [5n;6]) ==>
    f ((sw_group ^quadratic [] [1n]).exp (ECAffine [0n;1] [3n;1]) 65537)``;

val quadratic_power =
  pairingCurveCertificateLib.POWER_CERTIFICATE_TAC
    quadratic_prime quadratic_field;
val quadratic_power_step =
  pairingCurveCertificateLib.POWER_STEP_TAC
    quadratic_prime quadratic_field;
val _ = proof_test "Zero quadratic power closes without operation branches"
  quadratic_power
  ``^quadratic.prod.exp [1n;1] 0 = [1n]``;

val _ = proof_test "Power resumes from the strongest matching prefix"
  (STRIP_TAC THEN quadratic_power THEN ASM_REWRITE_TAC [])
  ``^quadratic.prod.exp [1n;1] 1 = [1n;1] /\
    ^quadratic.prod.exp [1n;1] 3 = [5n;2] /\
    ^quadratic.prod.exp [1n;2] 3 = [3n;5] /\
    f [5n;2] ==>
    f (^quadratic.prod.exp [1n;1] 3)``;

val _ = proof_test "Quadratic power resumes and retains its residual"
  (DISCH_TAC THEN
   pairingCurveCertificateLib.CERTIFICATE_CHUNKS_TAC
     quadratic_power quadratic_power_step [17, 2] [asm_rewrite_tac []])
  ``f [4n;4] ==> f (^quadratic.prod.exp [1n;1] 65537)``;

val _ = exit_count0 failures;
