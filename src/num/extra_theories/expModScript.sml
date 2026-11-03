Theory expMod[bare]
Ancestors
  arithmetic
Libs
  HolKernel boolLib Parse BasicProvers TotalDefn
  simpLib numSimps numLib metisLib

(* This implementation is heavily inspired by the modular exponentiation
   implementation in examples/AKS/compute/computeBasicScript.sml. *)

Definition exp_mod_step_def:
  exp_mod_step b n k acc =
    if k = 0 then (acc * b ** n) MOD k
    else if n = 0 then acc MOD k
    else exp_mod_step ((b * b) MOD k) (n DIV 2) k
           (if EVEN n then acc else (acc * b) MOD k)
End

Definition exp_mod_binary_def:
  exp_mod_binary a n m = exp_mod_step a n m 1
End

(* Splitting the exponent into its quotient and remainder modulo two. *)
Theorem exp_halves[local]:
  !b e. b ** e =
    if EVEN e then (b * b) ** (e DIV 2)
    else b * (b * b) ** (e DIV 2)
Proof
  rpt gen_tac >>
  `b ** e = b ** (e DIV 2 * 2 + e MOD 2)` by
    (AP_TERM_TAC >>
     MP_TAC (Q.SPEC `e` (MATCH_MP DIVISION (DECIDE ``0n < 2``))) >>
     DECIDE_TAC) >>
  pop_assum (fn th => CONV_TAC (LAND_CONV (REWR_CONV th))) >>
  Cases_on `EVEN e` >>
  ASM_SIMP_TAC (srw_ss())
    [MOD_2, EXP_ADD, GSYM EXP_EXP_MULT, GSYM EXP_2, MULT_COMM]
QED

Theorem exp_mod_step_acc_eq[local]:
  exp_mod_step b e m acc = (acc * b ** e) MOD m
Proof
  Q.ID_SPEC_TAC `acc` >>
  Q.ID_SPEC_TAC `b` >>
  completeInduct_on `e` >>
  rpt strip_tac >>
  Cases_on `m = 0` >-
    ASM_SIMP_TAC (srw_ss()) [Once exp_mod_step_def] >>
  Cases_on `e = 0` >-
    ASM_SIMP_TAC (srw_ss()) [Once exp_mod_step_def] >>
  `e DIV 2 < e` by
    (match_mp_tac DIV_LESS >> conj_tac >> DECIDE_TAC) >>
  ONCE_REWRITE_TAC [exp_mod_step_def] >>
  ASM_SIMP_TAC (srw_ss()) [] >>
  Cases_on `EVEN e` >>
  ASM_SIMP_TAC (srw_ss()) [] >>
  MP_TAC (Q.SPECL [`b`, `e`] exp_halves) >>
  ASM_SIMP_TAC (srw_ss()) [] >>
  DISCH_TAC >>
  ONCE_REWRITE_TAC [GSYM MOD_TIMES2] >>
  REWRITE_TAC [EXP_MOD, MOD_MOD] >>
  ASM_SIMP_TAC (srw_ss()) [MOD_TIMES2, MULT_ASSOC]
QED

Theorem exp_mod_binary_eqn:
  !m n a. exp_mod_binary a n m = (a ** n) MOD m
Proof
  SIMP_TAC (srw_ss()) [exp_mod_binary_def, exp_mod_step_acc_eq]
QED
