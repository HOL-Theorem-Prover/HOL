open HolKernel boolLib bossLib Parse

open normal_orderTheory churchDBTheory churchlistTheory
open reductionEval

fun Store_thm (trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

val _ = new_theory "steps"

val steps_def = Define`
  (steps 0 t = t) ∧
  (steps (SUC n) t = if bnf t then t else steps n (THE (noreduct t)))
`;
val _ = export_rewrites ["steps_def"]

val bnf_steps = store_thm(
  "bnf_steps",
  ``(bnf_of t = SOME u) ⇔ ∃n. (steps n t = u) ∧ bnf u``,
  SRW_TAC [][EQ_IMP_THM] THENL [
    IMP_RES_TAC bnf_of_SOME THEN SRW_TAC [][] THEN
    Q.PAT_ASSUM `t -n->* u` MP_TAC THEN
    MAP_EVERY Q.ID_SPEC_TAC [`u`, `t`] THEN
    HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN SRW_TAC [][] THEN1
      (Q.EXISTS_TAC `0` THEN SRW_TAC[][]) THEN
    Q.EXISTS_TAC `SUC n` THEN SRW_TAC [][] THEN1
      (METIS_TAC [normorder_bnf]) THEN
    FULL_SIMP_TAC (srw_ss()) [noreduct_characterisation],

    POP_ASSUM MP_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`t`,`n`] THEN
    Induct THEN SRW_TAC [][] THENL [
      MATCH_MP_TAC nstar_bnf_of_SOME_I THEN SRW_TAC [][],
      MATCH_MP_TAC nstar_bnf_of_SOME_I THEN SRW_TAC [][],
      SRW_TAC [][Once bnf_of_thm]
    ]
  ]);

val RTC_L1_I = CONJUNCT2 (SPEC_ALL relationTheory.RTC_RULES)

val steps_nstar = store_thm(
  "steps_nstar",
  ``∀n t. t -n->* steps n t``,
  Induct THEN SRW_TAC [][] THEN MATCH_MP_TAC RTC_L1_I THEN
  Q.EXISTS_TAC `THE (noreduct t)` THEN SRW_TAC [][] THEN
  `∃u. t -n-> u` by METIS_TAC [normorder_bnf] THEN
  `noreduct t = SOME u` by METIS_TAC [noreduct_characterisation] THEN
  SRW_TAC [][]);

val bnf_steps_upwards_closed = store_thm(
  "bnf_steps_upwards_closed",
  ``∀n m t. bnf (steps n t) ∧ n < m ⇒ (steps m t = steps n t)``,
  Induct_on `n` THEN SRW_TAC [][] THENL [
    Cases_on `m` THEN SRW_TAC [][],
    Cases_on `m` THEN SRW_TAC [][],
    Cases_on `m` THEN FULL_SIMP_TAC (srw_ss()) []
  ]);

val csteps_def = Define`
  csteps =
  LAM "n" (LAM "t"
    (VAR "n" @@ (LAM "u" (VAR "u"))
             @@ (LAM "f" (LAM "u"
                   (cbnf @@ VAR "u"
                         @@ VAR "u"
                         @@ (VAR "f" @@ (cnoreduct @@ VAR "u")))))
             @@ VAR "t"))
`;

val FV_csteps = Store_thm(
  "FV_csteps",
  ``FV csteps = {}``,
  SRW_TAC [][csteps_def, pred_setTheory.EXTENSION]);

open brackabs
val csteps_eqn = brackabs_equiv [] csteps_def

val csteps_behaviour = store_thm(
  "csteps_behaviour",
  ``∀n t.
      csteps @@ church n @@ cDB (fromTerm t) -n->* cDB (fromTerm (steps n t))``,
  SIMP_TAC (bsrw_ss()) [csteps_eqn] THEN
  Induct THEN
  ASM_SIMP_TAC (bsrw_ss()) [churchnumTheory.church_thm, cbnf_behaviour] THEN
  Q.X_GEN_TAC `t` THEN Cases_on `bnf t` THEN
  ASM_SIMP_TAC (bsrw_ss()) [churchboolTheory.cB_behaviour,
                            cnoreduct_behaviour]);

val cbnf_filter_def = Define`
  cbnf_filter =
  LAM "l" (VAR "l" @@ cnil
                   @@ (LAM "h" (LAM "r"
                          (cbnf @@ VAR "h"
                                @@ (ccons @@ VAR "h" @@ VAR "r")
                                @@ VAR "r"))))
`;

val FV_cbnf_filter = Store_thm(
  "FV_cbnf_filter",
  ``FV cbnf_filter = {}``,
  SRW_TAC [][cbnf_filter_def, pred_setTheory.EXTENSION]);


val cbnf_filter_eqn = brackabs_equiv [] cbnf_filter_def

val cbnf_filter_behaviour = store_thm(
  "cbnf_filter_behaviour",
  ``cbnf_filter @@ cnil == cnil ∧
    cbnf_filter @@ (cvcons (cDB (fromTerm t)) l) ==
      if bnf t then cvcons (cDB (fromTerm t)) (cbnf_filter @@ l)
      else cbnf_filter @@ l``,
  SIMP_TAC (bsrw_ss()) [cbnf_filter_eqn, cnil_def, wh_cvcons,
                        cbnf_behaviour] THEN
  Cases_on `bnf t` THEN
  ASM_SIMP_TAC (bsrw_ss()) [cbnf_filter_eqn, churchboolTheory.cB_behaviour,
                            Cong cvcons_cong, cnil_def, wh_ccons]);

val _ = export_theory ()
