open HolKernel boolLib bossLib Parse

open normal_orderTheory
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

val nstar_steps = store_thm(
  "nstar_steps",
  ``∀M N. M -n->* N ⇒ ∃n. N = steps n M``,
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN SRW_TAC [][] THEN1
    (Q.EXISTS_TAC `0` THEN SRW_TAC [][]) THEN
  FULL_SIMP_TAC (srw_ss()) [noreduct_characterisation] THEN
  Q.EXISTS_TAC `SUC n` THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [SYM noreduct_bnf]);

val steps_noreduct = store_thm(
  "steps_noreduct",
  ``∀t. ¬bnf (steps n t) ⇒
        (steps n (THE (noreduct t)) = THE (noreduct (steps n t)))``,
  Induct_on `n` THEN SRW_TAC [][] THEN
  POP_ASSUM MP_TAC THEN Cases_on `n` THEN SRW_TAC [][]);

val steps_plus = store_thm(
  "steps_plus",
  ``∀t. steps (m + n) t = steps m (steps n t)``,
  Induct_on `m` THEN SRW_TAC [][arithmeticTheory.ADD_CLAUSES] THENL [
    Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [],
    POP_ASSUM MP_TAC THEN Cases_on `n` THEN SRW_TAC [][],
    `steps n (THE (noreduct t)) = steps n t`
      by METIS_TAC [bnf_steps_upwards_closed, steps_def,
                    DECIDE ``n < SUC n``] THEN
    Cases_on `m` THEN SRW_TAC [][],
    SRW_TAC [][steps_noreduct]
  ]);

val bnf_steps_fixpoint = store_thm(
  "bnf_steps_fixpoint",
  ``bnf M ⇒ (steps n M = M)``,
  METIS_TAC [bnf_steps_upwards_closed, DECIDE ``0 < n ∨ (n = 0)``, steps_def]);

val _ = export_theory ()
