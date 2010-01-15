open HolKernel boolLib bossLib Parse

open pure_dBTheory normal_orderTheory

fun Store_thm(trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

val _ = new_theory "dnoreduct"

val dest_dabs_def = Define`
  (dest_dabs (dABS t) = t)
`;
val _ = export_rewrites ["dest_dabs_def"]

val dnoreduct_def = Define`
  (dnoreduct (dV i) = NONE) ∧
  (dnoreduct (dAPP t u) =
     if is_dABS t then SOME (nsub u 0 (dest_dabs t))
     else if dbnf t then OPTION_MAP (dAPP t) (dnoreduct u)
     else  SOME (dAPP (THE (dnoreduct t)) u)) ∧
  (dnoreduct (dABS t) = OPTION_MAP dABS (dnoreduct t))
`;
val _ = export_rewrites ["dnoreduct_def"]

val notbnf_noreduct = prove(
  ``¬bnf t ⇒ ∃u. noreduct t = SOME u``,
  Cases_on `noreduct t` THEN1 FULL_SIMP_TAC (srw_ss()) [noreduct_bnf] THEN
  SRW_TAC [][]);

val notbnf_dnoreduct = store_thm(
  "notbnf_dnoreduct",
  ``¬dbnf t ⇒ ∃u. dnoreduct t = SOME u``,
  Induct_on `t` THEN SRW_TAC [][]);

val dnoreduct_dbeta = store_thm(
  "dnoreduct_dbeta",
  ``∀t u. (dnoreduct t = SOME u) ⇒ dbeta t u``,
  Induct_on `t` THEN SRW_TAC [][] THENL [
    Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    METIS_TAC [dbeta_rules],
    METIS_TAC [dbeta_rules],
    IMP_RES_TAC notbnf_dnoreduct THEN SRW_TAC [][] THEN
    METIS_TAC [dbeta_rules],
    METIS_TAC [dbeta_rules]
  ]);

val dnoreduct_FV = store_thm(
  "dnoreduct_FV",
  ``(dnoreduct t = SOME u) ∧ v ∈ dFV u ⇒ v ∈ dFV t``,
  STRIP_TAC THEN IMP_RES_TAC dnoreduct_dbeta THEN
  FULL_SIMP_TAC (srw_ss()) [dbeta_dbeta'_eqn] THEN
  `∃tt uu. (t = fromTerm tt) ∧ (u = fromTerm uu)`
     by METIS_TAC [fromTerm_onto] THEN
  FULL_SIMP_TAC (srw_ss()) [IN_dFV, dbeta'_eq_ccbeta] THEN
  METIS_TAC [chap3Theory.cc_beta_FV_SUBSET, pred_setTheory.SUBSET_DEF]);

val dpm_is_dABS = Store_thm(
  "dpm_is_dABS",
  ``is_dABS (dpm π t) = is_dABS t``,
  Cases_on `t` THEN SRW_TAC [][]);

val dpm_dbnf = Store_thm(
  "dpm_dbnf",
  ``∀π. dbnf (dpm π t) = dbnf t``,
  Induct_on `t` THEN SRW_TAC [][]);

val dest_dabs_dpm = store_thm(
  "dest_dabs_dpm",
  ``is_dABS d ⇒ (dest_dabs (dpm π d) = dpm (inc_pm 0 π) (dest_dabs d))``,
  Cases_on `d` THEN SRW_TAC [][]);

val dnoreduct_dpm = store_thm(
  "dnoreduct_dpm",
  ``∀d π. dnoreduct (dpm π d) = OPTION_MAP (dpm π) (dnoreduct d)``,
  Induct_on `d` THEN
  SRW_TAC [][dpm_nsub, optionTheory.OPTION_MAP_COMPOSE, combinTheory.o_DEF,
             dest_dabs_dpm] THEN
  IMP_RES_TAC notbnf_dnoreduct THEN SRW_TAC [][]);

val dnoreduct_dLAM = Store_thm(
  "dnoreduct_dLAM",
  ``dnoreduct (dLAM i t) = OPTION_MAP (dLAM i) (dnoreduct t)``,
  SRW_TAC [][dLAM_def] THEN
  `dLAM i = λt. dLAM i t` by SRW_TAC [][FUN_EQ_THM] THEN
  POP_ASSUM SUBST1_TAC THEN SRW_TAC [][dLAM_def] THEN
  Q.ABBREV_TAC `MX = if dFV t = {} then 0 else MAX_SET (dFV t)` THEN
  `∀i. i ∈ dFV t ⇒ i ≤ MX`
      by SRW_TAC [][Abbr`MX`, pred_setTheory.MAX_SET_DEF] THEN
  Q.ABBREV_TAC `π = lifting_pm 0 MX` THEN
  `lift t 0 = dpm π t`
     by SRW_TAC [][lifts_are_specific_dpms, Abbr`π`] THEN
  `0 ∉ dFV (lift t 0)` by SRW_TAC [][] THEN
  `sub (dV 0) (i + 1) (lift t 0) = dpm [(n2s 0, n2s (i + 1))] (lift t 0)`
     by SRW_TAC [][fresh_dpm_sub] THEN
  SRW_TAC [][dnoreduct_dpm, optionTheory.OPTION_MAP_COMPOSE] THEN
  `(dnoreduct t = NONE) ∨ ∃u. dnoreduct t = SOME u`
     by (Cases_on `dnoreduct t` THEN SRW_TAC [][]) THEN
  SRW_TAC [][] THEN
  `∀i. i ∈ dFV u ⇒ i ≤ MX` by METIS_TAC [dnoreduct_FV] THEN
  `lift u 0 = dpm π u`
     by SRW_TAC [][lifts_are_specific_dpms, Abbr`π`] THEN
  `0 ∉ dFV (lift u 0)` by SRW_TAC [][] THEN
  `sub (dV 0) (i + 1) (lift u 0) = dpm [(n2s 0, n2s (i + 1))] (lift u 0)`
     by SRW_TAC [][fresh_dpm_sub] THEN
  SRW_TAC [][]);

val dnoreduct_correct = store_thm(
  "dnoreduct_correct",
  ``∀t. noreduct t = OPTION_MAP toTerm (dnoreduct (fromTerm t))``,
  HO_MATCH_MP_TAC termTheory.simple_induction THEN
  SRW_TAC [][noreduct_thm, optionTheory.OPTION_MAP_COMPOSE,
             combinTheory.o_DEF]
  THENL [
    `∃v t0. t = LAM v t0`
       by (Q.SPEC_THEN `t` FULL_STRUCT_CASES_TAC termTheory.term_CASES THEN
           FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []) THEN
    ASM_SIMP_TAC (srw_ss()) [noreduct_thm, dLAM_def, GSYM sub_nsub,
                             GSYM fromTerm_subst],

    `¬dbnf (fromTerm t)` by SRW_TAC [][] THEN
    IMP_RES_TAC notbnf_dnoreduct THEN SRW_TAC [][]
  ]);

val omap_lemma = prove(``OPTION_MAP (λx. x) y = y``,
                       Cases_on `y` THEN SRW_TAC [][])

val dnoreduct_thm = Store_thm(
  "dnoreduct_thm",
  ``(dnoreduct (fromTerm t) = OPTION_MAP fromTerm (noreduct t)) ∧
    (noreduct (toTerm d) = OPTION_MAP toTerm (dnoreduct d))``,
  SRW_TAC [][dnoreduct_correct, optionTheory.OPTION_MAP_COMPOSE,
             combinTheory.o_DEF, omap_lemma]);

val _ = export_theory()
