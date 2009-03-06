open HolKernel boolLib bossLib Parse binderLib

open chap3Theory
open pred_setTheory
open termTheory
open boolSimps
open normal_orderTheory

val _ = new_theory "churchbool"

val _ = set_trace "Unicode" 1

val _ = remove_ovl_mapping "LAM" {Name="LAM", Thy="labelledTerms"}
val _ = remove_ovl_mapping "FV"  {Name="FV",  Thy="labelledTerms"}
val _ = remove_ovl_mapping "VAR" {Name="VAR", Thy="labelledTerms"}
val _ = remove_ovl_mapping "@@"  {Name="APP", Thy="labelledTerms"}

fun Store_thm(n,t,tac) = store_thm(n,t,tac) before export_rewrites [n]

val cB_def = Define`cB p = LAM "x" (LAM "y" (VAR (if p then "x" else "y")))`;
val FV_cB = Store_thm(
  "FV_cB",
  ``FV (cB p) = {}``,
  SRW_TAC [][cB_def, EXTENSION])
val bnf_cB = Store_thm(
  "bnf_cB",
  ``bnf (cB p)``,
  SRW_TAC [][cB_def]);
val cB_11 = Store_thm(
  "cB_11",
  ``(cB p = cB q) ⇔ (p ⇔ q)``,
  SRW_TAC [][cB_def]);

val cB_behaviour = store_thm(
  "cB_behaviour",
  ``cB T @@ x @@ y -n->* x ∧ cB F @@ x @@ y -n->* y``,
  SRW_TAC [][cB_def] THEN FRESH_TAC THEN
  SRW_TAC [][Once relationTheory.RTC_CASES1, normorder_rwts] THEN
  SRW_TAC [][Once relationTheory.RTC_CASES1, normorder_rwts, lemma14b]);

val cnot_def = Define`
  cnot = LAM "b" (VAR "b" @@ cB F @@ cB T)
`;
val FV_cnot = Store_thm(
  "FV_cnot",
  ``FV cnot = {}``,
  SRW_TAC [][cnot_def, EXTENSION])
val bnf_cnot = Store_thm(
  "bnf_cnot",
  ``bnf cnot``,
  SRW_TAC [][cnot_def]);
val cnot_behaviour = store_thm(
  "cnot_behaviour",
  ``cnot @@ cB p -n->* cB (¬p)``,
  Cases_on `p` THEN
  SRW_TAC [][cnot_def] THEN
  SRW_TAC [][Once relationTheory.RTC_CASES1, normorder_rwts, lemma14b,
             cB_behaviour]);


val cand_def = Define`
  cand = LAM "p" (LAM "q" (VAR "p" @@ VAR "q" @@ cB F))
`;
val FV_cand = Store_thm(
  "FV_cand",
  ``FV cand = {}``,
  SRW_TAC [][cand_def, EXTENSION] THEN METIS_TAC []);
val bnf_cand = Store_thm(
  "bnf_cand",
  ``bnf cand``,
  SRW_TAC [][cand_def]);
val cand_behaviour = store_thm(
  "cand_behaviour",
  ``cand @@ cB p @@ cB q -n->* cB (p /\ q)``,
  SRW_TAC [][cand_def, Once relationTheory.RTC_CASES1, normorder_rwts,
             lemma14b] THEN
  SRW_TAC [][Once relationTheory.RTC_CASES1, normorder_rwts, lemma14b] THEN
  Cases_on `p` THEN SRW_TAC [][cB_behaviour]);

val cand_F1 = store_thm(
  "cand_F1",
  ``cand @@ cB F @@ X -n->* cB F``,
  SRW_TAC [][cand_def, Once relationTheory.RTC_CASES1, normorder_rwts,
             lemma14b] THEN
  SRW_TAC [][Once relationTheory.RTC_CASES1, normorder_rwts, lemma14b] THEN
  SRW_TAC [][cB_behaviour]);

val cand_T1 = store_thm(
  "cand_T1",
  ``cand @@ cB T @@ X -n->* X``,
  SRW_TAC [][cand_def, Once relationTheory.RTC_CASES1, normorder_rwts,
             lemma14b] THEN
  SRW_TAC [][Once relationTheory.RTC_CASES1, normorder_rwts, lemma14b] THEN
  SRW_TAC [][cB_behaviour]);


val _ = export_theory()

