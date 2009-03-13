open HolKernel boolLib bossLib Parse binderLib

open chap3Theory
open pred_setTheory
open termTheory
open boolSimps
open normal_orderTheory
open churchboolTheory
open reductionEval

val _ = new_theory "churchpair"

val _ = set_trace "Unicode" 1

fun Store_thm(n,t,tac) = store_thm(n,t,tac) before export_rewrites [n]

val cpair_def = Define`
  cpair = LAM "x" (LAM "y" (LAM "f" (VAR "f" @@ VAR "x" @@ VAR "y")))
`;

val FV_cpair = Store_thm(
  "FV_cpair",
  ``FV cpair = {}``,
  SRW_TAC [][cpair_def, EXTENSION] THEN METIS_TAC []);
val bnf_cpair = Store_thm(
  "bnf_cpair",
  ``bnf cpair``,
  SRW_TAC [][cpair_def]);

val cfst_def = Define`
  cfst = LAM "p" (VAR "p" @@ cB T)
`;
val FV_cfst = Store_thm(
  "FV_cfst",
  ``FV cfst = {}``,
  SRW_TAC [][cfst_def])
val bnf_cfst = Store_thm(
  "bnf_cfst",
  ``bnf cfst``,
  SRW_TAC [][cfst_def]);

val csnd_def = Define`
  csnd = LAM "p" (VAR "p" @@ cB F)
`;
val FV_csnd = Store_thm(
  "FV_csnd",
  ``FV csnd = {}``,
  SRW_TAC [][csnd_def])
val bnf_csnd = Store_thm(
  "bnf_csnd",
  ``bnf csnd``,
  SRW_TAC [][csnd_def]);

val cfst_pair = store_thm(
  "cfst_pair",
  ``cfst @@ (cpair @@ M @@ N) -n->* M``,
  SRW_TAC [][cfst_def, cpair_def] THEN FRESH_TAC THEN 
  SRW_TAC [NORMSTAR_ss][tpm_fresh, cB_behaviour]);

val csnd_pair = store_thm(
  "csnd_pair",
  ``csnd @@ (cpair @@ M @@ N) -n->* N``,
  SRW_TAC [][csnd_def, cpair_def] THEN FRESH_TAC THEN 
  SRW_TAC [NORMSTAR_ss][tpm_fresh, cB_behaviour])

val _ = export_theory()


