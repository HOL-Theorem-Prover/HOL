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

val cvpr_def = Define`
  cvpr M N = let v = NEW (FV M ∪ FV N)
             in
               LAM v (VAR v @@ M @@ N)
`;

val FV_cvpr = Store_thm(
  "FV_cvpr",
  ``FV (cvpr M N) = FV M ∪ FV N``,
  SRW_TAC [][cvpr_def, EXTENSION, LET_THM] THEN
  NEW_ELIM_TAC THEN METIS_TAC []);
val bnf_cvpr = Store_thm(
  "bnf_cvpr",
  ``bnf (cvpr M N) = bnf M ∧ bnf N``,
  SRW_TAC [][cvpr_def, LET_THM]);

val cvpr_fresh = store_thm(
  "cvpr_fresh",
  ``v ∉ FV M ∧ v ∉ FV N ⇒ (cvpr M N = LAM v (VAR v @@ M @@ N))``,
  SRW_TAC [][LET_THM, cvpr_def] THEN NEW_ELIM_TAC THEN
  SRW_TAC [][LAM_eq_thm, tpm_fresh]);

val cvpr_11 = Store_thm(
  "cvpr_11",
  ``(cvpr M₁ N₁ = cvpr M₂ N₂) = (M₁ = M₂) ∧ (N₁ = N₂)``,
  Q_TAC (NEW_TAC "z") `FV M₁ ∪ FV M₂ ∪ FV N₁ ∪ FV N₂` THEN
  `(cvpr M₁ N₁ = LAM z (VAR z @@ M₁ @@ N₁)) ∧
   (cvpr M₂ N₂ = LAM z (VAR z @@ M₂ @@ N₂))`
     by SRW_TAC [][cvpr_fresh] THEN
  SRW_TAC [][]);

val SUB_cvpr = Store_thm(
  "SUB_cvpr",
  ``[M/v] (cvpr N P) = cvpr ([M/v]N) ([M/v]P)``,
  Q_TAC (NEW_TAC "z") `{v} ∪ FV M ∪ FV N ∪ FV P` THEN
  `z ∉ FV ([M/v]N) ∧ z ∉ FV ([M/v]P)`
     by SRW_TAC [][termTheory.FV_SUB] THEN
  `(cvpr N P = LAM z (VAR z @@ N @@ P)) ∧
   (cvpr ([M/v]N) ([M/v]P) = LAM z (VAR z @@ [M/v]N @@ [M/v]P))`
     by SRW_TAC [][cvpr_fresh] THEN
  SRW_TAC [][]);
val tpm_cvpr = Store_thm(
  "tpm_cvpr",
  ``tpm pi (cvpr x y) = cvpr (tpm pi x) (tpm pi y)``,
  SRW_TAC [][cvpr_def, LET_THM] THEN
  NTAC 2 (NEW_ELIM_TAC THEN SRW_TAC [][]) THEN
  SRW_TAC [CONJ_ss][LAM_eq_thm] THEN
  Cases_on `lswapstr pi v = v'` THEN SRW_TAC [][nomsetTheory.stringpm_raw] THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  MATCH_MP_TAC tpm_fresh THEN SRW_TAC [][nomsetTheory.stringpm_raw]);

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
val cpair_behaviour = store_thm(
  "cpair_behaviour",
  ``cpair @@ M @@ N -n->* cvpr M N``,
  SRW_TAC [][cpair_def] THEN FRESH_TAC THEN
  MP_TAC (Q.GEN `M` (Q.GEN `N` (Q.INST [`v` |-> `f`] cvpr_fresh))) THEN
  SRW_TAC [][] THEN
  SRW_TAC [NORMSTAR_ss][]);

val wh_cpair = store_thm(
  "wh_cpair",
  ``cpair @@ x @@ y @@ f -w->* f @@ x @@ y``,
  REWRITE_TAC [cpair_def] THEN
  unvarify_tac head_reductionTheory.whstar_substitutive THEN
  ASM_SIMP_TAC (whfy (srw_ss())) []);



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

val is_abs_cfstsnd = Store_thm(
  "is_abs_cfstsnd",
  ``is_abs csnd ∧ is_abs cfst``,
  SRW_TAC [][cfst_def, csnd_def]);

val cfst_pair = store_thm(
  "cfst_pair",
  ``cfst @@ (cpair @@ M @@ N) -n->* M``,
  SRW_TAC [][cfst_def, cpair_def] THEN FRESH_TAC THEN
  SRW_TAC [NORMSTAR_ss][tpm_fresh, cB_behaviour]);
val _ = export_betarwt "cfst_pair"

val csnd_pair = store_thm(
  "csnd_pair",
  ``csnd @@ (cpair @@ M @@ N) -n->* N``,
  SRW_TAC [][csnd_def, cpair_def] THEN FRESH_TAC THEN
  SRW_TAC [NORMSTAR_ss][tpm_fresh, cB_behaviour])
val _ = export_betarwt "csnd_pair"

val cfst_cvpr = store_thm(
  "cfst_cvpr",
  ``cfst @@ cvpr M N -n->* M``,
  SRW_TAC [][cfst_def, cvpr_def, LET_THM] THEN NEW_ELIM_TAC THEN
  SRW_TAC [NORMSTAR_ss][cB_behaviour]);
val _ = export_betarwt "cfst_cvpr"

val csnd_cvpr = store_thm(
  "csnd_cvpr",
  ``csnd @@ cvpr M N -n->* N``,
  SRW_TAC [][csnd_def, cvpr_def, LET_THM] THEN NEW_ELIM_TAC THEN
  SRW_TAC [NORMSTAR_ss][cB_behaviour]);
val _ = export_betarwt "csnd_cvpr"

val _ = export_theory()


