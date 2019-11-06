open HolKernel boolLib bossLib Parse binderLib

open chap3Theory
open pred_setTheory
open termTheory
open boolSimps
open normal_orderTheory
open churchboolTheory
open reductionEval

val _ = new_theory "churchpair"

Definition cvpr_def:
  cvpr M N = let v = NEW (FV M ∪ FV N)
             in
               LAM v (VAR v @@ M @@ N)
End

Theorem FV_cvpr[simp]:
  FV (cvpr M N) = FV M ∪ FV N
Proof
  SRW_TAC [][cvpr_def, EXTENSION, LET_THM] THEN
  NEW_ELIM_TAC THEN METIS_TAC []
QED

Theorem bnf_cvpr[simp]:
  bnf (cvpr M N) ⇔ bnf M ∧ bnf N
Proof SRW_TAC [][cvpr_def, LET_THM]
QED

Theorem cvpr_fresh:
  v ∉ FV M ∧ v ∉ FV N ⇒ cvpr M N = LAM v (VAR v @@ M @@ N)
Proof
  SRW_TAC [][LET_THM, cvpr_def] THEN NEW_ELIM_TAC THEN
  SRW_TAC [][LAM_eq_thm, tpm_fresh]
QED

Theorem cvpr_11[simp]:
  cvpr M₁ N₁ = cvpr M₂ N₂ ⇔ M₁ = M₂ ∧ N₁ = N₂
Proof
  Q_TAC (NEW_TAC "z") ‘FV M₁ ∪ FV M₂ ∪ FV N₁ ∪ FV N₂’ THEN
  ‘(cvpr M₁ N₁ = LAM z (VAR z @@ M₁ @@ N₁)) ∧
   (cvpr M₂ N₂ = LAM z (VAR z @@ M₂ @@ N₂))’
     by SRW_TAC [][cvpr_fresh] THEN
  SRW_TAC [][]
QED

Theorem SUB_cvpr[simp]:
  [M/v] (cvpr N P) = cvpr ([M/v]N) ([M/v]P)
Proof
  Q_TAC (NEW_TAC "z") ‘{v} ∪ FV M ∪ FV N ∪ FV P’ THEN
  ‘z ∉ FV ([M/v]N) ∧ z ∉ FV ([M/v]P)’ by SRW_TAC [][termTheory.FV_SUB] THEN
  ‘(cvpr N P = LAM z (VAR z @@ N @@ P)) ∧
   (cvpr ([M/v]N) ([M/v]P) = LAM z (VAR z @@ [M/v]N @@ [M/v]P))’
     by SRW_TAC [][cvpr_fresh] THEN
  SRW_TAC [][]
QED
Theorem tpm_cvpr[simp]:
  tpm pi (cvpr x y) = cvpr (tpm pi x) (tpm pi y)
Proof
  SRW_TAC [][cvpr_def, LET_THM] THEN
  NTAC 2 (NEW_ELIM_TAC THEN SRW_TAC [][]) THEN
  SRW_TAC [CONJ_ss][LAM_eq_thm] THEN
  Cases_on ‘lswapstr pi v = v'’ THEN SRW_TAC [][] THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  MATCH_MP_TAC tpm_fresh THEN SRW_TAC [][]
QED

Definition cpair_def:
  cpair = LAM "x" (LAM "y" (LAM "f" (VAR "f" @@ VAR "x" @@ VAR "y")))
End

Theorem FV_cpair[simp]:    FV cpair = {}
Proof    SRW_TAC [][cpair_def, EXTENSION] THEN METIS_TAC []
QED

Theorem bnf_cpair[simp]:   bnf cpair
Proof    SRW_TAC [][cpair_def]
QED

Theorem cpair_behaviour:
  cpair @@ M @@ N -n->* cvpr M N
Proof
  SRW_TAC [][cpair_def] THEN FRESH_TAC THEN
  MP_TAC (Q.GEN `M` (Q.GEN `N` (Q.INST [`v` |-> `f`] cvpr_fresh))) THEN
  SRW_TAC [][] THEN SRW_TAC [NORMSTAR_ss][]
QED

Theorem wh_cpair:
  cpair @@ x @@ y @@ f -w->* f @@ x @@ y
Proof
  REWRITE_TAC [cpair_def] THEN
  unvarify_tac head_reductionTheory.whstar_substitutive THEN
  ASM_SIMP_TAC (whfy (srw_ss())) []
QED

Definition cfst_def:
  cfst = LAM "p" (VAR "p" @@ cB T)
End
Theorem FV_cfst[simp]:     FV cfst = {}
Proof SRW_TAC [][cfst_def]
QED
Theorem bnf_cfst[simp]:    bnf cfst
Proof SRW_TAC [][cfst_def]
QED

Definition csnd_def:
  csnd = LAM "p" (VAR "p" @@ cB F)
End
Theorem FV_csnd[simp]:     FV csnd = {}
Proof SRW_TAC [][csnd_def]
QED
Theorem bnf_csnd[simp]:    bnf csnd
Proof SRW_TAC [][csnd_def]
QED

Theorem is_abs_cfstsnd[simp]:    is_abs csnd ∧ is_abs cfst
Proof SRW_TAC [][cfst_def, csnd_def]
QED

Theorem cfst_pair:
  cfst @@ (cpair @@ M @@ N) -n->* M
Proof
  SRW_TAC [][cfst_def, cpair_def] THEN FRESH_TAC THEN
  SRW_TAC [NORMSTAR_ss][tpm_fresh, cB_behaviour]
QED
val _ = export_betarwt "cfst_pair"

Theorem csnd_pair:
  csnd @@ (cpair @@ M @@ N) -n->* N
Proof
  SRW_TAC [][csnd_def, cpair_def] THEN FRESH_TAC THEN
  SRW_TAC [NORMSTAR_ss][tpm_fresh, cB_behaviour]
QED
val _ = export_betarwt "csnd_pair"

Theorem cfst_cvpr:
  cfst @@ cvpr M N -n->* M
Proof
  SRW_TAC [][cfst_def, cvpr_def, LET_THM] THEN NEW_ELIM_TAC THEN
  SRW_TAC [NORMSTAR_ss][cB_behaviour]
QED
val _ = export_betarwt "cfst_cvpr"

Theorem csnd_cvpr:
  csnd @@ cvpr M N -n->* N
Proof
  SRW_TAC [][csnd_def, cvpr_def, LET_THM] THEN NEW_ELIM_TAC THEN
  SRW_TAC [NORMSTAR_ss][cB_behaviour]
QED
val _ = export_betarwt "csnd_cvpr"

val _ = export_theory()


