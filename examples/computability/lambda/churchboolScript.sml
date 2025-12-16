Theory churchbool
Ancestors
  chap3 pred_set term normal_order head_reduction
Libs
  binderLib boolSimps reductionEval

val _ = set_trace "Unicode" 1

val _ = remove_ovl_mapping "LAM" {Name="LAM", Thy="labelledTerms"}
val _ = clear_overloads_on "FV"
val _ = overload_on ("FV", ``supp term_pmact``)
val _ = remove_ovl_mapping "VAR" {Name="VAR", Thy="labelledTerms"}
val _ = remove_ovl_mapping "APP"  {Name="APP", Thy="labelledTerms"}

fun Store_thm(n,t,tac) = store_thm(n,t,tac) before export_rewrites [n]

Definition cB_def:  cB p = LAM "x" (LAM "y" (VAR (if p then "x" else "y")))
End
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

val cB_lameq11 = Store_thm(
  "cB_lameq11",
  ``(cB p == cB q) ⇔ (p ⇔ q)``,
  EQ_TAC THEN SRW_TAC [][] THEN
  `∃Z. cB p -β->* Z ∧ cB q -β->* Z`
    by METIS_TAC [beta_CR, theorem3_13, prop3_18] THEN
  `cB p = cB q`
    by METIS_TAC [corollary3_2_1, beta_normal_form_bnf, bnf_cB] THEN
  FULL_SIMP_TAC (srw_ss()) [])

Theorem cB_behaviour:
    cB T @@ x @@ y -n->* x ∧ cB F @@ x @@ y -n->* y
Proof
  SRW_TAC [][cB_def] THEN FRESH_TAC THEN
  SRW_TAC [NORMSTAR_ss][]
QED

Theorem wh_cB:
    cB T @@ x @@ y -w->* x ∧ cB F @@ x @@ y -w->* y
Proof
  REWRITE_TAC [cB_def] THEN CONJ_TAC THEN unvarify_tac whstar_substitutive THEN
  ASM_SIMP_TAC (whfy (srw_ss())) []
QED
val _ = export_betarwt "wh_cB"

Definition cnot_def:
  cnot = LAM "b" (VAR "b" @@ cB F @@ cB T)
End
val FV_cnot = Store_thm(
  "FV_cnot",
  ``FV cnot = {}``,
  SRW_TAC [][cnot_def, EXTENSION])
val bnf_cnot = Store_thm(
  "bnf_cnot",
  ``bnf cnot``,
  SRW_TAC [][cnot_def]);
Theorem cnot_behaviour:
    cnot @@ cB p -n->* cB (¬p)
Proof
  Cases_on `p` THEN
  SIMP_TAC (bsrw_ss()) [cnot_def]
QED
val _ = export_betarwt "cnot_behaviour"

Definition cand_def:
  cand = LAM "p" (LAM "q" (VAR "p" @@ VAR "q" @@ cB F))
End
val FV_cand = Store_thm(
  "FV_cand",
  ``FV cand = {}``,
  SRW_TAC [][cand_def, EXTENSION] THEN METIS_TAC []);
val bnf_cand = Store_thm(
  "bnf_cand",
  ``bnf cand``,
  SRW_TAC [][cand_def]);
val is_abs_cand = Store_thm(
  "is_abs_cand",
  ``is_abs cand``,
  SRW_TAC [][cand_def]);
Theorem cand_behaviour:
    cand @@ cB p @@ cB q -n->* cB (p /\ q)
Proof
  SIMP_TAC (bsrw_ss()) [cand_def] THEN
  Cases_on `p` THEN SIMP_TAC (bsrw_ss()) []
QED
val _ = export_betarwt "cand_behaviour"

Theorem wh_cand:
    cand @@ b1 @@ b2 -w->* b1 @@ b2 @@ cB F
Proof
  REWRITE_TAC [cand_def] THEN unvarify_tac whstar_substitutive THEN
  ASM_SIMP_TAC (whfy(srw_ss())) []
QED

Theorem cand_F1:
    cand @@ cB F @@ X -n->* cB F
Proof
  SIMP_TAC (bsrw_ss()) [cand_def]
QED
val _ = export_betarwt "cand_F1"

Theorem cand_T1:
    cand @@ cB T @@ X -w->* X
Proof
  unvarify_tac whstar_substitutive THEN
  SIMP_TAC (whfy(srw_ss())) [wh_cand, wh_cB]
QED

Definition cor_def:
  cor = LAM "p" (LAM "q" (VAR "p" @@ cB T @@ VAR "q"))
End
val FV_cor = Store_thm(
  "FV_cor",
  ``FV cor = {}``,
  SRW_TAC [][cor_def, EXTENSION] THEN METIS_TAC []);
val bnf_cor = Store_thm(
  "bnf_cor",
  ``bnf cor``,
  SRW_TAC [][cor_def]);

Theorem cor_behaviour:
    cor @@ cB p @@ cB q -n->* cB (p ∨ q)
Proof
  SIMP_TAC (bsrw_ss()) [cor_def] THEN
  Cases_on `p` THEN SIMP_TAC (bsrw_ss()) []
QED
val _ = export_betarwt "cor_behaviour"

Theorem cor_T1:
    cor @@ cB T @@ X == cB T
Proof
  SIMP_TAC (bsrw_ss()) [cor_def]
QED
val _ = export_betarwt "cor_T1"

Theorem cor_F1:
    cor @@ cB F @@ X == X
Proof
  SIMP_TAC (bsrw_ss()) [cor_def]
QED
val _ = export_betarwt "cor_F1"

val cB_mynames = prove(
  ``x ≠ y ⇒ (cB p = LAM x (LAM y (VAR (if p then x else y))))``,
  SRW_TAC [DNF_ss][cB_def, LAM_eq_thm] THEN
  SRW_TAC [][basic_swapTheory.swapstr_def] THEN METIS_TAC []);

Theorem whead_tests:
    (M == cB T ⇒ M @@ x @@ y -w->* x) ∧
    (M == cB F ⇒ M @@ x @@ y -w->* y)
Proof
  Q_TAC SUFF_TAC `∀M b x y. M == cB b ⇒ M @@ x @@ y -w->* if b then x else y`
        THEN1 METIS_TAC [] THEN
  REPEAT STRIP_TAC THEN
  `M -n->* cB b` by (MATCH_MP_TAC normal_finds_bnf THEN
                     SRW_TAC [][betastar_lameq_bnf]) THEN
  Q_TAC (NEW_TAC "u") `FV M ∪ FV x ∪ FV y` THEN
  Q_TAC (NEW_TAC "v") `{u} ∪ FV M ∪ FV x ∪ FV y` THEN
  ASSUME_TAC (MATCH_MP (GEN_ALL cB_mynames) (ASSUME ``v:string ≠ u``)) THEN
  `∃M0. M -w->* LAM v M0 ∧ M0 -n->* LAM u (VAR (if b then v else u))`
     by METIS_TAC [normstar_to_abs_wstar] THEN
  `M @@ x @@ y -w->* LAM v M0 @@ x @@ y`
     by ASM_SIMP_TAC (srw_ss()) [wh_app_congL] THEN
  `LAM v M0 @@ x -w->* [x/v]M0`
     by METIS_TAC [relationTheory.RTC_SINGLE, weak_head_rules] THEN
  `LAM v M0 @@ x @@ y -w->* [x/v]M0 @@ y`
     by METIS_TAC [relationTheory.RTC_CASES_RTC_TWICE,
                   wh_app_congL] THEN
  `∃M1. M0 -w->* LAM u M1 ∧ M1 -n->* VAR (if b then v else u)`
     by (MATCH_MP_TAC normstar_to_abs_wstar THEN
         `u ∉ FV (LAM v M0)` by METIS_TAC [whstar_FV] THEN
         POP_ASSUM MP_TAC THEN SRW_TAC [][]) THEN
  `[x/v]M0 -w->* [x/v](LAM u M1)` by METIS_TAC [whstar_substitutive] THEN
  `[x/v]M0 -w->* LAM u ([x/v]M1)` by (POP_ASSUM MP_TAC THEN SRW_TAC [][]) THEN
  `M1 -w->* VAR (if b then v else u)`
     by SRW_TAC [][normstar_to_vheadnullary_wstar] THEN
  `[x/v] M0 @@ y -w->* LAM u ([x/v]M1) @@ y`
     by METIS_TAC [wh_app_congL] THEN
  `LAM u ([x/v]M1) @@ y -w->* [y/u]([x/v]M1)`
     by METIS_TAC [weak_head_rules, relationTheory.RTC_SINGLE] THEN
  `[y/u]([x/v]M1) -w->* [y/u]([x/v] (VAR (if b then v else u)))`
     by METIS_TAC [whstar_substitutive] THEN
  POP_ASSUM MP_TAC THEN
  Cases_on `b` THEN ASM_SIMP_TAC (srw_ss()) [lemma14b] THEN
  METIS_TAC [relationTheory.RTC_CASES_RTC_TWICE]
QED

Theorem wh_S:
    S @@ f @@ g @@ x -w->* f @@ x @@ (g @@ x)
Proof
  REWRITE_TAC [chap2Theory.S_def] THEN unvarify_tac whstar_substitutive THEN
  ASM_SIMP_TAC (whfy (srw_ss())) []
QED

Theorem wh_K:
    K @@ x @@ y -w->* x
Proof
  REWRITE_TAC [chap2Theory.K_def] THEN unvarify_tac whstar_substitutive THEN
  ASM_SIMP_TAC (whfy (srw_ss())) []
QED

Theorem wh_B:
    B @@ f @@ g @@ x -w->* f @@ (g @@ x)
Proof
  unvarify_tac whstar_substitutive THEN
  SIMP_TAC (whfy(srw_ss())) [chap2Theory.B_def, wh_S, wh_K]
QED

