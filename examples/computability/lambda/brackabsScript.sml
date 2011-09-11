open HolKernel Parse reductionEval bossLib boolLib binderLib

open nomsetTheory termTheory

val _ = new_theory "brackabs"

val _ = remove_ovl_mapping "LAM" {Name="LAM", Thy="labelledTerms"}
val _ = clear_overloads_on "FV"
val _ = overload_on ("FV", ``supp term_pmact``)
val _ = remove_ovl_mapping "VAR" {Name="VAR", Thy="labelledTerms"}
val _ = remove_ovl_mapping "APP"  {Name="APP", Thy="labelledTerms"}


val NOT_IN_SUB = prove(
  ``x ∉ FV (M:term) ∧ (x ≠ v ⇒ x ∉ FV N) ⇒ x ∉ FV ([M/v]N)``,
  SRW_TAC [][termTheory.FV_SUB] THEN METIS_TAC []);

val B_I_uncond = store_thm(
  "B_I_uncond",
  ``v ∉ FV M ∧ v ∈ FV N ⇒ (LAM v (M @@ N) == B @@ M @@ (LAM v N))``,
  STRIP_TAC THEN
  ASM_SIMP_TAC (bsrw_ss()) [chap2Theory.B_def] THEN
  REWRITE_TAC [chap2Theory.S_def] THEN
  Q_TAC (NEW_TAC "z") `{"x"; "y"; "z"} ∪ FV M ∪ FV N` THEN
  `LAM "z" (VAR "x" @@ VAR "z" @@ (VAR "y" @@ VAR "z")) =
   LAM z (VAR "x" @@ VAR z @@ (VAR "y" @@ VAR z))`
     by SRW_TAC [][LAM_eq_thm] THEN
  POP_ASSUM SUBST1_TAC THEN
  Q_TAC (NEW_TAC "y") `{"x"; "y"; z} ∪ FV M ∪ FV N` THEN
  `LAM "y" (LAM z (VAR "x" @@ VAR z @@ (VAR "y" @@ VAR z))) =
   LAM y (LAM z (VAR "x" @@ VAR z @@ (VAR y @@ VAR z)))`
     by SRW_TAC [][LAM_eq_thm] THEN
  POP_ASSUM SUBST1_TAC THEN
  ASM_SIMP_TAC (bsrw_ss()) [] THEN
  `∀x y. (x = y) ⇒ (x == y)` by SRW_TAC [][] THEN POP_ASSUM MATCH_MP_TAC THEN
  SRW_TAC [boolSimps.CONJ_ss][LAM_eq_thm, tpm_fresh, NOT_IN_SUB] THEN
  SRW_TAC [][GSYM fresh_tpm_subst, pmact_flip_args]);

val B_I = store_thm(
  "B_I",
  ``v ∉ FV M ∧ v ∈ FV N ∧ N ≠ VAR v ⇒
      (LAM v (M @@ N) == B @@ M @@ (LAM v N))``,
  METIS_TAC [B_I_uncond]);

val C_I = store_thm(
  "C_I",
  ``v ∈ FV M ∧ v ∉ FV N ⇒ LAM v (M @@ N) == C @@ (LAM v M) @@ N``,
  STRIP_TAC THEN ASM_SIMP_TAC (bsrw_ss()) [chap2Theory.C_def] THEN
  REWRITE_TAC [chap2Theory.S_def] THEN
  Q_TAC (NEW_TAC "z") `{"x"; "y"; "z"} ∪ FV M ∪ FV N` THEN
  `LAM "z" (VAR "x" @@ VAR "z" @@ (VAR "y" @@ VAR "z")) =
   LAM z (VAR "x" @@ VAR z @@ (VAR "y" @@ VAR z))`
     by SRW_TAC [][LAM_eq_thm] THEN
  POP_ASSUM SUBST1_TAC THEN
  Q_TAC (NEW_TAC "y") `{"x"; "y"; z} ∪ FV M ∪ FV N` THEN
  `LAM "y" (LAM z (VAR "x" @@ VAR z @@ (VAR "y" @@ VAR z))) =
   LAM y (LAM z (VAR "x" @@ VAR z @@ (VAR y @@ VAR z)))`
     by SRW_TAC [][LAM_eq_thm] THEN
  POP_ASSUM SUBST1_TAC THEN
  ASM_SIMP_TAC (bsrw_ss()) [NOT_IN_SUB] THEN
  `∀x y. (x = y) ⇒ (x == y)` by SRW_TAC [][] THEN POP_ASSUM MATCH_MP_TAC THEN
  SRW_TAC [boolSimps.CONJ_ss][LAM_eq_thm, tpm_fresh, NOT_IN_SUB] THEN
  SRW_TAC [][GSYM fresh_tpm_subst, pmact_flip_args]);

val I_I = store_thm(
  "I_I",
  ``LAM x (VAR x) = I``,
  SIMP_TAC (srw_ss()) [LAM_eq_thm, chap2Theory.I_def]);

val K_I = store_thm(
  "K_I",
  ``v ∉ FV M ⇒ (LAM v M == K @@ M)``,
  STRIP_TAC THEN REWRITE_TAC [chap2Theory.K_def] THEN
  Q_TAC (NEW_TAC "y") `{"x"; "y"} ∪ FV M` THEN
  `LAM "y" (VAR "x") = LAM y (VAR "x")` by SRW_TAC [][LAM_eq_thm] THEN
  POP_ASSUM SUBST1_TAC THEN
  ASM_SIMP_TAC (bsrw_ss()) [] THEN
  `∀x y. (x = y) ⇒ (x == y)` by SRW_TAC [][] THEN POP_ASSUM MATCH_MP_TAC THEN
  SRW_TAC [boolSimps.CONJ_ss][LAM_eq_thm, tpm_fresh, NOT_IN_SUB]);

val S_I = store_thm(
  "S_I",
  ``v ∈ FV M ∧ v ∈ FV N ⇒
    LAM v (M @@ N) == S @@ (LAM v M) @@ (LAM v N)``,
  STRIP_TAC THEN REWRITE_TAC [chap2Theory.S_def] THEN
  Q_TAC (NEW_TAC "z") `{"x"; "y"; "z"} ∪ FV M ∪ FV N` THEN
  `LAM "z" (VAR "x" @@ VAR "z" @@ (VAR "y" @@ VAR "z")) =
   LAM z (VAR "x" @@ VAR z @@ (VAR "y" @@ VAR z))`
     by SRW_TAC [][LAM_eq_thm] THEN
  POP_ASSUM SUBST1_TAC THEN
  Q_TAC (NEW_TAC "y") `{"x"; "y"; z} ∪ FV M ∪ FV N` THEN
  `LAM "y" (LAM z (VAR "x" @@ VAR z @@ (VAR "y" @@ VAR z))) =
   LAM y (LAM z (VAR "x" @@ VAR z @@ (VAR y @@ VAR z)))`
     by SRW_TAC [][LAM_eq_thm] THEN
  POP_ASSUM SUBST1_TAC THEN
  ASM_SIMP_TAC (bsrw_ss()) [NOT_IN_SUB] THEN
  `LAM v (M @@ N) = LAM z ([VAR z/v] (M @@ N))`
     by SRW_TAC [][SIMPLE_ALPHA] THEN
  SRW_TAC [][]);

val fake_eta = store_thm(
  "fake_eta",
  ``v ∉ FV M ∧ is_abs M ⇒ (LAM v (M @@ VAR v) == M)``,
  STRIP_TAC THEN
  `∃u M0. M = LAM u M0`
     by (Q.SPEC_THEN `M` FULL_STRUCT_CASES_TAC term_CASES THEN
         FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []) THEN
  ASM_SIMP_TAC (bsrw_ss()) [] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `v = u` THEN SRW_TAC [][] THEN RES_TAC THEN
  `LAM u M0 = LAM v ([VAR v/u] M0)` by SRW_TAC [][SIMPLE_ALPHA] THEN
  SRW_TAC [][]);


val B_eta = store_thm(
  "B_eta",
  ``LAM v (B @@ VAR v) == B``,
  SIMP_TAC (bsrw_ss()) [chap2Theory.B_def] THEN
  `S @@ (K @@ S) @@ K =
   LAM "x" (LAM "y" (LAM "z" (VAR "x" @@ VAR "z" @@ (VAR "y" @@ VAR "z")))) @@
       (K @@ S) @@ K`
     by SRW_TAC [][chap2Theory.S_def] THEN
  ASM_SIMP_TAC (bsrw_ss()) [] THEN
  `∀x y. (x = y) ⇒ x == y` by SRW_TAC [][] THEN
  POP_ASSUM MATCH_MP_TAC THEN
  SRW_TAC [][LAM_eq_thm, tpm_fresh]);


val _ = export_theory()
