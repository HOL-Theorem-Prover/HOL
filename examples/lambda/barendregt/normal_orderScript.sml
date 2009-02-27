open HolKernel Parse boolLib bossLib

open boolSimps pred_setTheory pathTheory binderLib
open chap3Theory standardisationTheory term_posnsTheory termTheory
     finite_developmentsTheory

val _ = new_theory "normal_order"

val _ = set_trace "Unicode" 1

val (normorder_rules, normorder_ind, normorder_cases) = Hol_reln`
  (∀v M N. normorder (LAM v M @@ N) ([N/v]M)) ∧
  (∀v M1 M2. normorder M1 M2 ⇒ normorder (LAM v M1) (LAM v M2)) ∧
  (∀M1 M2 N. normorder M1 M2 ∧ ¬is_abs M1 ⇒ normorder (M1 @@ N) (M2 @@ N)) ∧
  (∀M N1 N2. normorder N1 N2 ∧ bnf M ∧ ¬is_abs M ⇒
              normorder (M @@ N1) (M @@ N2))
`;

val _ = set_fixity "-n->" (Infix(NONASSOC,450))
val _ = overload_on ("-n->", ``normorder``)
val _ = set_fixity "-n->*" (Infix(NONASSOC,450))
val _ = overload_on ("-n->*", ``RTC normorder``)

val tpm_normorder_I = store_thm(
  "tpm_normorder_I",
  ``∀M N. M -n-> N ⇒ ∀pi. tpm pi M -n-> tpm pi N``,
  HO_MATCH_MP_TAC normorder_ind THEN SRW_TAC [][normorder_rules, tpm_subst]);

val tpm_normorder_eqn = store_thm(
  "tpm_normorder_eqn",
  ``tpm pi M -n-> tpm pi N ⇔ M -n-> N``,
  METIS_TAC [tpm_inverse, tpm_normorder_I]);
val _ = export_rewrites ["tpm_normorder_eqn"]

val normorder_ccbeta = store_thm(
  "normorder_ccbeta",
  ``∀M N. M -n-> N ⇒ compat_closure beta M N``,
  HO_MATCH_MP_TAC normorder_ind THEN SRW_TAC [][compat_closure_rules] THEN
  METIS_TAC [compat_closure_rules, beta_def]);

val normorder_FV = store_thm(
  "normorder_FV",
  ``M -n-> N ∧ v ∈ FV N ⇒ v ∈ FV M``,
  METIS_TAC [normorder_ccbeta, cc_beta_FV_SUBSET, SUBSET_DEF]);

val normorder_rwts = store_thm(
  "normorder_rwts",
  ``(VAR s -n-> N ⇔ F) ∧
    (LAM v M -n-> N ⇔ ∃M'. (N = LAM v M') ∧ M -n-> M') ∧
    (LAM v M @@ N -n-> P ⇔ (P = [N/v]M)) ∧
    (¬is_abs M ⇒ (M @@ N -n-> P ⇔
                   (bnf M ∧ ∃N'. (P = M @@ N') ∧ N -n-> N') ∨
                   ∃M'. (P = M' @@ N) ∧ M -n-> M'))``,
  SRW_TAC [][] THENL [
    SRW_TAC [][Once normorder_cases],

    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [normorder_cases])) THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [LAM_eq_thm, tpm_eqr] THEN
    SRW_TAC [][EQ_IMP_THM] THEN1 SRW_TAC [][] THEN
    Q.EXISTS_TAC `tpm [(v,v')] M2` THEN
    `v ∉ FV (tpm [(v,v')] M)` by SRW_TAC [][] THEN
    `v ∉ FV M2` by METIS_TAC [normorder_FV] THEN
    SRW_TAC [][LAM_eq_thm, tpm_flip_args] THEN
    METIS_TAC [tpm_sing_inv, tpm_normorder_I],

    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [normorder_cases])) THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [LAM_eq_thm, tpm_eqr] THEN
    SRW_TAC [][EQ_IMP_THM] THEN
    METIS_TAC [fresh_tpm_subst, lemma15a, tpm_flip_args],

    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [normorder_cases])) THEN
    SRW_TAC [][EQ_IMP_THM] THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);


val normorder_bnf = store_thm(
  "normorder_bnf",
  ``bnf M ⇔ ∀N. ¬(M -n-> N)``,
  Q.ID_SPEC_TAC `M` THEN HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][normorder_rwts] THEN
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, normorder_rwts] THEN
  Cases_on `is_abs M` THENL [
    `∃v M0. M = LAM v M0`
      by (Q.SPEC_THEN `M` FULL_STRUCT_CASES_TAC term_CASES THEN
          FULL_SIMP_TAC (srw_ss()) [normorder_rwts] THEN
          METIS_TAC []) THEN
    SRW_TAC [][normorder_rwts],

    SRW_TAC [][normorder_rwts] THEN
    METIS_TAC [simpLib.SIMP_PROVE (srw_ss()) []
              ``∀M1 M2 N1 N2. (M1 @@ N1:term = M2 @@ N2) ⇔
                               (M1 = M2) ∧ (N1 = N2)``]
  ]);

val strong_normorder_ind =
    IndDefLib.derive_strong_induction (normorder_rules, normorder_ind)

val normorder_det = store_thm(
  "normorder_det",
  ``∀M N. M -n-> N ⇒ ∀N'. M -n-> N' ⇒ (N' = N)``,
  HO_MATCH_MP_TAC strong_normorder_ind THEN
  SRW_TAC [][normorder_rwts] THEN
  METIS_TAC [normorder_bnf]);

val noposn_def = define_recursive_term_function`
  (noposn (VAR s) = NONE) ∧
  (noposn (M @@ N) = if is_abs M then SOME []
                     else case noposn M of
                             NONE -> OPTION_MAP (CONS Rt) (noposn N)
                          || SOME p -> SOME (Lt::p)) ∧
  (noposn (LAM v M) = OPTION_MAP (CONS In) (noposn M))
`;
val _ = export_rewrites ["noposn_def"]

val bnf_noposn = store_thm(
  "bnf_noposn",
  ``∀M. bnf M ⇔ (noposn M = NONE)``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][] THEN Cases_on `noposn M` THEN SRW_TAC [][])

val normorder_noposn = store_thm(
  "normorder_noposn",
  ``M -n-> N ⇔ ∃p. (noposn M = SOME p) ∧ labelled_redn beta M p N``,
  EQ_TAC THENL [
    Q_TAC SUFF_TAC
     `∀M N. M -n-> N ⇒ ∃p. (noposn M = SOME p) ∧ labelled_redn beta M p N`
     THEN1 METIS_TAC [] THEN
    HO_MATCH_MP_TAC normorder_ind THEN SRW_TAC [][bnf_noposn] THEN
    SRW_TAC [][labelled_redn_rules] THEN
    METIS_TAC [labelled_redn_rules, beta_def],

    Q_TAC SUFF_TAC
      `∀M p N. labelled_redn beta M p N ⇒
                (noposn M = SOME p) ⇒ M -n-> N` THEN1 METIS_TAC [] THEN
    HO_MATCH_MP_TAC labelled_redn_ind THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [beta_def, normorder_rules] THEN
    SRW_TAC [][] THENL [
      Cases_on `noposn M` THEN FULL_SIMP_TAC (srw_ss()) [normorder_rules],
      Cases_on `noposn z` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [bnf_noposn, normorder_rules]
    ]
  ]);

val noposn_least = store_thm(
  "noposn_least",
  ``∀M p.
      (noposn M = SOME p) ⇒ p ∈ redex_posns M ∧
                            ∀p'. p' ∈ redex_posns M ⇒
                                 (p' = p) ∨ p < p'``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][redex_posns_def] THENL [
    Cases_on `noposn M` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][],
    Cases_on `noposn M` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
      `∃N. labelled_redn beta M x N`
         by METIS_TAC [is_redex_occurrence_def, IN_term_IN_redex_posns] THEN
      `bnf M` by METIS_TAC [bnf_noposn] THEN
      METIS_TAC [labelled_redn_cc, beta_normal_form_bnf, corollary3_2_1],
      SRW_TAC [][]
    ],

    Cases_on `noposn M` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][]
  ]);

val normorder_reduction_def = Define`
  normorder_reduction p =
    okpath (λM r N. (noposn M = SOME r) ∧ labelled_redn beta M r N) p
`
val normorder_is_standard = store_thm(
  "normorder_is_standard",
  ``∀p. normorder_reduction p ⇒ standard_reduction p``,
  HO_MATCH_MP_TAC standard_coind THEN
  SRW_TAC [][normorder_reduction_def] THEN
  METIS_TAC [posn_lt_antisym, posn_lt_irrefl, noposn_least]);

val ihr_noposn = store_thm(
  "ihr_noposn",
  ``∀r M. r is_head_redex M ⇒ (noposn M = SOME r)``,
  HO_MATCH_MP_TAC is_head_redex_ind THEN SRW_TAC [][]);

val head_is_normorder = store_thm(
  "head_is_normorder",
  ``∀p. is_head_reduction p ⇒ normorder_reduction p``,
  SIMP_TAC (srw_ss()) [normorder_reduction_def] THEN
  HO_MATCH_MP_TAC okpath_co_ind THEN
  SRW_TAC [][is_head_reduction_thm, ihr_noposn]);

val ADD1 = arithmeticTheory.ADD1

val last_el = store_thm(
  "last_el", 
  ``∀p. finite p ⇒ 
        (last p = el (THE (length p) - 1) p)``,
  HO_MATCH_MP_TAC finite_path_ind THEN SRW_TAC [][length_thm] THEN 
  Q_TAC SUFF_TAC `∃n. length p = SOME (SUC n)`
        THEN1 SIMP_TAC (srw_ss() ++ DNF_ss ++ ARITH_ss) [] THEN 
  METIS_TAC [finite_length, length_never_zero, arithmeticTheory.num_CASES]);

val standard_to_bnf_is_normal = store_thm(
  "standard_to_bnf_is_normal",
  ``∀p. standard_reduction p ∧ finite p ∧ bnf (last p) ⇒
        normorder_reduction p``,
  SIMP_TAC (srw_ss()) [normorder_reduction_def] THEN 
  HO_MATCH_MP_TAC okpath_co_ind THEN 
  SRW_TAC [][standard_reduction_thm] THEN 
  `∃r₀. noposn M = SOME r₀`
     by (Cases_on `noposn M` THEN SRW_TAC [][] THEN
         `bnf M` by METIS_TAC [bnf_noposn] THEN 
         METIS_TAC [labelled_redn_cc, beta_normal_form_bnf, 
                    corollary3_2_1]) THEN 
  `r₀ ∈ redex_posns M ∧ ∀r'. r' ∈ redex_posns M ⇒ (r' = r₀) ∨ r₀ < r'`
     by METIS_TAC [noposn_least] THEN 
  `r ∈ redex_posns M` by METIS_TAC [labelled_redn_beta_redex_posn] THEN 
  `(r = r₀) ∨ r₀ < r` by METIS_TAC [] THEN1 SRW_TAC [][] THEN 
  `okpath (labelled_redn beta) p` by METIS_TAC [standard_reductions_ok] THEN 
  `∀n. n ∈ PL p ⇒ r₀ ∈ redex_posns (el n p)`
     by (Induct THEN SRW_TAC [][] THENL [
           METIS_TAC [lr_beta_preserves_lefter_redexes],
           `labelled_redn beta (el n p) (nth_label n p) (el (SUC n) p)`
               by METIS_TAC [okpath_every_el_relates] THEN 
           `n ∈ PL p` 
               by METIS_TAC [PL_downward_closed, DECIDE ``x < SUC x``] THEN
           METIS_TAC [lr_beta_preserves_lefter_redexes, ADD1, el_def]
         ]) THEN 
  `∃m. 0 < m ∧ (length p = SOME m)`
     by METIS_TAC [finite_length, length_never_zero, 
                   DECIDE ``0 < x ⇔ x ≠ 0``] THEN 
  `last p = el (m - 1) p` 
     by METIS_TAC [last_el, optionTheory.option_CLAUSES] THEN 
  `m - 1 ∈ PL p` by SRW_TAC [][PL_def] THEN 
  `r₀ ∈ redex_posns (last p)` by METIS_TAC [] THEN 
  `∃N. labelled_redn beta (last p) r₀ N`
     by METIS_TAC [is_redex_occurrence_def, IN_term_IN_redex_posns] THEN 
  METIS_TAC [labelled_redn_cc, beta_normal_form_bnf, corollary3_2_1]);
    
val finite_normorder_RTC = store_thm(
  "finite_normorder_RTC",
  ``∀p. normorder_reduction p ∧ finite p ⇒ first p -n->* last p``,
  REWRITE_TAC [normorder_reduction_def] THEN 
  HO_MATCH_MP_TAC finite_okpath_ind THEN SRW_TAC [][] THEN 
  METIS_TAC [normorder_noposn, relationTheory.RTC_RULES]);
  
  
val normal_finds_bnf = store_thm(
  "normal_find_bnf",
  ``RTC (compat_closure beta) M N /\ bnf N ⇒ M -n->* N``,
  SRW_TAC [][] THEN 
  `∃p. (first p = M) ∧ finite p ∧ (last p = N) ∧ 
       standard_reduction p`
    by METIS_TAC [standardisation_theorem, reduction_def] THEN 
  METIS_TAC [standard_to_bnf_is_normal, finite_normorder_RTC]);
           
  

val _ = export_theory()
