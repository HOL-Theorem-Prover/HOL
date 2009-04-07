open HolKernel Parse boolLib bossLib

open boolSimps pred_setTheory pathTheory binderLib
open chap3Theory standardisationTheory term_posnsTheory termTheory
     finite_developmentsTheory

val _ = new_theory "normal_order"

val _ = set_trace "Unicode" 1

fun Store_thm(trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

(* ----------------------------------------------------------------------
    Normal order reduction

    This relation is a bit monstrous really.  In particular, nice
    properties of β-reduction don't necessarily translate across.  For
    example, substitutivity doesn't hold.  This would have that

     M -n-> N ⇒ [P/v]M -n-> [P/v]N

    but this isn't true because the variable v might be at the head
    position in M, and P might contain a redex.  Then the reduction
    that was OK on the left has to be deferred for the reduction in P
    on the right.
   ---------------------------------------------------------------------- *)

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

val normorder_bvc_gen_ind = store_thm(
  "normorder_bvc_gen_ind",
  ``∀P f.
      (∀x. FINITE (f x)) ∧
      (∀v M N x. v ∉ FV N ∧ v ∉ f x ⇒ P (LAM v M @@ N) ([N/v]M) x) ∧
      (∀v M N x. v ∉ f x ∧ (∀y. P M N y) ⇒ P (LAM v M) (LAM v N) x) ∧
      (∀M1 M2 N x. (∀y. P M1 M2 y) ∧ ¬is_abs M1 ⇒ P (M1 @@ N) (M2 @@ N) x) ∧
      (∀M N1 N2 x.
         (∀y. P N1 N2 y) ∧ bnf M ∧ ¬is_abs M ⇒ P (M @@ N1) (M @@ N2) x)
     ⇒
      ∀M N. M -n-> N ⇒ ∀x. P M N x``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC
        `∀M N. M -n-> N ⇒ ∀π x. P (tpm π M) (tpm π N) x`
        THEN1 METIS_TAC [tpm_NIL] THEN
  HO_MATCH_MP_TAC normorder_ind THEN SRW_TAC [][] THENL [
    SRW_TAC [][tpm_subst] THEN
    Q_TAC (NEW_TAC "z")
          `{lswapstr π v} ∪ FV (tpm π N) ∪ f x ∪ FV (tpm π M)` THEN
    `LAM (lswapstr π v) (tpm π M) = LAM z ([VAR z/lswapstr π v] (tpm π M))`
       by SRW_TAC [][SIMPLE_ALPHA] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    `[tpm π N/lswapstr π v](tpm π M) =
     [tpm π N/z] ([VAR z/lswapstr π v](tpm π M))`
        by SRW_TAC [][lemma15a] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][],

    Q_TAC (NEW_TAC "z")
          `{lswapstr π v} ∪ FV (tpm π M) ∪ FV (tpm π N) ∪ f x` THEN
    `(LAM (lswapstr π v) (tpm π M) = LAM z (tpm [(z, lswapstr π v)] (tpm π M)))
         ∧
     (LAM (lswapstr π v) (tpm π N) = LAM z (tpm [(z, lswapstr π v)] (tpm π N)))`
        by SRW_TAC [][tpm_ALPHA] THEN
    NTAC 2 (POP_ASSUM SUBST_ALL_TAC) THEN
    SRW_TAC [][GSYM tpm_APPEND]
  ]);

infix |> fun x |> f = f x
val normorder_bvc_ind = save_thm(
  "normorder_bvc_ind",
  normorder_bvc_gen_ind |> SPEC_ALL
                        |> Q.INST [`P` |-> `λM N x. P1 M N`, `f` |-> `λx. X`]
                        |> SIMP_RULE (srw_ss()) []
                        |> Q.INST [`P1` |-> `P`]
                        |> Q.GEN `X` |> Q.GEN `P`);

val normorder_ccbeta = store_thm(
  "normorder_ccbeta",
  ``∀M N. M -n-> N ⇒ M -β-> N``,
  HO_MATCH_MP_TAC normorder_ind THEN SRW_TAC [][compat_closure_rules] THEN
  METIS_TAC [compat_closure_rules, beta_def]);

val normorder_lameq = store_thm(
  "normorder_lameq",
  ``∀M N. M -n-> N ⇒ M == N``,
  SRW_TAC [][normorder_ccbeta, ccbeta_lameq]);

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
  "normal_finds_bnf",
  ``M -β->* N /\ bnf N ⇒ M -n->* N``,
  SRW_TAC [][] THEN
  `∃p. (first p = M) ∧ finite p ∧ (last p = N) ∧ standard_reduction p`
    by METIS_TAC [standardisation_theorem] THEN
  METIS_TAC [standard_to_bnf_is_normal, finite_normorder_RTC]);

val nstar_betastar = store_thm(
  "nstar_betastar",
  ``∀M N. M -n->* N ⇒ M -β->* N``,
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
  METIS_TAC [relationTheory.RTC_RULES, normorder_ccbeta]);

val nstar_lameq = store_thm(
  "nstar_lameq",
  ``∀M N. M -n->* N ⇒ M == N``,
  SRW_TAC [][nstar_betastar, betastar_lameq]);

val nstar_betastar_bnf = store_thm(
  "nstar_betastar_bnf",
  ``bnf N ⇒ (M -n->* N ⇔ M -β->* N)``,
  METIS_TAC [normal_finds_bnf, nstar_betastar]);

val normstar_LAM = store_thm(
  "normstar_LAM",
  ``∀M N. LAM x M -n->* LAM x N ⇔ M -n->* N``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, FORALL_AND_THM] THEN CONJ_TAC THENL [
    Q_TAC SUFF_TAC `∀M N. M -n->* N ⇒
                          ∀v M0 N0. (M = LAM v M0) ∧ (N = LAM v N0) ⇒
                                    M0 -n->* N0` THEN1 METIS_TAC [] THEN
    HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [normorder_rwts] THEN
    METIS_TAC [relationTheory.RTC_RULES],

    HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
    SRW_TAC [][] THEN
    METIS_TAC [normorder_rules, relationTheory.RTC_RULES]
  ]);
val _ = export_rewrites ["normstar_LAM"]

val normstar_APPr = store_thm(
  "normstar_APPr",
  ``bnf M ∧ ¬is_abs M ⇒
        (M @@ N -n->* P ⇔ ∃N'. (P = M @@ N') ∧ N -n->* N')``,
  SIMP_TAC (srw_ss() ++ DNF_ss) [EQ_IMP_THM] THEN CONJ_TAC THENL [
    Q_TAC SUFF_TAC `∀M₀ P. M₀ -n->* P ⇒
                            ∀M N. (M₀ = M @@ N) ∧ bnf M ∧ ¬is_abs M ⇒
                                   ∃N'. (P = M @@ N') ∧ N -n->* N'`
          THEN1 METIS_TAC [] THEN
    HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [normorder_rwts] THEN
    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
      METIS_TAC [relationTheory.RTC_RULES],
      METIS_TAC [normorder_bnf]
    ],

    Q_TAC SUFF_TAC `∀N N'. N -n->* N' ⇒
                           ∀M. bnf M ∧ ¬is_abs M ⇒ M @@ N -n->* M @@ N'`
          THEN1 METIS_TAC [] THEN
    HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
    METIS_TAC [normorder_rules, relationTheory.RTC_RULES]
  ]);

(* ----------------------------------------------------------------------
    -n->* congruences
   ---------------------------------------------------------------------- *)

val nstar_LAM_I = store_thm(
  "nstar_LAM_I",
  ``M -n->* N ⇒ LAM v M -n->* LAM v N``,
  SRW_TAC [][]);

val normstar_APPr_I = store_thm(
  "normstar_APPr_I",
  ``bnf M ⇒ ¬is_abs M ⇒ N -n->* N' ⇒ M @@ N -n->* M @@ N'``,
  SRW_TAC [][normstar_APPr]);

(* ----------------------------------------------------------------------
    Calculating normal order reducts
   ---------------------------------------------------------------------- *)

val noreduct_def = Define`
  noreduct t = if bnf t then NONE else SOME (@t'. t -n-> t')
`;

val noreduct_thm = store_thm(
  "noreduct_thm",
  ``(noreduct (LAM v M) = OPTION_MAP (LAM v) (noreduct M)) ∧
    (noreduct (LAM v M @@ N) = SOME ([N/v]M)) ∧
    (¬is_abs M ⇒ (noreduct (M @@ N) =
                  if bnf M then OPTION_MAP ((@@) M) (noreduct N)
                  else OPTION_MAP (λM'. M' @@ N) (noreduct M))) ∧
    (noreduct (VAR s) = NONE)``,
  SRW_TAC [][noreduct_def] THENL [
    SRW_TAC [][normorder_rwts] THEN
    `∃N. M -n-> N` by METIS_TAC [normorder_bnf] THEN
    `∀N'. M -n-> N' = (N' = N)` by METIS_TAC [normorder_det] THEN
    SRW_TAC [][],

    SRW_TAC [][normorder_rwts],
    FULL_SIMP_TAC (srw_ss()) [],

    SRW_TAC [][normorder_rwts] THEN
    `(∀N. M -n-> N ⇔ F) ∧ ∃N'. N -n-> N'` by METIS_TAC [normorder_bnf] THEN
    SRW_TAC [][] THEN
    `∀N₂. N -n-> N₂ ⇔ (N₂ = N')` by METIS_TAC [normorder_det] THEN
    SRW_TAC [][],

    SRW_TAC [][normorder_rwts] THEN
    `∃M'. M -n-> M'` by METIS_TAC [normorder_bnf] THEN
    `∀M₂. M -n-> M₂ ⇔ (M₂ = M')` by METIS_TAC [normorder_det] THEN
    SRW_TAC [][]
  ]);

val noreduct_characterisation = store_thm(
  "noreduct_characterisation",
  ``M -n-> N ⇔ (noreduct M = SOME N)``,
  SRW_TAC [][noreduct_def] THENL [
    METIS_TAC [normorder_bnf],
    `∃N₁. M -n-> N₁` by METIS_TAC [normorder_bnf] THEN
    `∀N₂. M -n-> N₂ ⇔ (N₂ = N₁)` by METIS_TAC [normorder_det] THEN
    SRW_TAC [][] THEN METIS_TAC []
  ]);

val noreduct_bnf = store_thm(
  "noreduct_bnf",
  ``(noreduct M = NONE) = bnf M``,
  SRW_TAC [][noreduct_def]);


val noreduct_vsubst = store_thm(
  "noreduct_vsubst",
  ``∀t. noreduct ([VAR v/u] t) = OPTION_MAP (SUB (VAR v) u) (noreduct t)``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN 
  SRW_TAC [][noreduct_thm, SUB_VAR] THENL [
    Cases_on `is_abs t` THENL [
      `∃z t0. (t = LAM z t0) ∧ z ≠ u ∧ z ≠ v`
         by (Q.SPEC_THEN `t` FULL_STRUCT_CASES_TAC term_CASES THEN 
             FULL_SIMP_TAC (srw_ss()) [] THEN 
             SRW_TAC [boolSimps.DNF_ss][LAM_eq_thm, tpm_eqr] THEN 
             DISJ2_TAC THEN 
             Q_TAC (NEW_TAC "z") `{v';u;v} ∪ FV t0` THEN METIS_TAC []) THEN
      SRW_TAC [][noreduct_thm] THEN 
      SRW_TAC [][GSYM chap2Theory.substitution_lemma],

      SRW_TAC [][noreduct_thm] THENL [
        Cases_on `noreduct t'` THEN SRW_TAC [][],
        Cases_on `noreduct t` THEN SRW_TAC [][]
      ]
    ],

    Cases_on `noreduct t` THEN SRW_TAC [][]
  ]);

val noreduct_tpm = store_thm(
  "noreduct_tpm",
  ``∀t. noreduct (tpm π t) = OPTION_MAP (tpm π) (noreduct t)``,
  HO_MATCH_MP_TAC simple_induction THEN 
  SRW_TAC [][noreduct_thm] THENL [
    Cases_on `is_abs t` THENL [
      `∃z t0. t = LAM z t0`
         by (Q.SPEC_THEN `t` FULL_STRUCT_CASES_TAC term_CASES THEN 
             FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []) THEN 
      SRW_TAC [][noreduct_thm, tpm_subst],

      SRW_TAC [][noreduct_thm] THENL [
        Cases_on `noreduct t'` THEN SRW_TAC [][],
        Cases_on `noreduct t` THEN SRW_TAC [][]
      ]
    ],

    Cases_on `noreduct t` THEN SRW_TAC [][]
  ]);


val noredAPP' = store_thm(
  "noredAPP'",
  ``~is_abs M ==> (noreduct (M @@ N) =
                     case noreduct M of
                       NONE -> OPTION_MAP ((@@) M) (noreduct N)
                     || SOME M' -> SOME (M' @@ N))``,
  SRW_TAC [][noreduct_thm, GSYM noreduct_bnf] THEN
  Cases_on `noreduct M` THEN FULL_SIMP_TAC (srw_ss()) []);

val _ = overload_on ("upcons", ``λx y. pcons x () y``)



val pair_case_unit = prove(
  ``pair_case (f : unit -> 'a -> 'b) v = f () (SND v)``,
  Cases_on `v` THEN SRW_TAC [][oneTheory.one]);

val option_case_unit = prove(
  ``option_case n (f : unit # 'a -> 'b) (OPTION_MAP ($, ()) x) =
    option_case n (λx. f ((), x)) x``,
  Cases_on `x` THEN SRW_TAC [][]);

val nopath_def = new_specification(
  "nopath_def",
  ["nopath"],
  pathTheory.path_Axiom |> ISPEC ``λM. (M, OPTION_MAP ((,) ()) (noreduct M))``
                        |> SIMP_RULE (srw_ss()) [oneTheory.one,
                                                 pair_case_unit,
                                                 option_case_unit]);

val first_nopath = Store_thm(
  "first_nopath",
  ``first (nopath M) = M``,
  ONCE_REWRITE_TAC [nopath_def] THEN Cases_on `noreduct M` THEN
  SRW_TAC [][]);

val mem_nopath = Store_thm(
  "mem_nopath",
  ``mem M (nopath M)``,
  ONCE_REWRITE_TAC [nopath_def] THEN Cases_on `noreduct M` THEN
  SRW_TAC [][]);

val mem_nopath_expanded = Store_thm(
  "mem_nopath_expanded",
  ``mem M (option_case (stopped_at M) (λy. pcons M l (f y)) v)``,
  Cases_on `v` THEN SRW_TAC [][]);

val nopath_okpath = store_thm(
  "nopath_okpath",
  ``okpath (λM u N. M -n-> N) (nopath M)``,
  Q_TAC SUFF_TAC `∀p. (∃M. p = nopath M) ⇒ okpath (λM u N. M -n-> N) p`
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC okpath_co_ind THEN REPEAT GEN_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [nopath_def])) THEN
  CONV_TAC LEFT_IMP_EXISTS_CONV THEN GEN_TAC THEN
  Cases_on `noreduct M'` THEN SRW_TAC [][] THEN
  METIS_TAC [noreduct_characterisation]);

val option_case_CONG = store_thm(
  "option_case_CONG",
  ``(x = x') ⇒ (option_case n f x = option_case n f x')``,
  SRW_TAC [][]);

val normstar_nopath = store_thm(
  "normstar_nopath",
  ``M -n->* N ⇔ mem N (nopath M)``,
  EQ_TAC THENL [
    Q_TAC SUFF_TAC `∀M N. M -n->* N ⇒ mem N (nopath M)` THEN1 METIS_TAC []THEN
    HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [noreduct_characterisation,
                              nopath_def, Cong option_case_CONG],

    SIMP_TAC (srw_ss())[mem_def, GSYM LEFT_FORALL_IMP_THM] THEN
    Q.ID_SPEC_TAC `N` THEN Q.ID_SPEC_TAC `M` THEN
    SIMP_TAC (srw_ss()) [] THEN Induct_on`i` THEN SRW_TAC [][] THEN
    Q.SPEC_THEN `M` ASSUME_TAC nopath_def THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    Cases_on `noreduct M` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    METIS_TAC [relationTheory.RTC_RULES, noreduct_characterisation]
  ]);

val bnf_posn_is_length = store_thm(
  "bnf_posn_is_length",  
  ``∀i M. i ∈ PL (nopath M) ∧ bnf (el i (nopath M)) ⇒ 
          (length (nopath M) = SOME (i + 1))``,
  Induct THEN SRW_TAC [][] THENL [
    ONCE_REWRITE_TAC [nopath_def] THEN 
    `noreduct M = NONE` by METIS_TAC [noreduct_bnf] THEN 
    SRW_TAC [][length_thm],

    Q.SPEC_THEN `M` SUBST_ALL_TAC nopath_def THEN 
    Cases_on `noreduct M` THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
    `length (nopath x) = SOME (i + 1)` by METIS_TAC [] THEN 
    `finite (nopath x)` by METIS_TAC [finite_length] THEN 
    SRW_TAC [][length_thm, arithmeticTheory.ADD1]
  ]);

val has_bnf_finite_nopath = store_thm(
  "has_bnf_finite_nopath",
  ``has_bnf M ⇔ finite (nopath M)``,
  SRW_TAC [][has_bnf_thm, EQ_IMP_THM] THENL [
    `M -n->* N` by METIS_TAC [nstar_betastar_bnf] THEN 
    `mem N (nopath M)` by METIS_TAC [normstar_nopath] THEN 
    `∃i. i ∈ PL (nopath M) ∧ (el i (nopath M) = N)`
       by METIS_TAC [pathTheory.mem_def] THEN 
    `length (nopath M) = SOME (i + 1)`
       by METIS_TAC [bnf_posn_is_length] THEN 
    METIS_TAC [pathTheory.finite_length],

    POP_ASSUM MP_TAC THEN 
    Q_TAC SUFF_TAC 
       `∀p. finite p ⇒ ∀M. (p = nopath M) ⇒ ∃N. M -β->* N ∧ bnf N`
       THEN1 METIS_TAC [] THEN 
    HO_MATCH_MP_TAC pathTheory.finite_path_ind THEN SRW_TAC [][] THENL [
      Q.SPEC_THEN `M` SUBST_ALL_TAC nopath_def THEN 
      Cases_on `noreduct M` THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
      METIS_TAC [noreduct_bnf, relationTheory.RTC_RULES],

      Q.SPEC_THEN `M` SUBST_ALL_TAC nopath_def THEN 
      Cases_on `noreduct M` THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
      SRW_TAC [][] THEN 
      METIS_TAC [normorder_ccbeta, noreduct_characterisation,
                 relationTheory.RTC_RULES]
    ]
  ]);

val Omega_def = chap2Theory.Omega_def
val noreduct_omega = Store_thm(
  "noreduct_omega",
  ``noreduct Ω = SOME Ω``,
  SRW_TAC [][noreduct_thm, Omega_def]);

val Omega_loops = store_thm(
  "Omega_loops",
  ``Ω -n-> Ω``,
  SRW_TAC [][noreduct_characterisation] THEN 
  SRW_TAC [][noreduct_thm, Omega_def]);

val Omega_path_infinite = store_thm(
  "Omega_path_infinite",
  ``¬finite (nopath Ω)``,
  Q_TAC SUFF_TAC `∀p. finite p ⇒ p ≠ nopath Ω` THEN1 METIS_TAC [] THEN 
  HO_MATCH_MP_TAC pathTheory.finite_path_ind THEN SRW_TAC [][] THEN 
  ONCE_REWRITE_TAC [nopath_def] THEN SRW_TAC [][]);


val Omega_has_no_bnf = Store_thm(
  "Omega_has_no_bnf",
  ``¬has_bnf Ω``,
  SRW_TAC [][has_bnf_finite_nopath, Omega_path_infinite]);
      
val _ = export_theory()
