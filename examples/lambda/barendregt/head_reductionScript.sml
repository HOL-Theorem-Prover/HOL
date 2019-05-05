open HolKernel Parse boolLib bossLib

open chap3Theory pred_setTheory termTheory boolSimps
open nomsetTheory binderLib

val _ = new_theory "head_reduction"

val _ = ParseExtras.temp_loose_equality()

fun Store_thm(trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

val _ = set_trace "Unicode" 1

val (hreduce1_rules, hreduce1_ind, hreduce1_cases) = Hol_reln`
  (∀v M N. hreduce1 (LAM v M @@ N) ([N/v]M)) ∧
  (∀v M1 M2. hreduce1 M1 M2 ⇒ hreduce1 (LAM v M1) (LAM v M2)) ∧
  (∀M1 M2 N. hreduce1 M1 M2 ∧ ¬is_abs M1 ⇒ hreduce1 (M1 @@ N) (M2 @@ N))
`;

val _ = set_fixity "-h->" (Infix(NONASSOC, 450))
val _ = overload_on ("-h->", ``hreduce1``)

val _ = set_fixity "-h->*" (Infix(NONASSOC, 450))
val _ = overload_on ("-h->*", ``hreduce1^*``)

val hreduce_ccbeta = store_thm(
  "hreduce_ccbeta",
  ``∀M N. M -h-> N ⇒ M -β-> N``,
  HO_MATCH_MP_TAC hreduce1_ind THEN SRW_TAC [][cc_beta_thm] THEN
  METIS_TAC []);

val hreduce1_FV = store_thm(
  "hreduce1_FV",
  ``∀M N. M -h-> N ⇒ ∀v. v ∈ FV N ⇒ v ∈ FV M``,
  METIS_TAC [SUBSET_DEF, hreduce_ccbeta, cc_beta_FV_SUBSET]);


val _ = temp_add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT,2)),
                       fixity = Infix(NONASSOC, 950),
                       paren_style = OnlyIfNecessary,
                       pp_elements = [TOK "·", BreakSpace(0,0)],
                       term_name = "apply_perm"}
val _ = temp_overload_on ("apply_perm", ``λp M. tpm [p] M``)
val _ = temp_overload_on ("apply_perm", ``tpm``)
val _ = temp_overload_on ("#", ``λv t. v ∉ FV t``)
val _ = temp_set_fixity "#" (Infix(NONASSOC, 450))

val tpm_hreduce_I = store_thm(
  "tpm_hreduce_I",
  ``∀M N. M -h-> N ⇒ ∀π. π·M -h-> π·N``,
  HO_MATCH_MP_TAC hreduce1_ind THEN SRW_TAC [][tpm_subst, hreduce1_rules]);

val tpm_hreduce = store_thm(
  "tpm_hreduce",
  ``∀M N π. π·M -h-> π·N ⇔ M -h-> N``,
  METIS_TAC [pmact_inverse, tpm_hreduce_I]);

val hreduce1_rwts = store_thm(
  "hreduce1_rwts",
  ``(VAR s -h-> M ⇔ F) ∧
    (¬is_abs M ⇒ (M @@ N -h-> P ⇔ ∃M'. (P = M' @@ N) ∧ M -h-> M')) ∧
    (LAM v M -h-> N ⇔ ∃M'. (N = LAM v M') ∧ M -h-> M') ∧
    (LAM v M @@ N -h-> P ⇔ (P = [N/v]M))``,
  REPEAT STRIP_TAC THENL [
    SRW_TAC [][Once hreduce1_cases],
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [hreduce1_cases])) THEN
    SRW_TAC [][] THEN
    Q_TAC SUFF_TAC `∀v N. M ≠ LAM v N` THEN1 METIS_TAC [] THEN
    SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [],
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [hreduce1_cases])) THEN
    SRW_TAC [DNF_ss][LAM_eq_thm, tpm_eqr] THEN EQ_TAC THEN
    SRW_TAC [][] THEN1 SRW_TAC [][] THEN
    Q.EXISTS_TAC `(v,v')·M2` THEN
    SRW_TAC [][] THENL [
      `v # (v,v')·M` by SRW_TAC [][] THEN
      `v # M2` by METIS_TAC [hreduce1_FV] THEN
      SRW_TAC [][GSYM tpm_ALPHA],

      METIS_TAC [pmact_sing_inv, tpm_hreduce_I]
    ],

    SRW_TAC [DNF_ss][Once hreduce1_cases, LAM_eq_thm] THEN
    SRW_TAC [][EQ_IMP_THM, tpm_eqr] THEN
    METIS_TAC [lemma15a, pmact_flip_args, fresh_tpm_subst]
  ]);

val hnf_def = Define`hnf M = ∀N. ¬(M -h-> N)`;
val hnf_thm = Store_thm(
  "hnf_thm",
  ``(hnf (VAR s) ⇔ T) ∧
    (hnf (M @@ N) ⇔ hnf M ∧ ¬is_abs M) ∧
    (hnf (LAM v M) ⇔ hnf M)``,
  SRW_TAC [][hnf_def, hreduce1_rwts] THEN
  Cases_on `is_abs M` THEN SRW_TAC [][hreduce1_rwts] THEN
  Q.SPEC_THEN `M` FULL_STRUCT_CASES_TAC term_CASES THEN
  FULL_SIMP_TAC (srw_ss()) [hreduce1_rwts]);

val hnf_tpm = Store_thm(
  "hnf_tpm",
  ``∀M π. hnf (π·M) = hnf M``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]);

val hreduce1_unique = store_thm(
  "hreduce1_unique",
  ``∀M N1 N2. M -h-> N1 ∧ M -h-> N2 ⇒ (N1 = N2)``,
  Q_TAC SUFF_TAC `∀M N. M -h-> N ⇒ ∀P. M -h-> P ⇒ (N = P)`
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC hreduce1_ind THEN
  SIMP_TAC (srw_ss() ++ DNF_ss) [hreduce1_rwts]);

val strong_cc_ind = IndDefLib.derive_strong_induction (compat_closure_rules,
                                                       compat_closure_ind)

val hnf_ccbeta_preserved = store_thm(
  "hnf_ccbeta_preserved",
  ``∀M N. compat_closure beta M N ∧ hnf M ⇒ hnf N``,
  Q_TAC SUFF_TAC
        `∀M N. compat_closure beta M N ⇒ hnf M ⇒ hnf N`
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC strong_cc_ind THEN SRW_TAC [][] THENL [
    FULL_SIMP_TAC (srw_ss()) [beta_def] THEN
    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [],

    Q.SPEC_THEN `M` FULL_STRUCT_CASES_TAC term_CASES THEN
    FULL_SIMP_TAC (srw_ss()) [cc_beta_thm] THEN
    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []
  ]);

val (weak_head_rules, weak_head_ind, weak_head_cases) = Hol_reln`
  (∀v M N. weak_head (LAM v M @@ N) ([N/v]M)) ∧
  (∀M₁ M₂ N. weak_head M₁ M₂ ⇒ weak_head (M₁ @@ N) (M₂ @@ N))
`;
val _ = set_fixity "-w->" (Infix(NONASSOC, 450))
val _ = overload_on ("-w->", ``weak_head``)

val strong_weak_ind = IndDefLib.derive_strong_induction(weak_head_rules,
                                                        weak_head_ind)

val wh_is_abs = store_thm(
  "wh_is_abs",
  ``∀M N. M -w-> N ⇒ ¬is_abs M``,
  HO_MATCH_MP_TAC weak_head_ind THEN SRW_TAC [][]);

val wh_lam = Store_thm(
  "wh_lam",
  ``∀v M N. ¬(LAM v M -w-> N)``,
  ONCE_REWRITE_TAC [weak_head_cases] THEN SRW_TAC [][]);

val wh_head = store_thm(
  "wh_head",
  ``∀M N. M -w-> N ⇒ M -h-> N``,
  HO_MATCH_MP_TAC strong_weak_ind THEN METIS_TAC [wh_is_abs, hreduce1_rules]);



val _ = set_fixity "-w->*" (Infix(NONASSOC, 450))
val _ = overload_on ("-w->*", ``RTC (-w->)``)

val whead_FV = store_thm(
  "whead_FV",
  ``∀M N. M -w-> N ⇒ v ∈ FV N ⇒ v ∈ FV M``,
  HO_MATCH_MP_TAC weak_head_ind THEN SRW_TAC [][FV_SUB] THEN
  METIS_TAC []);
val whstar_FV = store_thm(
  "whstar_FV",
  ``∀M N. M -w->* N ⇒ v ∈ FV N ⇒ v ∈ FV M``,
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
  METIS_TAC [relationTheory.RTC_RULES, whead_FV]);


val _ = reveal "Y"
val whY1 = store_thm(
  "whY1",
  ``Y @@ f -w-> Yf f``,
  SRW_TAC [][chap2Theory.Y_def, chap2Theory.Yf_def, LET_THM,
             Once weak_head_cases] THEN
  NEW_ELIM_TAC THEN REPEAT STRIP_TAC THEN
  SRW_TAC [DNF_ss][LAM_eq_thm] THEN DISJ1_TAC THEN
  SRW_TAC [][chap2Theory.SUB_LAM_RWT, LET_THM] THEN NEW_ELIM_TAC THEN
  SRW_TAC [][LAM_eq_thm, tpm_fresh]);

val whY2 = store_thm(
  "whY2",
  ``Yf f -w-> f @@ Yf f``,
  SRW_TAC [][chap2Theory.Yf_def, LET_THM, Once weak_head_cases] THEN
  NEW_ELIM_TAC THEN SRW_TAC [DNF_ss][LAM_eq_thm, lemma14b]);

val wh_unique = store_thm(
  "wh_unique",
  ``M -w-> N₁ ∧ M -w-> N₂ ⇒ (N₁ = N₂)``,
  METIS_TAC [hreduce1_unique, wh_head]);

val whnf_def = Define`
  whnf M = ∀N. ¬(M -w-> N)
`;

val hnf_whnf = store_thm(
  "hnf_whnf",
  ``hnf M ⇒ whnf M``,
  METIS_TAC [hnf_def, whnf_def, wh_head]);

val bnf_hnf = store_thm(
  "bnf_hnf",
  ``bnf M ⇒ hnf M``,
  METIS_TAC [hnf_def, beta_normal_form_bnf, corollary3_2_1, hreduce_ccbeta]);

val bnf_whnf = store_thm(
  "bnf_whnf",
  ``bnf M ⇒ whnf M``,
  METIS_TAC [hnf_whnf, bnf_hnf]);

val whnf_thm = Store_thm(
  "whnf_thm",
  ``whnf (VAR s) ∧
    (whnf (M @@ N) ⇔ ¬is_abs M ∧ whnf M) ∧
    whnf (LAM v M)``,
  REPEAT CONJ_TAC THEN SRW_TAC [][whnf_def, Once weak_head_cases] THEN
  EQ_TAC THEN SRW_TAC [][FORALL_AND_THM] THENL [
    Q.SPEC_THEN `M` FULL_STRUCT_CASES_TAC term_CASES THEN SRW_TAC [][] THEN
    METIS_TAC [],
    Q.SPEC_THEN `M` FULL_STRUCT_CASES_TAC term_CASES THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);

val wh_weaken_cong = store_thm(
  "wh_weaken_cong",
  ``whnf N ⇒ M₁ -w->* M₂ ⇒ (M₁ -w->* N = M₂ -w->* N)``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, IMP_CONJ_THM] THEN CONJ_TAC THENL [
    Q_TAC SUFF_TAC `∀M N. M -w->* N ⇒ ∀N'. M -w->* N' ∧ whnf N' ⇒ N -w->* N'`
          THEN1 METIS_TAC [] THEN
    HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN SRW_TAC [][] THEN
    METIS_TAC [relationTheory.RTC_CASES1, whnf_def, wh_unique],

    METIS_TAC [relationTheory.RTC_CASES_RTC_TWICE]
  ]);

val wh_app_congL = store_thm(
  "wh_app_congL",
  ``M -w->* M' ==> M @@ N -w->* M' @@ N``,
  STRIP_TAC THEN Q.ID_SPEC_TAC `N` THEN POP_ASSUM MP_TAC THEN
  MAP_EVERY Q.ID_SPEC_TAC [`M'`, `M`] THEN
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN SRW_TAC [][] THEN
  METIS_TAC [relationTheory.RTC_RULES, weak_head_rules]);

val tpm_whead_I = store_thm(
  "tpm_whead_I",
  ``∀M N. M -w-> N ⇒ π·M -w-> π·N``,
  HO_MATCH_MP_TAC weak_head_ind THEN SRW_TAC [][weak_head_rules, tpm_subst]);

val whead_gen_bvc_ind = store_thm(
  "whead_gen_bvc_ind",
  ``∀P f. (∀x. FINITE (f x)) ∧
          (∀v M N x. v ∉ f x ⇒ P (LAM v M @@ N) ([N/v]M) x) ∧
          (∀M₁ M₂ N x. (∀z. P M₁ M₂ z) ⇒ P (M₁ @@ N) (M₂ @@ N) x)
        ⇒
          ∀M N. M -w-> N ⇒ ∀x. P M N x``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `∀M N. M -w-> N ⇒ ∀π x. P (π·M) (π·N) x`
        THEN1 METIS_TAC [pmact_nil] THEN
  HO_MATCH_MP_TAC weak_head_ind THEN SRW_TAC [][tpm_subst] THEN
  Q_TAC (NEW_TAC "z") `{lswapstr π v} ∪ FV (π·M) ∪ FV (π·N) ∪ f x` THEN
  `LAM (lswapstr π v) (π·M) = LAM z ([VAR z/lswapstr π v](π·M))`
     by SRW_TAC [][SIMPLE_ALPHA] THEN
  `[π·N/lswapstr π v](π·M) = [π·N/z] ([VAR z/lswapstr π v](π·M))`
     by SRW_TAC [][lemma15a] THEN
  SRW_TAC [][]);

val whead_bvcX_ind = save_thm(
  "whead_bvcX_ind",
  whead_gen_bvc_ind |> Q.SPECL [`λM N x. P' M N`, `λx. X`]
                    |> SIMP_RULE (srw_ss()) []
                    |> Q.INST [`P'` |-> `P`]
                    |> Q.GEN `X` |> Q.GEN `P`);

val wh_substitutive = store_thm(
  "wh_substitutive",
  ``∀M N. M -w-> N ⇒ [P/v]M -w-> [P/v]N``,
  HO_MATCH_MP_TAC whead_bvcX_ind THEN Q.EXISTS_TAC `FV P ∪ {v}` THEN
  SRW_TAC [][weak_head_rules] THEN
  METIS_TAC [chap2Theory.substitution_lemma, weak_head_rules]);

val whstar_substitutive = store_thm(
  "whstar_substitutive",
  ``∀M N. M -w->* N ⇒ [P/v]M -w->* [P/v]N``,
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN SRW_TAC [][] THEN
  METIS_TAC [relationTheory.RTC_RULES, wh_substitutive]);

val whstar_betastar = store_thm(
  "whstar_betastar",
  ``∀M N. M -w->* N ⇒ M -β->* N``,
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN SRW_TAC [][] THEN
  METIS_TAC [relationTheory.RTC_RULES, wh_head, hreduce_ccbeta]);

val whstar_lameq = store_thm(
  "whstar_lameq",
  ``M -w->* N ⇒ M == N``,
  METIS_TAC [betastar_lameq, whstar_betastar]);

val whstar_abs = Store_thm(
  "whstar_abs",
  ``LAM v M -w->* N ⇔ (N = LAM v M)``,
  SRW_TAC [][EQ_IMP_THM] THEN
  FULL_SIMP_TAC (srw_ss()) [Once relationTheory.RTC_CASES1,
                            Once weak_head_cases]);

(* ----------------------------------------------------------------------
    has_whnf
   ---------------------------------------------------------------------- *)

(* definition of has_hnf in standardisationScript has == rather than -h->*
   as the relation on the RHS.  This means that has_bnf automatically implies
   has_hnf, but makes the corollary to the standardisation theorem interesting
   to prove... *)
val has_whnf_def = Define`
  has_whnf M = ∃N. M -w->* N ∧ whnf N
`;

open lcsymtacs
val has_whnf_APP_E = store_thm(
  "has_whnf_APP_E",
  ``has_whnf (M @@ N) ⇒ has_whnf M``,
  simp_tac (srw_ss())[has_whnf_def] >>
  Q_TAC SUFF_TAC
     `∀M N. M -w->* N ⇒ ∀M0 M1. (M = M0 @@ M1) ∧ whnf N ⇒
                                 ∃N'. M0 -w->* N' ∧ whnf N'`
     >- metis_tac [] >>
  ho_match_mp_tac relationTheory.RTC_INDUCT >> conj_tac
    >- (simp_tac (srw_ss()) [] >> metis_tac [relationTheory.RTC_RULES]) >>
  srw_tac [][] >> Cases_on `is_abs M0`
    >- (Q.SPEC_THEN `M0` FULL_STRUCT_CASES_TAC term_CASES >>
        full_simp_tac (srw_ss()) [] >>
        metis_tac [relationTheory.RTC_RULES, whnf_thm]) >>
  full_simp_tac (srw_ss()) [Once weak_head_cases] >>
  metis_tac [relationTheory.RTC_RULES])

val hreduce_weak_or_strong = store_thm(
  "hreduce_weak_or_strong",
  ``∀M N. M -h-> N ⇒ whnf M ∨ M -w-> N``,
  ho_match_mp_tac simple_induction >> simp_tac (srw_ss()) [] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp_tac (srw_ss()) [Once hreduce1_cases] >>
  simp_tac (srw_ss() ++ DNF_ss) [] >> conj_tac
    >- metis_tac [weak_head_rules] >>
  srw_tac [][] >> metis_tac [weak_head_rules]);

val head_reductions_have_weak_prefixes = store_thm(
  "head_reductions_have_weak_prefixes",
  ``∀M N. M -h->* N ⇒ hnf N ⇒
          ∃N0. M -w->* N0 ∧ whnf N0 ∧ N0 -h->* N``,
   ho_match_mp_tac relationTheory.RTC_STRONG_INDUCT >> conj_tac
     >- metis_tac [hnf_whnf, relationTheory.RTC_RULES] >>
   metis_tac [relationTheory.RTC_RULES, hreduce_weak_or_strong]);

val _ = export_theory()
