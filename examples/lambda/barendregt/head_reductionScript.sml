open HolKernel Parse boolLib bossLib BasicProvers;

open boolSimps relationTheory pred_setTheory listTheory finite_mapTheory
     arithmeticTheory llistTheory pathTheory optionTheory rich_listTheory
     hurdUtils;

open termTheory appFOLDLTheory chap2Theory chap3Theory nomsetTheory binderLib
     horeductionTheory term_posnsTheory finite_developmentsTheory;

val _ = new_theory "head_reduction"

val _ = ParseExtras.temp_loose_equality()

fun Store_thm(trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

Inductive hreduce1 :
[~BETA:]
  (∀v M N. hreduce1 (LAM v M @@ N) ([N/v]M))
[~LAM:]
  (∀v M1 M2. hreduce1 M1 M2 ⇒ hreduce1 (LAM v M1) (LAM v M2))
[~APP:]
  (∀M1 M2 N. hreduce1 M1 M2 ∧ ¬is_abs M1 ⇒ hreduce1 (M1 @@ N) (M2 @@ N))
End

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

Theorem hreduces_FV :
    ∀M N. M -h->* N ⇒ v ∈ FV N ⇒ v ∈ FV M
Proof
    HO_MATCH_MP_TAC relationTheory.RTC_INDUCT
 >> METIS_TAC [relationTheory.RTC_RULES, hreduce1_FV]
QED

val _ = temp_add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT,2)),
                       fixity = Infix(NONASSOC, 950),
                       paren_style = OnlyIfNecessary,
                       pp_elements = [TOK "·", BreakSpace(0,0)],
                       term_name = "apply_perm"}
val _ = temp_overload_on ("apply_perm", ``λp M. tpm [p] M``)
val _ = temp_overload_on ("apply_perm", ``tpm``)

val tpm_hreduce_I = store_thm(
  "tpm_hreduce_I",
  ``∀M N. M -h-> N ⇒ ∀π. π·M -h-> π·N``,
  HO_MATCH_MP_TAC hreduce1_ind THEN SRW_TAC [][tpm_subst, hreduce1_rules]);

Theorem tpm_hreduce[simp] :
    ∀M N π. π·M -h-> π·N ⇔ M -h-> N
Proof
  METIS_TAC [pmact_inverse, tpm_hreduce_I]
QED

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

val hreduce1_unique = store_thm(
  "hreduce1_unique",
  ``∀M N1 N2. M -h-> N1 ∧ M -h-> N2 ⇒ (N1 = N2)``,
  Q_TAC SUFF_TAC `∀M N. M -h-> N ⇒ ∀P. M -h-> P ⇒ (N = P)`
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC hreduce1_ind THEN
  SIMP_TAC (srw_ss() ++ DNF_ss) [hreduce1_rwts]);

Theorem hreduce1_rules_appstar :
    !Ns. M1 -h-> M2 /\ ~is_abs M1 ==> M1 @* Ns -h-> M2 @* Ns
Proof
    Induct_on ‘Ns’ using SNOC_INDUCT
 >> rw [appstar_SNOC]
 >> fs [hreduce1_rules]
QED

Theorem hreduce1_gen_bvc_ind :
  !P f. (!x. FINITE (f x)) /\
        (!v M N x. v NOTIN f x ==> P (LAM v M @@ N) ([N/v] M) x) /\
        (!v M1 M2 x. M1 -h-> M2 /\ v NOTIN f x /\ (!z. P M1 M2 z) ==>
                     P (LAM v M1) (LAM v M2) x) /\
        (!M1 M2 N x. M1 -h-> M2 /\ (!z. P M1 M2 z) /\ ~is_abs M1 ==>
                     P (M1 @@ N) (M2 @@ N) x)
    ==> !M N. M -h-> N ==> !x. P M N x
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Suff ‘!M N. M -h-> N ==> !p x. P (tpm p M) (tpm p N) x’
 >- METIS_TAC [pmact_nil]
 >> HO_MATCH_MP_TAC hreduce1_strongind
 >> reverse (rw []) (* easy goal first *)
 >- (Q.ABBREV_TAC ‘u = lswapstr p v’ \\
     Q_TAC (NEW_TAC "z") ‘(f x) UNION {v} UNION FV (tpm p M) UNION FV (tpm p N)’ \\
    ‘(LAM u (tpm p M) = LAM z (tpm ([(z,u)] ++ p) M)) /\
     (LAM u (tpm p N) = LAM z (tpm ([(z,u)] ++ p) N))’
       by rw [tpm_ALPHA, pmact_decompose] >> rw [])
 (* stage work *)
 >> Q.ABBREV_TAC ‘u = lswapstr p v’
 >> Q_TAC (NEW_TAC "z") ‘(f x) UNION {v} UNION FV (tpm p M) UNION FV (tpm p N)’
 >> ‘LAM u (tpm p M) = LAM z (tpm ([(z,u)] ++ p) M)’ by rw [tpm_ALPHA, pmact_decompose]
 >> POP_ORW
 >> Q.ABBREV_TAC ‘M1 = apply_perm ([(z,u)] ++ p) M’
 >> Suff ‘tpm p ([N/v] M) = [tpm p N/z] M1’ >- rw []
 >> rw [tpm_subst, Abbr ‘M1’]
 >> simp [Once tpm_CONS, fresh_tpm_subst]
 >> simp [lemma15a]
QED

(* |- !P X.
        FINITE X /\ (!v M N. v NOTIN X ==> P (LAM v M @@ N) ([N/v] M)) /\
        (!v M1 M2. M1 -h-> M2 /\ v NOTIN X /\ P M1 M2 ==> P (LAM v M1) (LAM v M2)) /\
        (!M1 M2 N. M1 -h-> M2 /\ P M1 M2 /\ ~is_abs M1 ==> P (M1 @@ N) (M2 @@ N)) ==>
        !M N. M -h-> N ==> P M N
 *)
Theorem hreduce1_bvcX_ind =
  hreduce1_gen_bvc_ind |> Q.SPECL [`λM N x. P' M N`, `λx. X`]
                       |> SIMP_RULE (srw_ss()) []
                       |> Q.INST [`P'` |-> `P`]
                       |> Q.GEN `X` |> Q.GEN `P`

(* Lemma 8.3.12 [1, p.174] *)
Theorem hreduce1_substitutive :
    !M N. M -h-> N ==> [P/v] M -h-> [P/v] N
Proof
    HO_MATCH_MP_TAC hreduce1_bvcX_ind
 >> Q.EXISTS_TAC ‘FV P UNION {v}’ >> rw [hreduce1_rules]
 >- METIS_TAC [substitution_lemma, hreduce1_rules]
 >> ‘is_comb M \/ is_var M’ by METIS_TAC [term_cases]
 >- (MATCH_MP_TAC hreduce1_APP >> art [] \\
     gs [is_comb_APP_EXISTS, is_abs_thm])
 >> gs [is_var_cases, hreduce1_rwts]
QED

(* This form is useful for ‘|- substitutive R ==> ...’ theorems (chap3Theory) *)
Theorem substitutive_hreduce1 :
    substitutive (-h->)
Proof
    rw [substitutive_def, hreduce1_substitutive]
QED

Theorem hreduce_substitutive :
    !M N. M -h->* N ==> [P/v] M -h->* [P/v] N
Proof
    HO_MATCH_MP_TAC RTC_INDUCT >> rw []
 >> METIS_TAC [RTC_RULES, hreduce1_substitutive]
QED

Theorem substitutive_hreduce :
    substitutive (-h->*)
Proof
    rw [substitutive_def, hreduce_substitutive]
QED

(* ----------------------------------------------------------------------
    Head normal form (hnf)
   ---------------------------------------------------------------------- *)

val hnf_def = Define`hnf M = ∀N. ¬(M -h-> N)`;

Theorem hnf_thm[simp] :
    (hnf (VAR s) ⇔ T) ∧
    (hnf (M @@ N) ⇔ hnf M ∧ ¬is_abs M) ∧
    (hnf (LAM v M) ⇔ hnf M)
Proof
  SRW_TAC [][hnf_def, hreduce1_rwts] THEN
  Cases_on `is_abs M` THEN SRW_TAC [][hreduce1_rwts] THEN
  Q.SPEC_THEN `M` FULL_STRUCT_CASES_TAC term_CASES THEN
  FULL_SIMP_TAC (srw_ss()) [hreduce1_rwts]
QED

Theorem hnf_tpm[simp] :
    ∀M π. hnf (π·M) = hnf M
Proof
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]
QED

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

Theorem hnf_I :
    hnf I
Proof
    RW_TAC std_ss [hnf_thm, I_def]
QED

Theorem hnf_LAMl[simp] :
    hnf (LAMl vs M) <=> hnf M
Proof
    Induct_on ‘vs’ >> rw []
QED

Theorem hnf_appstar :
    !M Ns. hnf (M @* Ns) <=> hnf M /\ (is_abs M ⇒ (Ns = []))
Proof
  Induct_on ‘Ns’ using SNOC_INDUCT >> simp[appstar_SNOC] >>
  dsimp[SF CONJ_ss] >> metis_tac[]
QED

(* NOTE: ‘ALL_DISTINCT vs’ has been added to RHS. *)
Theorem hnf_cases :
    !M : term. hnf M <=> ?vs args y. ALL_DISTINCT vs /\ (M = LAMl vs (VAR y @* args))
Proof
  simp[FORALL_AND_THM, EQ_IMP_THM] >> conj_tac
  >- (gen_tac >> MP_TAC (Q.SPEC ‘M’ strange_cases)
      >> RW_TAC std_ss []
      >- (FULL_SIMP_TAC std_ss [size_1_cases] \\
          qexistsl_tac [‘vs’, ‘[]’, ‘y’] >> rw [])
      >> FULL_SIMP_TAC std_ss [hnf_LAMl]
      >> ‘hnf t /\ ~is_abs t’ by PROVE_TAC [hnf_appstar]
      >> ‘is_var t’ by METIS_TAC [term_cases]
      >> FULL_SIMP_TAC std_ss [is_var_cases]
      >> qexistsl_tac [‘vs’, ‘args’, ‘y’] >> art []) >>
  simp[PULL_EXISTS, hnf_appstar]
QED

(* A more general version of ‘hnf_cases’ directly based on term_laml_cases *)
Theorem hnf_cases_genX :
    !X. FINITE X ==>
        !M. hnf M <=> ?vs args y. ALL_DISTINCT vs /\ (M = LAMl vs (VAR y @* args)) /\
                                  DISJOINT (set vs) X
Proof
    reverse (rw [FORALL_AND_THM, EQ_IMP_THM])
 >- rw [hnf_appstar]
 >> MP_TAC (Q.SPEC ‘M’ (MATCH_MP term_laml_cases (ASSUME “FINITE (X :string -> bool)”)))
 >> RW_TAC std_ss []
 >| [ (* goal 1 (of 3) *)
      qexistsl_tac [‘[]’, ‘[]’, ‘s’] >> rw [],
      (* goal 2 (of 3) *)
      Know ‘is_comb (M1 @@ M2)’ >- rw [] \\
      ONCE_REWRITE_TAC [is_comb_appstar_exists] >> rw [] \\
      Q.PAT_X_ASSUM ‘M1 @@ M2 = t @* args’ (FULL_SIMP_TAC std_ss o wrap) \\
      fs [hnf_appstar] \\
     ‘is_var t’ by METIS_TAC [term_cases] >> fs [is_var_cases],
      (* goal 3 (of 3) *)
      fs [hnf_LAMl] >> rename1 ‘hnf M’ \\
     ‘is_var M \/ is_comb M’ by METIS_TAC [term_cases]
      >- (fs [is_var_cases] \\
          qexistsl_tac [‘v::vs’, ‘[]’, ‘y’] >> rw []) \\
      FULL_SIMP_TAC std_ss [Once is_comb_appstar_exists] \\
      gs [hnf_appstar] \\
     ‘is_var t’ by METIS_TAC [term_cases] >> fs [is_var_cases] \\
      qexistsl_tac [‘v::vs’, ‘args’, ‘y’] >> rw [] ]
QED

(* ----------------------------------------------------------------------
    Weak head reductions (weak_head or -w->)
   ---------------------------------------------------------------------- *)

Inductive weak_head :
  (∀v M N :term. weak_head (LAM v M @@ N) ([N/v]M)) ∧
  (∀M₁ M₂ N. weak_head M₁ M₂ ⇒ weak_head (M₁ @@ N) (M₂ @@ N))
End

val _ = set_fixity "-w->" (Infix(NONASSOC, 450))
val _ = overload_on ("-w->", ``weak_head``)

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
    HO_MATCH_MP_TAC weak_head_strongind
 >> METIS_TAC [wh_is_abs, hreduce1_rules]);

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

(* ----------------------------------------------------------------------
    Head redex
   ---------------------------------------------------------------------- *)

val _ = add_infix ("is_head_redex", 760, NONASSOC)

Inductive is_head_redex :
    (!v (t:term) u. [] is_head_redex (LAM v t @@ u)) /\
    (!v t p. p is_head_redex t ==> (In::p) is_head_redex (LAM v t)) /\
    (!t u v p. p is_head_redex (t @@ u) ==>
               (Lt::p) is_head_redex (t @@ u) @@ v)
End

val ihr_bvc_ind = store_thm(
  "ihr_bvc_ind",
  ``!P X. FINITE X /\
          (!v M N. ~(v IN X) /\ ~(v IN FV N) ==> P [] (LAM v M @@ N)) /\
          (!v M p. ~(v IN X) /\ P p M ==> P (In::p) (LAM v M)) /\
          (!M N L p. P p (M @@ N) ==> P (Lt::p) ((M @@ N) @@ L)) ==>
          !p M. p is_head_redex M ==> P p M``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!p M. p is_head_redex M ==> !pi. P p (tpm pi M)`
        THEN1 METIS_TAC [pmact_nil] THEN
  HO_MATCH_MP_TAC is_head_redex_ind THEN
  SRW_TAC [][is_head_redex_rules] THENL [
    Q.MATCH_ABBREV_TAC `P [] (LAM vv MM @@ NN)` THEN
    markerLib.RM_ALL_ABBREVS_TAC THEN
    Q_TAC (NEW_TAC "z") `FV MM UNION FV NN UNION X` THEN
    `LAM vv MM = LAM z (tpm [(z,vv)] MM)` by SRW_TAC [][tpm_ALPHA] THEN
    SRW_TAC [][],
    Q.MATCH_ABBREV_TAC `P (In::p) (LAM vv MM)` THEN
    Q_TAC (NEW_TAC "z") `FV MM UNION X` THEN
    `LAM vv MM = LAM z (tpm [(z,vv)] MM)` by SRW_TAC [][tpm_ALPHA] THEN
    SRW_TAC [][GSYM pmact_decompose, Abbr`MM`]
  ]);

val is_head_redex_subst_invariant = store_thm(
  "is_head_redex_subst_invariant",
  ``!p t u v. p is_head_redex t ==> p is_head_redex [u/v] t``,
  REPEAT GEN_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`t`, `p`] THEN
  HO_MATCH_MP_TAC ihr_bvc_ind THEN Q.EXISTS_TAC `v INSERT FV u` THEN
  SRW_TAC [][SUB_THM, SUB_VAR, is_head_redex_rules]);

Theorem is_head_redex_tpm_invariant[simp] :
    p is_head_redex (tpm pi t) = p is_head_redex t
Proof
  Q_TAC SUFF_TAC `!p t. p is_head_redex t ==> !pi. p is_head_redex (tpm pi t)`
        THEN1 METIS_TAC [pmact_inverse] THEN
  HO_MATCH_MP_TAC is_head_redex_ind THEN SRW_TAC [][is_head_redex_rules]
QED

val is_head_redex_unique = store_thm(
  "is_head_redex_unique",
  ``!t p1 p2. p1 is_head_redex t /\ p2 is_head_redex t ==> (p1 = p2)``,
  Q_TAC SUFF_TAC
        `!p1 t. p1 is_head_redex t ==> !p2. p2 is_head_redex t ==> (p1 = p2)`
        THEN1 PROVE_TAC [] THEN
  HO_MATCH_MP_TAC is_head_redex_ind THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [is_head_redex_cases] THEN
  SRW_TAC [][LAM_eq_thm]);

val is_head_redex_thm = store_thm(
  "is_head_redex_thm",
  ``(p is_head_redex (LAM v t) = ?p0. (p = In::p0) /\ p0 is_head_redex t) /\
    (p is_head_redex (t @@ u) = (p = []) /\ is_abs t \/
                                ?p0. (p = Lt::p0) /\ is_comb t /\
                                          p0 is_head_redex t) /\
    (p is_head_redex (VAR v) = F)``,
  REPEAT CONJ_TAC THEN
  SRW_TAC [][Once is_head_redex_cases, SimpLHS, LAM_eq_thm] THEN
  SRW_TAC [][EQ_IMP_THM] THENL [
    PROVE_TAC [],
    PROVE_TAC [is_abs_thm, term_CASES],
    METIS_TAC [is_comb_thm, term_CASES]
  ]);

val head_redex_leftmost = store_thm(
  "head_redex_leftmost",
  ``!p t. p is_head_redex t ==>
          !p'. p' IN redex_posns t ==> (p = p') \/ p < p'``,
  HO_MATCH_MP_TAC is_head_redex_ind THEN
  SRW_TAC [][redex_posns_thm, DISJ_IMP_THM]);

val hnf_no_head_redex = store_thm(
  "hnf_no_head_redex",
  ``!t. hnf t = !p. ~(p is_head_redex t)``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][hnf_thm, is_head_redex_thm] THEN
  Q.SPEC_THEN `t` STRUCT_CASES_TAC term_CASES THEN
  SRW_TAC [][is_head_redex_thm]);

val head_redex_is_redex = store_thm(
  "head_redex_is_redex",
  ``!p t. p is_head_redex t ==> p IN redex_posns t``,
  HO_MATCH_MP_TAC is_head_redex_ind THEN
  SRW_TAC [][redex_posns_thm]);

val is_head_redex_vsubst_invariant = store_thm(
  "is_head_redex_vsubst_invariant",
  ``!t v x p. p is_head_redex ([VAR v/x] t) = p is_head_redex t``,
  REPEAT GEN_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`p`, `t`] THEN
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{x;v}` THEN
  SRW_TAC [][is_head_redex_thm, SUB_THM, SUB_VAR]);

val head_redex_preserved = store_thm(
  "head_redex_preserved",
  ``!M p N.
      labelled_redn beta M p N ==>
      !h. h is_head_redex M /\ ~(h = p) ==> h is_head_redex N``,
  HO_MATCH_MP_TAC strong_labelled_redn_ind THEN
  SRW_TAC [][is_head_redex_thm, beta_def] THENL [
    FULL_SIMP_TAC (srw_ss()) [is_head_redex_thm],
    `?v t. M = LAM v t` by PROVE_TAC [is_abs_thm, term_CASES] THEN
    FULL_SIMP_TAC (srw_ss()) [labelled_redn_lam],
    `?f x. M = f @@ x` by PROVE_TAC [is_comb_APP_EXISTS] THEN
    SRW_TAC [][] THEN
    Q.PAT_X_ASSUM `labelled_redn beta _ _ _` MP_TAC THEN
    ONCE_REWRITE_TAC [labelled_redn_cases] THEN
    FULL_SIMP_TAC (srw_ss()) [is_head_redex_thm, beta_def] THEN
    PROVE_TAC [is_comb_thm]
  ]);

(* moved here from standardisationScript.sml *)
Definition is_head_reduction_def :
  is_head_reduction s = okpath (labelled_redn beta) s /\
                        !i. i + 1 IN PL s ==>
                            nth_label i s is_head_redex el i s
End

Theorem is_head_reduction_thm[simp] :
    (is_head_reduction (stopped_at x) = T) /\
    (is_head_reduction (pcons x r p) =
       labelled_redn beta x r (first p) /\ r is_head_redex x /\
       is_head_reduction p)
Proof
  SRW_TAC [][is_head_reduction_def, GSYM ADD1,
             EQ_IMP_THM]
  THENL [
    POP_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN SRW_TAC [][],
    RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [],
    Cases_on `i` THEN SRW_TAC [][]
  ]
QED

val _ = add_infix ("head_reduces", 760, NONASSOC)
Definition head_reduces_def :
  M head_reduces N = ?s. finite s /\ (first s = M) /\ (last s = N) /\
                         is_head_reduction s
End

val head_reduce1_def = store_thm(
  "head_reduce1_def",
  ``M -h-> N = (?r. r is_head_redex M /\ labelled_redn beta M r N)``,
  EQ_TAC THENL [
    Q_TAC SUFF_TAC `!M N. M -h-> N ==>
                          ?r. r is_head_redex M /\ labelled_redn beta M r N`
          THEN1 METIS_TAC [] THEN
    HO_MATCH_MP_TAC hreduce1_ind THEN SRW_TAC [][] THENL [
      METIS_TAC [beta_def, is_head_redex_rules, labelled_redn_rules],
      METIS_TAC [is_head_redex_rules, labelled_redn_rules],
      Q.SPEC_THEN `M` FULL_STRUCT_CASES_TAC term_CASES THENL [
        FULL_SIMP_TAC (srw_ss()) [Once labelled_redn_cases, beta_def],
        METIS_TAC [is_head_redex_rules, labelled_redn_rules],
        FULL_SIMP_TAC (srw_ss()) []
      ]
    ],
    Q_TAC SUFF_TAC `!M r N. labelled_redn beta M r N ==>
                            r is_head_redex M ==> M -h-> N`
          THEN1 METIS_TAC [] THEN
    HO_MATCH_MP_TAC labelled_redn_ind THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [beta_def, is_head_redex_thm,
                                   Once is_comb_APP_EXISTS, hreduce1_rwts]
  ]);

val head_reduces_RTC_hreduce1 = store_thm(
  "head_reduces_RTC_hreduce1",
  ``(head_reduces) = RTC (-h->)``,
  SIMP_TAC (srw_ss()) [head_reduces_def, FUN_EQ_THM, GSYM LEFT_FORALL_IMP_THM,
                       FORALL_AND_THM, EQ_IMP_THM] THEN
  CONJ_TAC THENL [
    Q_TAC SUFF_TAC `!s. finite s ==>
                        is_head_reduction s ==>
                        RTC (-h->) (first s) (last s)` THEN1
          PROVE_TAC [] THEN
    HO_MATCH_MP_TAC pathTheory.finite_path_ind THEN
    SIMP_TAC (srw_ss()) [relationTheory.RTC_RULES] THEN
    MAP_EVERY Q.X_GEN_TAC [`x`,`r`,`p`] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (CONJUNCT2 (SPEC_ALL relationTheory.RTC_RULES)) THEN
    Q.EXISTS_TAC `first p` THEN SRW_TAC [][head_reduce1_def] THEN
    PROVE_TAC [],
    HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
    SRW_TAC [][head_reduce1_def] THENL [
      Q.EXISTS_TAC `stopped_at x` THEN SRW_TAC [][],
      Q.EXISTS_TAC `pcons x r s` THEN SRW_TAC [][]
    ]
  ]);

val head_reduces_reduction_beta = store_thm(
  "head_reduces_reduction_beta",
  ``!M N. M head_reduces N ==> reduction beta M N``,
  SIMP_TAC (srw_ss()) [head_reduces_RTC_hreduce1] THEN
  MATCH_MP_TAC relationTheory.RTC_MONOTONE THEN
  METIS_TAC [head_reduce1_def, labelled_redn_cc]);

Theorem hreduces_lameq :
    M -h->* N ==> M == N
Proof
    rw [SYM head_reduces_RTC_hreduce1]
 >> MATCH_MP_TAC betastar_lameq
 >> MATCH_MP_TAC head_reduces_reduction_beta >> art []
QED

val head_reduces_TRANS = store_thm(
  "head_reduces_TRANS",
  ``!M N P. M head_reduces N /\ N head_reduces P ==> M head_reduces P``,
  METIS_TAC [relationTheory.RTC_RTC, head_reduces_RTC_hreduce1]);

(* moved here from standardisationScript.sml *)
val has_hnf_def = Define`
  has_hnf M = ?N. M == N /\ hnf N
`;

Theorem hnf_has_hnf :
    !M. hnf M ==> has_hnf M
Proof
    rw [has_hnf_def]
 >> Q.EXISTS_TAC ‘M’ >> rw []
QED

val has_bnf_hnf = store_thm(
  "has_bnf_hnf",
  ``has_bnf M ⇒ has_hnf M``,
  SRW_TAC [][has_hnf_def, chap2Theory.has_bnf_def] THEN
  METIS_TAC [bnf_hnf]);

val head_reduct_def = Define`
  head_reduct M = if ?r. r is_head_redex M then
                    SOME (@N. M -h-> N)
                  else NONE
`;

val head_reduct_unique = store_thm(
  "head_reduct_unique",
  ``!M N. M -h-> N ==> (head_reduct M = SOME N)``,
  SRW_TAC [][head_reduce1_def, head_reduct_def] THEN1 METIS_TAC [] THEN
  SELECT_ELIM_TAC THEN METIS_TAC [is_head_redex_unique, labelled_redn_det]);

val head_reduct_NONE = store_thm(
  "head_reduct_NONE",
  ``(head_reduct M = NONE) = !N. ~(M -h-> N)``,
  SRW_TAC [][head_reduct_def, head_reduce1_def] THEN
  METIS_TAC [head_redex_is_redex, IN_term_IN_redex_posns,
             is_redex_occurrence_def]);

val head_reduct_SOME = store_thm(
  "head_reduct_SOME",
  ``(head_reduct M = SOME N) = M -h-> N``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, head_reduct_unique] THEN
  SRW_TAC [][head_reduct_def] THEN SELECT_ELIM_TAC THEN
  SRW_TAC [][head_reduce1_def] THEN
  METIS_TAC [head_redex_is_redex, IN_term_IN_redex_posns,
             is_redex_occurrence_def]);

val is_head_reduction_coind = store_thm(
  "is_head_reduction_coind",
  ``(!x r q. P (pcons x r q) ==>
             labelled_redn beta x r (first q) /\
             r is_head_redex x /\ P q) ==>
    !p. P p ==> is_head_reduction p``,
  SIMP_TAC (srw_ss()) [is_head_reduction_def, IMP_CONJ_THM,
                       FORALL_AND_THM] THEN CONJ_TAC
  THENL [
    STRIP_TAC THEN HO_MATCH_MP_TAC okpath_co_ind THEN METIS_TAC [],
    STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
    Q_TAC SUFF_TAC `!i. i + 1 IN PL p ==> nth_label i p is_head_redex el i p /\
                                          P (drop (i + 1) p)` THEN1
          METIS_TAC [] THEN
    Induct THEN FULL_SIMP_TAC (srw_ss()) [GSYM ADD1] THENL [
      Q.ISPEC_THEN `p` FULL_STRUCT_CASES_TAC path_cases THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [],
      STRIP_TAC THEN
      `SUC i IN PL p`
         by METIS_TAC [PL_downward_closed, DECIDE ``x < SUC x``] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Q.ISPEC_THEN `p` FULL_STRUCT_CASES_TAC path_cases THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `?y s q'. drop i q = pcons y s q'` by METIS_TAC [drop_not_stopped] THEN
      `labelled_redn beta y s (first q') /\ s is_head_redex y /\ P q'`
          by METIS_TAC [stopped_at_not_pcons, pcons_11] THEN
      `el 0 (drop i q) = el i q` by SRW_TAC [][] THEN
      `el i q = y` by METIS_TAC [el_def, first_thm] THEN
      `nth_label 0 (drop i q) = nth_label i q` by SRW_TAC [][] THEN
      `nth_label i q = s` by METIS_TAC [nth_label_def, first_label_def] THEN
      SRW_TAC [][drop_tail_commute]
    ]
  ]);

val head_reduction_path_uexists = prove(
  ``!M. ?!p. (first p = M) /\ is_head_reduction p /\
             (finite p ==> hnf (last p))``,
  GEN_TAC THEN
  Q.ISPEC_THEN `\M. (M, OPTION_MAP (\N. ((@r. r is_head_redex M), N))
                                  (head_reduct M))`
               STRIP_ASSUME_TAC path_Axiom THEN
  `!M. first (g M) = M`
      by (POP_ASSUM (fn th => SRW_TAC [][Once th]) THEN
          Cases_on `head_reduct M` THEN SRW_TAC [][]) THEN
  `!M. is_head_reduction (g M)`
      by (Q_TAC SUFF_TAC
                `!p. (?M. p = g M) ==> is_head_reduction p` THEN1
                METIS_TAC [] THEN
          HO_MATCH_MP_TAC is_head_reduction_coind THEN
          Q.PAT_X_ASSUM `!x:term. g x = Z`
                          (fn th => SIMP_TAC (srw_ss())
                                             [Once th, SimpL ``(==>)``]) THEN
          REPEAT GEN_TAC THEN STRIP_TAC THEN
          Cases_on `head_reduct M` THEN
          FULL_SIMP_TAC (srw_ss()) [head_reduct_SOME, head_reduce1_def] THEN
          REPEAT VAR_EQ_TAC THEN SELECT_ELIM_TAC THEN
          METIS_TAC [is_head_redex_unique]) THEN
  `!p. finite p ==> !M. (p = g M) ==> hnf (last p)`
      by (HO_MATCH_MP_TAC finite_path_ind THEN
          SIMP_TAC (srw_ss()) [] THEN CONJ_TAC THEN REPEAT GEN_TAC THENL [
            Q.PAT_X_ASSUM `!x:term. g x = Z`
                        (fn th => ONCE_REWRITE_TAC [th]) THEN
            Cases_on `head_reduct M` THEN SRW_TAC [][] THEN
            FULL_SIMP_TAC (srw_ss()) [hnf_no_head_redex, head_reduct_NONE,
                                      head_reduce1_def] THEN
            METIS_TAC [head_redex_is_redex, IN_term_IN_redex_posns,
                       is_redex_occurrence_def],
            STRIP_TAC THEN GEN_TAC THEN
            Q.PAT_X_ASSUM `!x:term. g x = Z`
                        (fn th => ONCE_REWRITE_TAC [th]) THEN
            Cases_on `head_reduct M` THEN SRW_TAC [][]
          ]) THEN
  SIMP_TAC (srw_ss()) [EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL [
    Q.EXISTS_TAC `g M` THEN
    Q.PAT_X_ASSUM `!x:term. g x = Z` (K ALL_TAC) THEN METIS_TAC [],
    REPEAT (POP_ASSUM (K ALL_TAC)) THEN
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [path_bisimulation] THEN
    Q.EXISTS_TAC `\p1 p2. is_head_reduction p1 /\ is_head_reduction p2 /\
                          (first p1 = first p2) /\
                          (finite p1 ==> hnf (last p1)) /\
                          (finite p2 ==> hnf (last p2))` THEN
    SRW_TAC [][] THEN
    Q.ISPEC_THEN `q1` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC)
                 path_cases THEN
    Q.ISPEC_THEN `q2` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC)
                 path_cases THEN FULL_SIMP_TAC (srw_ss()) []
    THENL [
      METIS_TAC [hnf_no_head_redex],
      METIS_TAC [hnf_no_head_redex],
      METIS_TAC [is_head_redex_unique, labelled_redn_det]
    ]
  ]);

(* moved here from standardisationScript.sml *)
val head_reduction_path_def = new_specification(
  "head_reduction_path_def",
  ["head_reduction_path"],
  CONJUNCT1 ((SIMP_RULE bool_ss [EXISTS_UNIQUE_THM] o
              SIMP_RULE bool_ss [UNIQUE_SKOLEM_THM])
             head_reduction_path_uexists));

val head_reduction_path_unique = store_thm(
  "head_reduction_path_unique",
  ``!M p. (first p = M) /\ is_head_reduction p /\
          (finite p ==> hnf (last p)) ==>
          (head_reduction_path M = p)``,
  REPEAT STRIP_TAC THEN
  Q.SPEC_THEN `M` (ASSUME_TAC o CONJUNCT2 o
                   SIMP_RULE bool_ss [EXISTS_UNIQUE_THM])
              head_reduction_path_uexists THEN
  METIS_TAC [head_reduction_path_def]);

Theorem infinite_is_head_reduction_drop :
    !p. infinite p /\ is_head_reduction p ==> !n. is_head_reduction (drop n p)
Proof
    NTAC 2 STRIP_TAC
 >> Induct_on ‘n’ >> rw []
 >> ‘!i. i IN PL p’ by PROVE_TAC [infinite_PL]
 >> rw [drop_tail_commute]
 >> REWRITE_TAC [GSYM ADD1]
 >> ‘infinite (drop n p)’ by PROVE_TAC [finite_drop]
 (* stage work *)
 >> Q.PAT_X_ASSUM ‘is_head_reduction (drop n p)’ MP_TAC
 >> Q.PAT_X_ASSUM ‘infinite p’ MP_TAC
 >> KILL_TAC
 >> rw [drop_def]
 >> ‘!i. i IN PL p’ by PROVE_TAC [infinite_PL]
 >> ASM_SIMP_TAC std_ss [drop_tail_commute]
 >> qabbrev_tac ‘q = drop n p’
 >> ‘infinite q’ by PROVE_TAC [finite_drop]
 >> ‘?x r xs. q = pcons x r xs’ by METIS_TAC [infinite_path_cases]
 >> POP_ASSUM (fs o wrap)
QED

Theorem finite_is_head_reduction_drop :
    !p. finite p /\ is_head_reduction p ==>
        !n. n < THE (length p) ==> is_head_reduction (drop n p)
Proof
    NTAC 2 STRIP_TAC
 >> ‘?N. length p = SOME (SUC N)’ by METIS_TAC [length_cases]
 >> fs []
 >> Q.PAT_X_ASSUM ‘is_head_reduction p’ MP_TAC
 >> Know ‘PL p = count (SUC N)’
 >- (rw [PL_def, count_def])
 >> DISCH_TAC
 >> simp [is_head_reduction_def]
QED

Theorem infinite_head_reduction_path_to_llist :
    !M. infinite (head_reduction_path M) <=>
        ?l. ~LFINITE l /\ (LNTH 0 l = SOME M) /\
            !i. THE (LNTH i l) -h-> THE (LNTH (SUC i) l)
Proof
    Q.X_GEN_TAC ‘M’
 >> qabbrev_tac ‘p = head_reduction_path M’
 >> EQ_TAC >> rpt STRIP_TAC
 >- (Q.EXISTS_TAC ‘LGENLIST (\n. el n p) NONE’ \\
     rw [LNTH_LGENLIST] >- (rw [Abbr ‘p’, head_reduction_path_def]) \\
     rw [head_reduce1_def] \\
    ‘!i. i IN PL p’ by PROVE_TAC [infinite_PL] \\
     qabbrev_tac ‘q = drop i p’ \\
    ‘el i p = first q’ by rw [Abbr ‘q’] >> POP_ORW \\
     Know ‘el i (tail p) = first (tail q)’
     >- (rw [Abbr ‘q’, REWRITE_RULE [ADD1] el_def]) >> Rewr' \\
    ‘infinite q’ by PROVE_TAC [finite_drop] \\
     Know ‘is_head_reduction q’
     >- (qunabbrev_tac ‘q’ \\
         MATCH_MP_TAC infinite_is_head_reduction_drop \\
         rw [Abbr ‘p’, head_reduction_path_def]) >> DISCH_TAC \\
    ‘?x r xs. q = pcons x r xs’ by METIS_TAC [infinite_path_cases] \\
     fs [is_head_reduction_thm] \\
     Q.EXISTS_TAC ‘r’ >> art [])
 (* stage work *)
 >> qabbrev_tac ‘f = \i. THE (LNTH i l)’
 >> Know ‘!i. ?r. r is_head_redex (f i) /\ labelled_redn beta (f i) r (f (SUC i))’
 >- (Q.X_GEN_TAC ‘n’ \\
     Know ‘f n -h-> f (SUC n)’ >- PROVE_TAC [] \\
     rw [head_reduce1_def] \\
     Q.EXISTS_TAC ‘r’ >> art [])
 (* this asserts ‘g’ as the path label generator *)
 >> DISCH_THEN ((Q.X_CHOOSE_THEN ‘g’ STRIP_ASSUME_TAC) o
                (SIMP_RULE std_ss [SKOLEM_THM]))
 >> qabbrev_tac ‘q = pgenerate f g’
 >> ‘infinite q’ by PROVE_TAC [pgenerate_infinite]
 >> Suff ‘head_reduction_path M = q’ >- PROVE_TAC []
 (* applying head_reduction_path_unique *)
 >> MATCH_MP_TAC head_reduction_path_unique >> simp []
 >> CONJ_TAC
 >- ASM_SIMP_TAC std_ss [Abbr ‘q’, GSYM el_def, el_pgenerate, Abbr ‘f’]
 >> Q.PAT_X_ASSUM ‘finite p’ K_TAC
 >> qunabbrev_tac ‘p’
 >> rename1 ‘is_head_reduction p’
 >> ‘!i. i IN PL p’ by PROVE_TAC [infinite_PL]
 (* applying is_head_reduction_coind *)
 >> irule is_head_reduction_coind
 >> Q.EXISTS_TAC ‘\q. ?i. q = drop i p’ >> simp []
 >> CONJ_TAC >- (Q.EXISTS_TAC ‘0’ >> rw [])
 >> rpt GEN_TAC >> STRIP_TAC
 >> Know ‘(first (pcons x r q) = first (drop i p)) /\
          (first_label (pcons x r q) = first_label (drop i p)) /\
          (tail (pcons x r q) = tail (drop i p))’ >- art []
 >> simp []
 >> DISCH_THEN (fs o wrap)
 >> ‘nth_label i p = g i’ by (rw [Abbr ‘p’, nth_label_pgenerate])
 >> ‘!i. el i p = f i’    by (rw [Abbr ‘p’, el_pgenerate])
 >> ASM_REWRITE_TAC [GSYM ADD1]
 >> Q.EXISTS_TAC ‘SUC i’ >> REWRITE_TAC []
QED

Theorem finite_head_reduction_path_to_list :
    !M. finite (head_reduction_path M) <=>
        ?l. l <> [] /\ (HD l = M) /\ hnf (LAST l) /\
            !i. SUC i < LENGTH l ==> EL i l -h-> EL (SUC i) l
Proof
    Q.X_GEN_TAC ‘M’
 >> qabbrev_tac ‘p = head_reduction_path M’
 >> EQ_TAC >> rpt STRIP_TAC
 >- (‘?n. length p = SOME n’ by METIS_TAC [finite_length] \\
     Cases_on ‘n’ >- fs [length_never_zero] \\
     rename1 ‘length p = SOME (SUC n)’ \\
     Q.EXISTS_TAC ‘GENLIST (\i. el i p) (SUC n)’ >> simp [] \\
     STRONG_CONJ_TAC >- rw [NOT_NIL_EQ_LENGTH_NOT_0] >> DISCH_TAC \\
     CONJ_TAC >- rw [GSYM EL, Abbr ‘p’, head_reduction_path_def] \\
     CONJ_TAC (* hnf *)
     >- (qabbrev_tac ‘l = GENLIST (\i. el i p) (SUC n)’ \\
         rw [Abbr ‘l’, LAST_EL] \\
         Suff ‘el n p = last p’ >- rw [Abbr ‘p’, head_reduction_path_def] \\
         rw [finite_last_el]) \\
     rw [head_reduce1_def] \\
    ‘i IN PL p /\ i + 1 IN PL p’ by rw [PL_def] \\
     qabbrev_tac ‘q = drop i p’ \\
    ‘el i p = first q’ by rw [Abbr ‘q’] >> POP_ORW \\
     Know ‘el i (tail p) = first (tail q)’
     >- (rw [Abbr ‘q’, REWRITE_RULE [ADD1] el_def]) >> Rewr' \\
     Know ‘is_head_reduction q’
     >- (qunabbrev_tac ‘q’ \\
         irule finite_is_head_reduction_drop \\
         rw [Abbr ‘p’, head_reduction_path_def]) >> DISCH_TAC \\
  (* perform case analysis *)
    ‘(?x. q = stopped_at x) \/ ?x r xs. q = pcons x r xs’ by METIS_TAC [path_cases]
     >- (Know ‘PL q = IMAGE (\n. n - i) (PL p)’
         >- rw [Abbr ‘q’, PL_drop] \\
        ‘PL p = count (SUC n)’ by rw [PL_def, count_def] >> POP_ORW \\
         POP_ORW (* q = stopped_at x *) \\
         simp [PL_stopped_at] \\
         Suff ‘IMAGE (\n. n - i) (count (SUC n)) <> {0}’ >- METIS_TAC [] \\
         rw [Once EXTENSION] \\
         Q.EXISTS_TAC ‘n - i’ >> rw [] \\
         Q.EXISTS_TAC ‘n’ >> art []) \\
     fs [is_head_reduction_thm] \\
     Q.EXISTS_TAC ‘r’ >> art [])
 (* stage work *)
 >> qabbrev_tac ‘len = LENGTH l’
 >> ‘0 < len /\ len <> 0’ by rw [Abbr ‘len’, GSYM NOT_NIL_EQ_LENGTH_NOT_0]
 >> Know ‘!i. SUC i < len ==>
              ?r. r is_head_redex (EL i l) /\ labelled_redn beta (EL i l) r (EL (SUC i) l)’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!i. SUC i < len ==> P’ (Q.SPEC_THEN ‘i’ MP_TAC) \\
     rw [head_reduce1_def])
 >> DISCH_TAC
 (* this asserts ‘f’ as the path label generator *)
 >> FULL_SIMP_TAC std_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
 >> qabbrev_tac ‘nl = GENLIST I (PRE len)’
 >> qabbrev_tac ‘g = \i. pcons (EL i l) (f i)’
 >> qabbrev_tac ‘q = FOLDR g (stopped_at (LAST l)) nl’
 >> Know ‘finite q’
 >- (qunabbrev_tac ‘q’ \\
     Q.PAT_X_ASSUM ‘Abbrev (nl = _)’ K_TAC \\
     Induct_on ‘nl’ >- rw [] \\
     rw [Abbr ‘g’])
 >> DISCH_TAC
 (* applying head_reduction_path_unique *)
 >> Suff ‘head_reduction_path M = q’ >- PROVE_TAC []
 >> MATCH_MP_TAC head_reduction_path_unique >> simp []
 (* stage work *)
 >> CONJ_TAC (* first q = M *)
 >- (‘(len = 1) \/ 1 < len’ by rw []
     >- (rw [Abbr ‘nl’, Abbr ‘q’, HD_GENLIST, LAST_EL]) \\
     Know ‘HD nl = 0’
     >- (rw [Abbr ‘nl’] \\
         Cases_on ‘len’ >> rw [] \\
         Cases_on ‘n’ >> rw [HD_GENLIST]) >> DISCH_TAC \\
    ‘0 < PRE len’ by (Cases_on ‘len’ >> rw []) \\
    ‘nl <> []’ by (rw [Abbr ‘nl’, NOT_NIL_EQ_LENGTH_NOT_0]) \\
     Cases_on ‘nl’ >> fs [EL, Abbr ‘q’, Abbr ‘g’])
 >> qunabbrev_tac ‘p’
 >> Q.PAT_X_ASSUM ‘finite q’ K_TAC
 (* stage work *)
 >> reverse CONJ_TAC (* hnf (last q) *)
 >- (qunabbrev_tac ‘q’ \\
     Q.PAT_X_ASSUM ‘Abbrev (nl = _)’ K_TAC \\
     Induct_on ‘nl’ >- rw [] \\
     rw [Abbr ‘g’])
 >> rename1 ‘is_head_reduction p’
 (* applying is_head_reduction_thm *)
 >> qunabbrev_tac ‘p’
 >> ‘nl = DROP (PRE len - PRE len) nl’ by rw [] >> POP_ORW
 >> Suff ‘!n. n < len ==>
              is_head_reduction (FOLDR g (stopped_at (LAST l)) (DROP (PRE len - n) nl))’
 >- rw []
 >> Induct_on ‘n’ >> simp []
 >- (Know ‘DROP (PRE len) nl = []’
     >- (MATCH_MP_TAC DROP_LENGTH_TOO_LONG >> rw [Abbr ‘len’, Abbr ‘nl’]) >> Rewr' \\
     rw [Abbr ‘g’, is_head_reduction_thm])
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘n < len ==> P’ MP_TAC
 >> Know ‘n < len’ >- rw []
 >> RW_TAC std_ss []
 >> qabbrev_tac ‘k = PRE len - SUC n’
 >> Q.PAT_X_ASSUM ‘is_head_reduction _’ MP_TAC
 >> ‘PRE len - n = SUC k’ by rw [Abbr ‘k’] >> POP_ORW
 >> ‘(len = 1) \/ 1 < len’ by rw [] >- rw [Abbr ‘nl’]
 >> ‘0 < PRE len’ by (Cases_on ‘len’ >> rw [])
 >> ‘nl <> []’ by (rw [Abbr ‘nl’, NOT_NIL_EQ_LENGTH_NOT_0])
 >> Know ‘HD nl = 0’
 >- (rw [Abbr ‘nl’] \\
     Cases_on ‘len’ >> rw [] \\
     rename1 ‘n < SUC m’ \\
     Cases_on ‘m’ >> rw [HD_GENLIST])
 >> DISCH_TAC
 >> ‘?x xs. nl = x::xs’ by METIS_TAC [list_CASES] >> gs []
 >> Cases_on ‘k = 0’ >> rw []
 >- (RW_TAC std_ss [DROP_def ,Abbr ‘g’] \\
     RW_TAC arith_ss [is_head_reduction_thm] \\
    ‘SUC 0 < len’ by rw [] \\
     Suff ‘first (FOLDR (\i. pcons (EL i l) (f i)) (stopped_at (LAST l)) xs) =
           EL (SUC 0) l’ >- RW_TAC bool_ss [] \\
     Cases_on ‘xs = []’
     >- (fs [is_head_reduction_thm, LAST_EL] \\
         Know ‘LENGTH (GENLIST I (PRE len)) = LENGTH [0]’ >- art [] \\
         simp []) \\
    ‘?y ys. xs = y::ys’ by METIS_TAC [list_CASES] >> rw [] \\
     Know ‘y = EL 1 (GENLIST I (PRE len))’ >- rw [] \\
     Know ‘LENGTH (GENLIST I (PRE len)) = LENGTH (0::y::ys)’ >- art [] \\
     simp [])
 (* stage work *)
 >> qabbrev_tac ‘ys = DROP k xs’
 >> Know ‘DROP (k - 1) xs = EL (k - 1) xs::ys’
 >- (qunabbrev_tac ‘ys’ \\
     MATCH_MP_TAC LIST_EQ >> rw []
     >- (rw [SUB_LEFT_SUC] \\
         Know ‘LENGTH (GENLIST I (PRE len)) = LENGTH (0::xs)’ >- art [] \\
         simp [Abbr ‘k’]) \\
     Cases_on ‘x = 0’ >- (rw [HD_DROP]) \\
    ‘x + k - 1 < LENGTH xs’ by rw [] \\
     rw [EL_DROP] \\
     Cases_on ‘x’ >> rw [] \\
     rename1 ‘SUC m + k - 1 < LENGTH xs’ \\
    ‘m + k < LENGTH xs’ by rw [] \\
     rw [EL_DROP] \\
     Suff ‘k + SUC m - 1 = k + m’ >- Rewr \\
     numLib.ARITH_TAC)
 >> Rewr'
 >> Know ‘EL (k - 1) xs = EL (SUC (k - 1)) (GENLIST I (PRE len))’
 >- rw []
 >> ‘SUC (k - 1) = k’ by rw [] >> POP_ORW
 >> ‘k < PRE len’ by rw [Abbr ‘k’]
 >> rw [EL_GENLIST]
 >> Q.PAT_X_ASSUM ‘!i. SUC i < len ==> P’ (MP_TAC o (Q.SPEC ‘k’))
 >> rw [Abbr ‘g’]
 >> Suff ‘first (FOLDR (\i. pcons (EL i l) (f i)) (stopped_at (LAST l)) ys) =
          EL (SUC k) l’ >- RW_TAC bool_ss []
 >> Cases_on ‘ys = []’
 >- (fs [is_head_reduction_thm, LAST_EL] \\
     Suff ‘PRE len = SUC k’ >- rw [] \\
    ‘LENGTH xs <= k’ by fs [Abbr ‘ys’, DROP_EQ_NIL] \\
     Know ‘LENGTH (GENLIST I (PRE len)) = LENGTH (0::xs)’ >- art [] \\
     simp [])
 >> ‘k < LENGTH xs’ by fs [Abbr ‘ys’, DROP_EQ_NIL]
 >> ‘?z zs. ys = z::zs’ by METIS_TAC [list_CASES] >> rw []
 >> ‘z = HD (DROP k xs)’ by rw [] >> POP_ORW
 >> rw [HD_DROP]
 (* preparing for EL_GENLIST *)
 >> Suff ‘EL k xs = I (SUC k)’ >- rw []
 >> Know ‘EL k xs = EL (SUC k) (GENLIST I (PRE len))’ >- rw []
 >> Rewr'
 >> MATCH_MP_TAC EL_GENLIST
 >> Know ‘LENGTH (GENLIST I (PRE len)) = LENGTH (0::xs)’ >- art []
 >> simp []
QED

(* cf. Omega_starloops *)
Theorem Omega_hreduce1_loops :
    Omega -h-> N <=> (N = Omega)
Proof
    rw [hreduce1_rwts, Omega_def]
QED

(*---------------------------------------------------------------------------*
 *  Accessors of hnf components
 *---------------------------------------------------------------------------*)

Definition hnf_head_def :
    hnf_head t = if is_comb t then hnf_head (rator t) else t
Termination
    WF_REL_TAC ‘measure size’
 >> rw [is_comb_APP_EXISTS] >> rw []
End

Theorem hnf_head_appstar :
    !t. ~is_comb t ==> (hnf_head (t @* args) = t)
Proof
    Induct_on ‘args’ using SNOC_INDUCT
 >> rw [appstar_SNOC, Once hnf_head_def, FOLDL]
QED

Theorem hnf_head_hnf[simp] :
    (hnf_head (VAR y @@ t) = VAR y) /\
    (hnf_head (VAR y @* args) = VAR y)
Proof
    CONJ_TAC
 >- NTAC 2 (rw [Once hnf_head_def])
 >> MATCH_MP_TAC hnf_head_appstar
 >> rw []
QED

Overload hnf_headvar = “\t. THE_VAR (hnf_head t)”

(* hnf_children retrives the ‘args’ part of an abs-free hnf (VAR y @* args) *)
Definition hnf_children_def :
    hnf_children t = if is_comb t then
                        SNOC (rand t) (hnf_children (rator t))
                     else []
Termination
    WF_REL_TAC ‘measure size’ >> rw [is_comb_APP_EXISTS] >> rw []
End

Theorem hnf_children_thm :
   (!y.     hnf_children ((VAR :string -> term) y) = []) /\
   (!v t.   hnf_children (LAM v t) = []) /\
   (!t1 t2. hnf_children (t1 @@ t2) = SNOC t2 (hnf_children t1))
Proof
   rpt (rw [Once hnf_children_def])
QED

Theorem hnf_children_appstar :
    !t. ~is_comb t ==> (hnf_children (t @* args) = args)
Proof
    Induct_on ‘args’ using SNOC_INDUCT
 >- rw [Once hnf_children_def, FOLDL]
 >> RW_TAC std_ss [appstar_SNOC]
 >> rw [Once hnf_children_def]
QED

Theorem hnf_children_hnf :
    !y args. hnf_children (VAR y @* args) = args
Proof
    rpt GEN_TAC
 >> MATCH_MP_TAC hnf_children_appstar >> rw []
QED

Theorem absfree_hnf_cases :
    !M. hnf M /\ ~is_abs M <=> ?y args. M = VAR y @* args
Proof
    Q.X_GEN_TAC ‘M’
 >> EQ_TAC
 >- (STRIP_TAC \\
    ‘?vs args y. ALL_DISTINCT vs /\ (M = LAMl vs (VAR y @* args))’
        by METIS_TAC [hnf_cases] \\
     reverse (Cases_on ‘vs = []’) >- fs [] \\
     qexistsl_tac [‘y’, ‘args’] >> rw [LAMl_thm])
 >> rpt STRIP_TAC
 >- rw [hnf_appstar]
 >> rfs [is_abs_cases]
QED

Theorem absfree_hnf_thm :
    !M. hnf M /\ ~is_abs M ==> (M = hnf_head M @* hnf_children M)
Proof
    rw [absfree_hnf_cases]
 >> rw [hnf_children_appstar, hnf_head_appstar]
QED

Theorem hnf_head_absfree :
    !y args. hnf_head (VAR y @* args) = VAR y
Proof
    rpt GEN_TAC
 >> MATCH_MP_TAC hnf_head_appstar >> rw []
QED

Theorem lameq_hnf_fresh_subst :
    !as args P. (LENGTH args = LENGTH as) /\ DISJOINT (set as) (FV P) ==>
                ([LAMl as P/y] (VAR y @* args) == P)
Proof
    Induct_on ‘as’ using SNOC_INDUCT >> rw []
 >> Cases_on ‘args = []’ >- fs []
 >> ‘args = SNOC (LAST args) (FRONT args)’ by PROVE_TAC [SNOC_LAST_FRONT]
 >> POP_ORW
 >> REWRITE_TAC [appstar_SNOC, SUB_THM]
 >> MATCH_MP_TAC lameq_TRANS
 >> qabbrev_tac ‘M = [LAMl as (LAM x P)/y] (LAST args)’
 >> Q.EXISTS_TAC ‘LAM x P @@ M’
 >> CONJ_TAC
 >- (MATCH_MP_TAC lameq_APPL \\
     FIRST_X_ASSUM MATCH_MP_TAC >> rw [FV_thm, LENGTH_FRONT] \\
     Q.PAT_X_ASSUM ‘DISJOINT _ _’ MP_TAC \\
     rw [DISJOINT_ALT])
 >> rw [Once lameq_cases] >> DISJ1_TAC
 >> qexistsl_tac [‘x’, ‘P’] >> art []
 >> MATCH_MP_TAC (GSYM lemma14b)
 >> Q.PAT_X_ASSUM ‘DISJOINT _ _’ MP_TAC
 >> rw [DISJOINT_ALT]
QED

(*---------------------------------------------------------------------------*
 *  LAMl_size (of hnf)
 *---------------------------------------------------------------------------*)

val (LAMl_size_thm, _) = define_recursive_term_function
   ‘(LAMl_size ((VAR :string -> term) s) = 0) /\
    (LAMl_size (t1 @@ t2) = 0) /\
    (LAMl_size (LAM v t) = 1 + LAMl_size t)’;

val _ = export_rewrites ["LAMl_size_thm"];

Theorem LAMl_size_0_cases :
    !t. is_var t \/ is_comb t ==> (LAMl_size t = 0)
Proof
    rw [is_var_cases, is_comb_APP_EXISTS]
 >> rw []
QED

Theorem LAMl_size_0_cases' :
    !t. ~is_abs t ==> (LAMl_size t = 0)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC LAMl_size_0_cases
 >> METIS_TAC [term_cases]
QED

Theorem LAMl_size_LAMl :
    !vs t. ~is_abs t ==> (LAMl_size (LAMl vs t) = LENGTH vs)
Proof
    rpt STRIP_TAC
 >> Induct_on ‘vs’
 >- rw [LAMl_size_0_cases']
 >> rw []
QED

Theorem LAMl_size_hnf[simp] :
    LAMl_size (LAMl vs (VAR y @* args)) = LENGTH vs
Proof
    MATCH_MP_TAC LAMl_size_LAMl
 >> Cases_on ‘args = []’ >- rw []
 >> ‘?x l. args = SNOC x l’ by METIS_TAC [SNOC_CASES]
 >> rw [appstar_SNOC]
QED

Theorem LAMl_size_hnf_absfree[simp] :
    LAMl_size (VAR y @* args) = 0
Proof
    Cases_on ‘args = []’ >- rw []
 >> ‘?x l. args = SNOC x l’ by METIS_TAC [SNOC_CASES]
 >> rw [appstar_SNOC]
QED

(* Another variant of ‘hnf_cases’ with a given (shared) list of fresh variables

   NOTE: "irule (iffLR hnf_cases_shared)" is a useful tactic for this theorem.
 *)
Theorem hnf_cases_shared :
    !vs M. ALL_DISTINCT vs /\ LAMl_size M <= LENGTH vs /\
           DISJOINT (set vs) (FV M) ==>
          (hnf M <=> ?y args. (M = LAMl (TAKE (LAMl_size M) vs) (VAR y @* args)))
Proof
    rpt STRIP_TAC
 >> reverse EQ_TAC
 >- (STRIP_TAC >> POP_ORW \\
     rw [hnf_appstar, hnf_LAMl])
 >> rpt (POP_ASSUM MP_TAC)
 >> Q.ID_SPEC_TAC ‘M’
 >> Induct_on ‘vs’
 >- (rw [] \\
    ‘?vs args y. M = LAMl vs (VAR y @* args)’ by METIS_TAC [hnf_cases] \\
     fs [LAMl_size_hnf])
 (* stage work *)
 >> rw [LIST_TO_SET_SNOC, ALL_DISTINCT_SNOC]
 >> fs []
 >> Cases_on ‘LAMl_size M = 0’
 >- (fs [] \\
     Q.PAT_X_ASSUM ‘!M. P’ (MP_TAC o (Q.SPEC ‘M’)) >> rw [])
 >> ‘is_abs M’ by METIS_TAC [LAMl_size_0_cases']
 (* applying is_abs_cases_genX *)
 >> ‘?t0. M = LAM h t0’ by METIS_TAC [is_abs_cases_genX]
 >> FIRST_X_ASSUM (MP_TAC o (Q.SPEC ‘t0’))
 >> ‘hnf t0’ by METIS_TAC [hnf_thm]
 >> fs [LAMl_size_hnf]
 >> Suff ‘DISJOINT (set vs) (FV t0)’ >- rw []
 >> Q.PAT_X_ASSUM ‘DISJOINT _ _’ MP_TAC
 >> rw [DISJOINT_ALT]
 >> METIS_TAC []
QED

val _ = export_theory()
val _ = html_theory "head_reduction";

(* References:

   [1] Barendregt, H.P.: The Lambda Calculus, Its Syntax and Semantics.
       College Publications, London (1984).
 *)
