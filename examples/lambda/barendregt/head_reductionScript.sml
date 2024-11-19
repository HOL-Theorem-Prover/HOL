(* ========================================================================== *)
(* FILE    : head_reductionScript.sml                                         *)
(* TITLE   : Head Reduction of Lambda Terms and (Weak) Head Normal Forms      *)
(*                                                                            *)
(* AUTHORS : 2005-2011 Michael Norrish                                        *)
(*         : 2023-2024 Michael Norrish and Chun Tian                          *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib BasicProvers;

open boolSimps relationTheory pred_setTheory listTheory finite_mapTheory
     arithmeticTheory llistTheory pathTheory optionTheory rich_listTheory
     hurdUtils pairTheory;

open termTheory appFOLDLTheory chap2Theory chap3Theory nomsetTheory binderLib
     horeductionTheory term_posnsTheory finite_developmentsTheory
     basic_swapTheory;

val _ = new_theory "head_reduction"

val _ = hide "Y";

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

Theorem hreduce1_beta_reduce[simp] :
     LAM h M @@ VAR h -h-> M
Proof
    MP_TAC (Q.SPECL [‘h’, ‘M’, ‘VAR h’] hreduce1_BETA)
 >> REWRITE_TAC [lemma14a]
QED

Theorem hreduce_TRANS :
    !M0 M1 M2. M0 -h->* M1 /\ M1 -h->* M2 ==> M0 -h->* M2
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC (REWRITE_RULE [transitive_def] RTC_TRANSITIVE)
 >> Q.EXISTS_TAC ‘M1’ >> art []
QED

val hreduce_ccbeta = store_thm(
  "hreduce_ccbeta",
  ``∀M N. M -h-> N ⇒ M -β-> N``,
  HO_MATCH_MP_TAC hreduce1_ind THEN SRW_TAC [][cc_beta_thm] THEN
  METIS_TAC []);

val hreduce1_FV = store_thm(
  "hreduce1_FV",
  ``∀M N. M -h-> N ⇒ ∀v. v ∈ FV N ⇒ v ∈ FV M``,
  METIS_TAC [SUBSET_DEF, hreduce_ccbeta, cc_beta_FV_SUBSET]);

(* |- !M N. M -h-> N ==> FV N SUBSET FV M *)
Theorem hreduce1_FV_SUBSET = hreduce1_FV |> REWRITE_RULE [GSYM SUBSET_DEF]

Theorem hreduces_FV :
    ∀M N. M -h->* N ⇒ v ∈ FV N ⇒ v ∈ FV M
Proof
    HO_MATCH_MP_TAC relationTheory.RTC_INDUCT
 >> METIS_TAC [relationTheory.RTC_RULES, hreduce1_FV]
QED

Theorem hreduce_FV_SUBSET :
    !M N. M -h->* N ==> FV N SUBSET FV M
Proof
    rw [SUBSET_DEF]
 >> irule hreduces_FV
 >> Q.EXISTS_TAC ‘N’ >> art []
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

Theorem tpm_hreduces_I[local] :
    !M N. M -h->* N ==> tpm pi M -h->* tpm pi N
Proof
    HO_MATCH_MP_TAC RTC_INDUCT >> rw []
 >> rw [Once RTC_CASES1]
 >> DISJ2_TAC
 >> Q.EXISTS_TAC ‘tpm pi M'’ >> rw []
QED

Theorem tpm_hreduces[simp] :
    !pi M N. tpm pi M -h->* tpm pi N <=> M -h->* N
Proof
    METIS_TAC [pmact_inverse, tpm_hreduces_I]
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

Theorem hreduce1_appstar :
    !Ns. M1 -h-> M2 /\ ~is_abs M1 ==> M1 @* Ns -h-> M2 @* Ns
Proof
    Induct_on ‘Ns’ using SNOC_INDUCT
 >> rw [appstar_SNOC]
 >> fs [hreduce1_rules]
QED

Theorem hreduce_BETA_extended :
    !l vs t. LAMl vs t @* MAP VAR vs @* MAP VAR l -h->* t @* MAP VAR l
Proof
    Q.X_GEN_TAC ‘l’
 >> Induct_on ‘vs’ >- rw []
 >> rw [Once RTC_CASES1]
 >> DISJ2_TAC
 >> qabbrev_tac ‘M = LAMl vs t’
 >> Q.EXISTS_TAC ‘[VAR h/h] M @* MAP VAR vs @* MAP VAR l’
 >> reverse CONJ_TAC >- rw [Abbr ‘M’]
 >> REWRITE_TAC [GSYM appstar_APPEND]
 >> MATCH_MP_TAC hreduce1_appstar
 >> rw [hreduce1_BETA]
QED

(* |- !vs t. LAMl vs t @* MAP VAR vs -h->* t *)
Theorem hreduce_BETA[simp] =
        hreduce_BETA_extended |> Q.SPEC ‘[]’
                              |> REWRITE_RULE [MAP, appstar_empty]

Theorem hreduce1_LAMl[simp] :
    !vs M1 M2. LAMl vs M1 -h-> LAMl vs M2 <=> M1 -h-> M2
Proof
    Induct_on ‘vs’
 >> rw [Once hreduce1_rwts]
QED

Theorem hreduce_LAMl[simp] :
    !vs M1 M2. LAMl vs M1 -h->* LAMl vs M2 <=> M1 -h->* M2
Proof
    rpt GEN_TAC
 >> reverse EQ_TAC
 >- (Q.ID_SPEC_TAC ‘M2’ \\
     Q.ID_SPEC_TAC ‘M1’ \\
     HO_MATCH_MP_TAC RTC_INDUCT >> rw [] \\
     ONCE_REWRITE_TAC [RTC_CASES1] >> DISJ2_TAC \\
     Q.EXISTS_TAC ‘LAMl vs M1'’ >> rw [])
 >> Q.ID_SPEC_TAC ‘vs’
 >> Induct_on ‘vs’ >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> POP_ASSUM MP_TAC
 >> Suff ‘!M2 M. M -h->* LAM h M2 ==> !M1. (M = LAM h M1) ==> M1 -h->* M2’
 >- PROVE_TAC []
 >> Q.X_GEN_TAC ‘M2’
 >> HO_MATCH_MP_TAC RTC_ALT_INDUCT >> rw []
 >> Q.PAT_X_ASSUM ‘LAM h M1 -h-> M'’ MP_TAC
 >> rw [Once hreduce1_rwts]
 >> rename1 ‘M1 -h-> M0’
 >> ONCE_REWRITE_TAC [RTC_CASES1] >> DISJ2_TAC
 >> Q.EXISTS_TAC ‘M0’ >> rw []
QED

Theorem hreduce1_abs :
    !M N. M -h-> N ==> is_abs M ==> is_abs N
Proof
    rw [Once hreduce1_cases] >> fs []
QED

Theorem hreduce_abs :
    !M N. M -h->* N ==> is_abs M ==> is_abs N
Proof
    HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1
 >> rw []
 >> irule hreduce1_abs
 >> Q.EXISTS_TAC ‘N’ >> art []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

(* NOTE: Initially M1 is an APP, eventually it may become a VAR, never be LAM

   The condition ‘!M. M1 -h->* M /\ M -h-> M2 ==> ~is_abs M’ cannot be further
   reduced. It says that all head reductions between M1 and M2 (excluded) must
   not be abstractions. Only starting from M2 it can be abstractions.

   NOTE2: for ‘!M. M1 -h->* M /\ M -h-> M2 ==> ~is_abs M’ to hold, ‘M1’ usually
   must be solvable (i.e. having finite head reduction path). If this is NOT the
   case, then there may be an infinite head reduction path such that

      M1 -h-> M -h-> ... -h-> M2 -h-> ... -h-> M2

   which indicates ‘~is_abs M2’ (see also [hreduce_rules_appstar']).

   NOTE3: note that there's no requirements on ‘Ns’, which can be anything.
 *)
Theorem hreduce_rules_appstar :
    !M1 M2 Ns. ~is_abs M1 /\ (!M. M1 -h->* M /\ M -h-> M2 ==> ~is_abs M) /\
               M1 -h->* M2 ==> M1 @* Ns -h->* M2 @* Ns
Proof
    rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘~is_abs M1’ MP_TAC
 >> Q.PAT_X_ASSUM ‘!M. P’ MP_TAC
 >> POP_ASSUM MP_TAC
 >> Q.ID_SPEC_TAC ‘M2’
 >> Q.ID_SPEC_TAC ‘M1’
 >> HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 >> rw []
 >> rw [Once RTC_CASES2] >> DISJ2_TAC
 >> Q.EXISTS_TAC ‘M2 @* Ns’
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC hreduce1_appstar >> art [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> FIRST_X_ASSUM irule >> rw []
 >> CCONTR_TAC >> fs []
 >> ‘is_abs M2’ by PROVE_TAC [hreduce1_abs]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> PROVE_TAC []
QED

(* slight weaker but more useful *)
Theorem hreduce_rules_appstar' :
    !M1 M2 Ns. ~is_abs M1 /\ ~is_abs M2 /\ M1 -h->* M2 ==> M1 @* Ns -h->* M2 @* Ns
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC hreduce_rules_appstar >> art []
 >> rpt STRIP_TAC
 >> PROVE_TAC [hreduce1_abs]
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

(* hreduce1 and ISUB *)
Theorem hreduce1_ISUB :
    !sub M N. M -h-> N ==> M ISUB sub -h-> N ISUB sub
Proof
    Induct_on ‘sub’ >- rw []
 >> SIMP_TAC std_ss [FORALL_PROD, ISUB_def]
 >> rpt STRIP_TAC
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> MATCH_MP_TAC hreduce1_substitutive >> art []
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

(* hreduce and ISUB *)
Theorem hreduce_ISUB :
    !sub M N. M -h->* N ==> M ISUB sub -h->* N ISUB sub
Proof
    Induct_on ‘sub’ >- rw []
 >> SIMP_TAC std_ss [FORALL_PROD, ISUB_def]
 >> rpt STRIP_TAC
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> MATCH_MP_TAC hreduce_substitutive >> art []
QED

(* This nice and hard-to-prove theorem gives a precise explicit form for any
   lambda term whose single-step head reduction is in the form of ‘LAMl vs t’.

   NOTE: This proof is hard in the sense that some primitive theorems from
   nomsetTheory are used. And ‘~is_abs t’ is necessary for the case vs = [].
 *)
Theorem hreduce1_LAMl_cases :
    !M vs t. ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M) /\
             M -h-> LAMl vs t /\ ~is_abs t ==>
        ?vs1 vs2 N. (vs = vs1 ++ vs2) /\ (M = LAMl vs1 N) /\ ~is_abs N /\
                    N -h-> LAMl vs2 t
Proof
    HO_MATCH_MP_TAC simple_induction >> rw []
 >> Cases_on ‘vs = []’
 >- (Q.PAT_X_ASSUM ‘LAM v M -h-> LAMl vs t’ MP_TAC \\
     rw [Once hreduce1_cases] >> fs [])
 >> Cases_on ‘vs’ >> FULL_SIMP_TAC list_ss []
 >> rename1 ‘LAM v M -h-> LAM h (LAMl vs t)’
 >> Q.PAT_X_ASSUM ‘T’ K_TAC
 >> Q.PAT_X_ASSUM ‘LAM v M -h-> _’ MP_TAC
 >> rw [Once hreduce1_cases]
 >> Q.PAT_X_ASSUM ‘LAM v M = LAM v' M1’ MP_TAC
 >> rw [LAM_eq_thm]
  (* v = v' *)
 >- (fs [LAM_eq_thm] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       Q.PAT_X_ASSUM ‘h = v’ (fs o wrap) \\
      ‘FV M DELETE v = FV M’ by ASM_SET_TAC [] >> fs [] \\
       Q.PAT_X_ASSUM ‘!vs t. P’ (MP_TAC o (Q.SPECL [‘vs’, ‘t’])) >> rw [] \\
       fs [LAMl_APPEND] \\
       qexistsl_tac [‘v::vs1’, ‘vs2’, ‘N’] >> rw [],
       (* goal 2 (of 4) *)
       fs [tpm_eqr, tpm_LAMl] \\
       qabbrev_tac ‘vs' = listpm string_pmact [(h,v)] vs’ \\
       qabbrev_tac ‘t' = tpm [(h,v)] t’ \\
      ‘ALL_DISTINCT vs'’ by rw [ALL_DISTINCT_listpm, Abbr ‘vs'’] \\
       Know ‘DISJOINT (set vs') (FV M)’
       >- (rw [DISJOINT_ALT, Abbr ‘vs'’, MEM_listpm] \\
           Cases_on ‘x = h’ >- art [] \\
           Cases_on ‘x = v’ >- fs [] \\
           Q.PAT_X_ASSUM ‘DISJOINT (set vs) (FV M DELETE v)’ MP_TAC \\
           rw [DISJOINT_ALT] >> fs [] \\
           METIS_TAC []) >> DISCH_TAC \\
       Q.PAT_X_ASSUM ‘!vs t. P’ (MP_TAC o (Q.SPECL [‘vs'’, ‘t'’])) \\
       Know ‘~is_abs t'’ >- rw [Abbr ‘t'’, is_abs_cases] >> rw [] \\
       Know ‘vs = listpm string_pmact [(v,h)] (vs1 ++ vs2)’
       >- (Q.PAT_X_ASSUM ‘_ = vs1 ++ vs2’ MP_TAC \\
           NTAC 2 (rw [Once LIST_EQ_REWRITE]) \\
           Know ‘EL x (vs1 ++ vs2) = swapstr h v (EL x vs)’
           >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
               FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr' \\
           simp []) >> Rewr' \\
       qexistsl_tac [‘h::listpm string_pmact [(v,h)] vs1’,
                     ‘listpm string_pmact [(v,h)] vs2’, ‘tpm [(v,h)] N’] \\
       simp [listpm_APPENDlist] \\
       reverse CONJ_TAC
       >- (Know ‘LAMl (listpm string_pmact [(v,h)] vs2) t = tpm [(v,h)] (LAMl vs2 t')’
           >- (rw [Abbr ‘t'’, tpm_LAMl] \\
               rw [Once tpm_eqr, pmact_flip_args]) >> Rewr' \\
           rw [tpm_hreduce]) \\
       Know ‘LAMl (listpm string_pmact [(v,h)] vs1) (tpm [(v,h)] N) =
             tpm [(v,h)] (LAMl vs1 N)’ >- rw [tpm_LAMl] >> Rewr' \\
       simp [LAM_eq_thm, pmact_flip_args],
       (* goal 3 (of 4) *)
       Q.PAT_X_ASSUM ‘h = v’ (fs o wrap) \\
       Q.PAT_X_ASSUM ‘T’ K_TAC \\
       Q.PAT_X_ASSUM ‘!vs t. P’ (MP_TAC o (Q.SPECL [‘vs’, ‘t’])) \\
       Know ‘DISJOINT (set vs) (FV M)’
       >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) (FV M DELETE v)’ MP_TAC \\
           rw [DISJOINT_ALT'] >> METIS_TAC []) \\
       RW_TAC std_ss [] \\
       qexistsl_tac [‘v::vs1’, ‘vs2’, ‘N’] >> rw [],
       (* goal 4 (of 4) *)
       METIS_TAC [] ])
 (* v <> v' *)
 >> fs [tpm_eql, LAM_eq_thm] (* another 4 subgoals, even harder *)
 >| [ (* goal 1 (of 4) *)
      Q.PAT_X_ASSUM ‘h = v'’ (fs o wrap o SYM) \\
      Q.PAT_X_ASSUM ‘T’ K_TAC \\
      Q.PAT_X_ASSUM ‘LAMl vs t = M2’ (fs o wrap o SYM) \\
     ‘tpm [(v,h)] M1 -h-> tpm [(v,h)] (LAMl vs t)’ by rw [tpm_hreduce] \\
      FULL_SIMP_TAC std_ss [tpm_LAMl] \\
      qabbrev_tac ‘vs' = listpm string_pmact [(v,h)] vs’ \\
      qabbrev_tac ‘t' = tpm [(v,h)] t’ \\
     ‘ALL_DISTINCT vs'’ by rw [ALL_DISTINCT_listpm, Abbr ‘vs'’] \\
     ‘~is_abs t'’ by rw [Abbr ‘t'’, is_abs_cases] \\
      Know ‘DISJOINT (set vs') (FV (tpm [(v,h)] M1))’
      >- (rw [DISJOINT_ALT', FV_tpm, Abbr ‘vs'’, MEM_listpm] \\
          Cases_on ‘x = v’ >- rw [] \\
          Cases_on ‘x = h’ >- fs [] \\
          fs [] (* eliminate swapstr *) \\
          Q.PAT_X_ASSUM ‘DISJOINT (set vs) (FV (tpm [(v,h)] M1) DELETE v)’ MP_TAC \\
          rw [DISJOINT_ALT', MEM_listpm]) >> DISCH_TAC \\
      Q.PAT_X_ASSUM ‘!vs t. P’ (MP_TAC o (Q.SPECL [‘vs'’, ‘t'’])) \\
      RW_TAC std_ss [] \\
      fs [tpm_LAMl] \\
      Know ‘vs = listpm string_pmact [(v,h)] (vs1 ++ vs2)’
      >- (Q.PAT_X_ASSUM ‘_ = vs1 ++ vs2’ MP_TAC \\
          NTAC 2 (rw [Once LIST_EQ_REWRITE]) \\
          Know ‘EL x (vs1 ++ vs2) = swapstr h v (EL x vs)’
          >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
              FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr' \\
          simp []) >> Rewr' \\
      qexistsl_tac [‘h::listpm string_pmact [(v,h)] vs1’,
                    ‘listpm string_pmact [(v,h)] vs2’, ‘tpm [(v,h)] N’] \\
      simp [listpm_APPENDlist] \\
      reverse CONJ_TAC
      >- (Know ‘LAMl (listpm string_pmact [(v,h)] vs2) t = tpm [(v,h)] (LAMl vs2 t')’
          >- (rw [Abbr ‘t'’, tpm_LAMl] \\
              rw [Once tpm_eqr, pmact_flip_args]) >> Rewr' \\
          rw [tpm_hreduce]) \\
      Know ‘LAMl (listpm string_pmact [(v,h)] vs1) (tpm [(v,h)] N) =
            tpm [(v,h)] (LAMl vs1 N)’ >- rw [tpm_LAMl] \\
      DISCH_THEN (fs o wrap) \\
      simp [LAM_eq_thm, pmact_flip_args],
      (* goal 2 (of 4): this is the most difficult subgoal... *)
      fs [tpm_eqr, tpm_LAMl] \\
      qabbrev_tac ‘vs' = listpm string_pmact [(h,v')] vs’ \\
      qabbrev_tac ‘t' = tpm [(h,v')] t’ \\
      Q.PAT_X_ASSUM ‘LAMl vs' t' = M2’ (fs o wrap o SYM) \\
     ‘tpm [(v,v')] M1 -h-> tpm [(v,v')] (LAMl vs' t')’ by rw [tpm_hreduce] \\
      FULL_SIMP_TAC std_ss [tpm_LAMl] \\
      qabbrev_tac ‘vs'' = listpm string_pmact [(v,v')] vs'’ \\
      qabbrev_tac ‘t'' = tpm [(v,v')] t'’ \\
     ‘ALL_DISTINCT vs'’ by rw [ALL_DISTINCT_listpm, Abbr ‘vs'’] \\
     ‘ALL_DISTINCT vs''’ by rw [ALL_DISTINCT_listpm, Abbr ‘vs''’] \\
     ‘~is_abs t'’ by rw [Abbr ‘t'’, is_abs_cases] \\
     ‘~is_abs t''’ by rw [Abbr ‘t''’, is_abs_cases] \\
      Know ‘DISJOINT (set vs'') (FV (tpm [(v,v')] M1))’
      >- (rw [DISJOINT_ALT', FV_tpm, Abbr ‘vs''’, MEM_listpm] \\
          simp [Abbr ‘vs'’, MEM_listpm] \\
          Cases_on ‘x = v'’ >- fs [] \\
          Cases_on ‘x = v’ >> fs [] \\
          Cases_on ‘x = h’ >> fs [] \\
          Q.PAT_X_ASSUM ‘DISJOINT (set vs) (FV (tpm [(v,v')] M1) DELETE v)’ MP_TAC \\
          rw [DISJOINT_ALT', MEM_listpm]) >> DISCH_TAC \\
      Q.PAT_X_ASSUM ‘!vs t. P’ (MP_TAC o (Q.SPECL [‘vs''’, ‘t''’])) \\
      RW_TAC std_ss [] \\
      qabbrev_tac ‘vs'' = listpm string_pmact [(v,v')] vs'’ \\
      Know ‘vs = listpm string_pmact [(h,v')] vs'’
      >- (rw [Once LIST_EQ_REWRITE, Abbr ‘vs'’]) >> Rewr' \\
      Know ‘vs' = listpm string_pmact [(v,v')] vs''’
      >- (rw [Once LIST_EQ_REWRITE, Abbr ‘vs''’]) >> Rewr' \\
      Q.PAT_X_ASSUM ‘vs'' = vs1 ++ vs2’ (ONCE_REWRITE_TAC o wrap) \\
      qunabbrev_tac ‘vs''’ \\
      qexistsl_tac [‘h::listpm string_pmact [(h,v')] (listpm string_pmact [(v,v')] vs1)’,
                    ‘listpm string_pmact [(h,v')] (listpm string_pmact [(v,v')] vs2)’,
                    ‘tpm [(h,v')] (tpm [(v,v')] N)’] \\
      simp [listpm_APPENDlist] \\
      reverse CONJ_TAC
      >- (qabbrev_tac ‘vs2' = listpm string_pmact [(v,v')] vs2’ \\
          Know ‘LAMl (listpm string_pmact [(h,v')] vs2') t = tpm [(h,v')] (LAMl vs2' t')’
          >- (rw [Abbr ‘t'’, tpm_LAMl]) >> Rewr' \\
          rw [tpm_hreduce, Abbr ‘vs2'’] \\
          Know ‘LAMl (listpm string_pmact [(v,v')] vs2) t' = tpm [(v,v')] (LAMl vs2 t'')’
          >- (rw [Abbr ‘t''’, tpm_LAMl]) >> Rewr' \\
          rw [tpm_hreduce]) \\
      qabbrev_tac ‘vs1' = listpm string_pmact [(v,v')] vs1’ \\
      qabbrev_tac ‘N' = tpm [(v,v')] N’ \\
      Know ‘LAMl (listpm string_pmact [(h,v')] vs1') (tpm [(h,v')] N') =
            tpm [(h,v')] (LAMl vs1' N')’ >- rw [tpm_LAMl] >> Rewr' \\
      qunabbrevl_tac [‘vs1'’, ‘N'’] \\
      Know ‘LAMl (listpm string_pmact [(v,v')] vs1) (tpm [(v,v')] N) =
            tpm [(v,v')] (LAMl vs1 N)’ >- rw [tpm_LAMl] >> Rewr' \\
      Cases_on ‘h = v’ >> fs [] \\
      simp [LAM_eq_thm, pmact_flip_args] \\
      Q.PAT_X_ASSUM ‘tpm [(v,v')] M1 = LAMl vs1 N’ (REWRITE_TAC o wrap o SYM) \\
      rw [FV_tpm] \\
   (* applying fresh_tpm_subst *)
      simp [fresh_tpm_subst] \\
      qabbrev_tac ‘M = [VAR h/v'] M1’ \\
      Know ‘tpm [(h,v)] M = [VAR v/h] M’
      >- (rw [Once pmact_flip_args] \\
          MATCH_MP_TAC fresh_tpm_subst \\
          rw [FV_SUB, Abbr ‘M’]) >> Rewr' \\
      qunabbrev_tac ‘M’ \\
   (* applying lemma15a *)
      ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
      MATCH_MP_TAC lemma15a >> art [],
      (* goal 3 (of 4): conflicts of assumptions *)
      METIS_TAC [],
      (* goal 4 (of 4): cannot be harder than others *)
      Q.PAT_X_ASSUM ‘h = v’ (fs o wrap) \\
      Q.PAT_X_ASSUM ‘T’ K_TAC \\
      fs [tpm_eqr, tpm_LAMl] \\
      qabbrev_tac ‘vs' = listpm string_pmact [(v,v')] vs’ \\
      qabbrev_tac ‘t' = tpm [(v,v')] t’ \\
      Q.PAT_X_ASSUM ‘LAMl vs' t' = M2’ (fs o wrap o SYM) \\
     ‘tpm [(v,v')] M1 -h-> tpm [(v,v')] (LAMl vs' t')’ by rw [tpm_hreduce] \\
      FULL_SIMP_TAC std_ss [tpm_LAMl] \\
      Know ‘listpm string_pmact [(v,v')] vs' = vs’
      >- (rw [Once LIST_EQ_REWRITE, Abbr ‘vs'’]) >> DISCH_THEN (fs o wrap) \\
      Know ‘tpm [(v,v')] t' = t’
      >- (rw [Abbr ‘t'’]) >> DISCH_THEN (fs o wrap) \\
      Know ‘DISJOINT (set vs) (FV (tpm [(v,v')] M1))’
      >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) (FV (tpm [(v,v')] M1) DELETE v)’ MP_TAC \\
          rw [DISJOINT_ALT', FV_tpm] \\
          Cases_on ‘x = v’ >- fs [] \\
          Cases_on ‘x = v'’ >> fs []) >> DISCH_TAC \\
      Q.PAT_X_ASSUM ‘!vs t. P’ (MP_TAC o (Q.SPECL [‘vs’, ‘t’])) \\
      RW_TAC std_ss [] \\
      qexistsl_tac [‘v::vs1’, ‘vs2’, ‘N’] \\
      simp [listpm_APPENDlist] ]
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

Theorem wh_lam[simp] :
    ∀v M N. ¬(LAM v M -w-> N)
Proof
  ONCE_REWRITE_TAC [weak_head_cases] THEN SRW_TAC [][]
QED

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

val whY1 = store_thm(
  "whY1",
  ``chap2$Y @@ f -w-> Yf f``,
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

Theorem whnf_thm[simp] :
   whnf (VAR s) ∧
    (whnf (M @@ N) ⇔ ¬is_abs M ∧ whnf M) ∧
    whnf (LAM v M)
Proof
  REPEAT CONJ_TAC THEN SRW_TAC [][whnf_def, Once weak_head_cases] THEN
  EQ_TAC THEN SRW_TAC [][FORALL_AND_THM] THENL [
    Q.SPEC_THEN `M` FULL_STRUCT_CASES_TAC term_CASES THEN SRW_TAC [][] THEN
    METIS_TAC [],
    Q.SPEC_THEN `M` FULL_STRUCT_CASES_TAC term_CASES THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]
QED

val wh_weaken_cong = store_thm(
  "wh_weaken_cong",
  ``whnf N ⇒ M₁ -w->* M₂ ⇒ (M₁ -w->* N <=> M₂ -w->* N)``,
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

Theorem whstar_abs[simp] :
    LAM v M -w->* N ⇔ (N = LAM v M)
Proof
  SRW_TAC [][EQ_IMP_THM] THEN
  FULL_SIMP_TAC (srw_ss()) [Once relationTheory.RTC_CASES1,
                            Once weak_head_cases]
QED

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
  ``(p is_head_redex (LAM v t) <=> ?p0. (p = In::p0) /\ p0 is_head_redex t) /\
    (p is_head_redex (t @@ u) <=> (p = []) /\ is_abs t \/
                                ?p0. (p = Lt::p0) /\ is_comb t /\
                                          p0 is_head_redex t) /\
    (p is_head_redex (VAR v) <=> F)``,
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
  ``!t. hnf t <=> !p. ~(p is_head_redex t)``,
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
  ``!t v x p. p is_head_redex ([VAR v/x] t) <=> p is_head_redex t``,
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
  is_head_reduction s <=> okpath (labelled_redn beta) s /\
                        !i. i + 1 IN PL s ==>
                            nth_label i s is_head_redex el i s
End

Theorem is_head_reduction_thm[simp] :
    (is_head_reduction (stopped_at x) <=> T) /\
    (is_head_reduction (pcons x r p) <=>
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
  ``M -h-> N <=> (?r. r is_head_redex M /\ labelled_redn beta M r N)``,
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

Theorem lameq_has_hnf_cong :
    !M N. M == N ==> (has_hnf M <=> has_hnf N)
Proof
    rpt STRIP_TAC
 >> EQ_TAC >> rw [has_hnf_def]
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC ‘N'’ >> art [] \\
      Q_TAC (TRANS_TAC lameq_TRANS) ‘M’ >> art [] \\
      simp [Once lameq_SYM],
      (* goal 1 (of 2) *)
      Q.EXISTS_TAC ‘N'’ >> art [] \\
      Q_TAC (TRANS_TAC lameq_TRANS) ‘N’ >> art [] ]
QED

Theorem hreduces_has_hnf_cong :
    !M N. M -h->* N ==> (has_hnf M <=> has_hnf N)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC lameq_has_hnf_cong
 >> MATCH_MP_TAC hreduces_lameq >> art []
QED

Theorem hreduce1_has_hnf_cong :
    !M N. M -h-> N ==> (has_hnf M <=> has_hnf N)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC hreduces_has_hnf_cong
 >> MATCH_MP_TAC RTC_SINGLE >> art []
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
  ``(head_reduct M = SOME N) <=> M -h-> N``,
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
 >> ‘nth_label i p = g i’ by rw [Abbr ‘p’, nth_label_pgenerate]
 >> ‘!i. el i p = f i’    by rw [Abbr ‘p’, el_pgenerate]
 >> ASM_REWRITE_TAC [GSYM ADD1]
 >> Q.EXISTS_TAC ‘SUC i’ >> REWRITE_TAC []
QED

(* This theorem guarentees the one-one mapping between the list and the path *)
Theorem finite_head_reduction_path_to_list_11 :
    !M p. (p = head_reduction_path M) /\ finite p ==>
          ?l. l <> [] /\ (HD l = M) /\ hnf (LAST l) /\
             (LENGTH l = THE (length p)) /\
             (!i. i < LENGTH l ==> (EL i l = el i (head_reduction_path M))) /\
              !i. SUC i < LENGTH l ==> EL i l -h-> EL (SUC i) l
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘p = head_reduction_path M’
 >> ‘?n. length p = SOME n’ by METIS_TAC [finite_length]
 >> Cases_on ‘n’ >- fs [length_never_zero]
 >> rename1 ‘length p = SOME (SUC n)’
 >> Q.EXISTS_TAC ‘GENLIST (\i. el i p) (SUC n)’ >> simp []
 >> STRONG_CONJ_TAC >- rw [NOT_NIL_EQ_LENGTH_NOT_0] >> DISCH_TAC
 >> CONJ_TAC >- rw [GSYM EL, Abbr ‘p’, head_reduction_path_def]
 >> CONJ_TAC (* hnf *)
 >- (qabbrev_tac ‘l = GENLIST (\i. el i p) (SUC n)’ \\
     rw [Abbr ‘l’, LAST_EL] \\
     Suff ‘el n p = last p’ >- rw [Abbr ‘p’, head_reduction_path_def] \\
     rw [finite_last_el])
 >> rw [head_reduce1_def]
 >> ‘i IN PL p /\ i + 1 IN PL p’ by rw [PL_def]
 >> qabbrev_tac ‘q = drop i p’
 >> ‘el i p = first q’ by rw [Abbr ‘q’] >> POP_ORW
 >> Know ‘el i (tail p) = first (tail q)’
 >- (rw [Abbr ‘q’, REWRITE_RULE [ADD1] el_def])
 >> Rewr'
 >> Know ‘is_head_reduction q’
 >- (qunabbrev_tac ‘q’ \\
     irule finite_is_head_reduction_drop \\
     rw [Abbr ‘p’, head_reduction_path_def])
 >> DISCH_TAC
 (* perform case analysis *)
 >> ‘(?x. q = stopped_at x) \/ ?x r xs. q = pcons x r xs’ by METIS_TAC [path_cases]
 >- (Know ‘PL q = IMAGE (\n. n - i) (PL p)’
     >- rw [Abbr ‘q’, PL_drop] \\
    ‘PL p = count (SUC n)’ by rw [PL_def, count_def] >> POP_ORW \\
     POP_ORW (* q = stopped_at x *) \\
     simp [PL_stopped_at] \\
     Suff ‘IMAGE (\n. n - i) (count (SUC n)) <> {0}’ >- METIS_TAC [] \\
     rw [Once EXTENSION] \\
     Q.EXISTS_TAC ‘n - i’ >> rw [] \\
     Q.EXISTS_TAC ‘n’ >> rw [])
 >> fs [is_head_reduction_thm]
 >> Q.EXISTS_TAC ‘r’ >> art []
QED

Theorem finite_head_reduction_path_to_list :
    !M. finite (head_reduction_path M) <=>
        ?l. l <> [] /\ (HD l = M) /\ hnf (LAST l) /\
            !i. SUC i < LENGTH l ==> EL i l -h-> EL (SUC i) l
Proof
    Q.X_GEN_TAC ‘M’
 >> qabbrev_tac ‘p = head_reduction_path M’
 >> EQ_TAC >> rpt STRIP_TAC
 >- (MP_TAC (Q.SPECL [‘M’, ‘p’] finite_head_reduction_path_to_list_11) \\
     rw [] >> Q.EXISTS_TAC ‘l’ >> rw [])
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

(* hnf_children retrives the ‘args’ part of absfree hnf *)
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

Theorem hnf_children_hnf[simp] :
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

Theorem hnf_children_FV_SUBSET :
    !M Ms. hnf M /\ ~is_abs M /\ (Ms = hnf_children M) ==>
           !i. i < LENGTH Ms ==> FV (EL i Ms) SUBSET FV M
Proof
    rpt STRIP_TAC
 >> ‘M = hnf_head M @* hnf_children M’ by PROVE_TAC [absfree_hnf_thm]
 >> POP_ORW
 >> Q.PAT_X_ASSUM ‘Ms = hnf_children M’ (fs o wrap)
 >> qabbrev_tac ‘Ms = hnf_children M’
 >> simp [FV_appstar]
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘BIGUNION (IMAGE FV (set Ms))’
 >> simp []
 >> rw [SUBSET_DEF, IN_BIGUNION_IMAGE]
 >> Q.EXISTS_TAC ‘EL i Ms’ >> rw [EL_MEM]
QED

Theorem absfree_hnf_head :
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

Theorem hnf_children_tpm :
    !pi M. hnf M ==> (hnf_children (tpm pi M) = MAP (tpm pi) (hnf_children M))
Proof
    rpt STRIP_TAC
 >> Cases_on ‘~is_comb M’
 >- (‘is_var M \/ is_abs M’ by METIS_TAC [term_cases]
     >- (‘?y. M = VAR y’ by METIS_TAC [is_var_cases] \\
         NTAC 2 (rw [Once hnf_children_def])) \\
    ‘?v t. M = LAM v t’ by METIS_TAC [is_abs_cases] \\
     NTAC 2 (rw [Once hnf_children_def]))
 >> fs []
 >> ‘?t args. (M = t @* args) /\ args <> [] /\ ~is_comb t’
      by METIS_TAC [is_comb_appstar_exists]
 >> rw [tpm_appstar]
 >> Know ‘~is_abs t’
 >- (CCONTR_TAC >> fs [hnf_appstar])
 >> DISCH_TAC
 >> ‘is_var t’ by METIS_TAC [term_cases]
 >> ‘?y. t = VAR y’ by METIS_TAC [is_var_cases]
 >> rw [hnf_children_hnf]
 >> rw [LIST_EQ_REWRITE, EL_MAP]
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

Theorem LAMl_size_eq_0 :
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
 >- rw [LAMl_size_eq_0]
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

Theorem LAMl_size_appstar[simp] :
    LAMl_size (VAR y @* args) = 0
Proof
    Cases_on ‘args = []’ >- rw []
 >> ‘?x l. args = SNOC x l’ by METIS_TAC [SNOC_CASES]
 >> rw [appstar_SNOC]
QED

Theorem LAMl_size_tpm[simp] :
    !M. LAMl_size (tpm pi M) = LAMl_size M
Proof
    HO_MATCH_MP_TAC simple_induction >> rw []
QED

(*---------------------------------------------------------------------------*
 *  hnf_children_size (of hnf)
 *---------------------------------------------------------------------------*)

val (hnf_children_size_thm, _) = define_recursive_term_function
   ‘(hnf_children_size ((VAR :string -> term) s) = 0) /\
    (hnf_children_size (t1 @@ t2) = 1 + hnf_children_size t1) /\
    (hnf_children_size (LAM v t) = hnf_children_size t)’;

val _ = export_rewrites ["hnf_children_size_thm"];

Theorem hnf_children_size_LAMl[simp] :
    hnf_children_size (LAMl vs t) = hnf_children_size t
Proof
    Induct_on ‘vs’ >> rw []
QED

Theorem hnf_children_size_appstar[simp] :
    hnf_children_size (VAR y @* Ms) = LENGTH Ms
Proof
    Induct_on ‘Ms’ using SNOC_INDUCT >- rw []
 >> rw [appstar_SNOC]
QED

Theorem hnf_children_size_tpm[simp] :
    !M. hnf_children_size (tpm pi M) = hnf_children_size M
Proof
    HO_MATCH_MP_TAC simple_induction >> rw []
QED

Theorem hnf_children_size_hnf :
    !M. hnf M /\ ~is_abs M ==> hnf_children_size M = LENGTH (hnf_children M)
Proof
    rw [absfree_hnf_cases] >> rw []
QED

(*---------------------------------------------------------------------------*
 *  hnf_cases_shared - ‘hnf_cases’ with a given list of fresh variables
 *---------------------------------------------------------------------------*)

(* NOTE: "irule (iffLR hnf_cases_shared)" is a useful tactic *)
Theorem hnf_cases_shared :
    !vs M. ALL_DISTINCT vs /\ LAMl_size M <= LENGTH vs /\
           DISJOINT (set vs) (FV M) ==>
          (hnf M <=> ?y args. M = LAMl (TAKE (LAMl_size M) vs) (VAR y @* args))
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
 >> ‘is_abs M’ by METIS_TAC [LAMl_size_eq_0]
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

(*---------------------------------------------------------------------------*
 *  hreduce, LAMl and appstar
 *---------------------------------------------------------------------------*)

Theorem hreduce_LAMl_appstar_lemma[local] :
    !pi t args.
          ALL_DISTINCT (MAP FST pi) /\
          EVERY (\e. DISJOINT (FV e) (set (MAP FST pi))) (MAP SND pi) ==>
          LAMl (MAP FST pi) t @* MAP SND pi @* args -h->*
          (FEMPTY |++ pi) ' t @* args
Proof
    Induct_on ‘pi’
 >> rw [FUPDATE_LIST_THM] (* only one goal left *)
 >> Know ‘EVERY (\e. DISJOINT (FV e) (set (MAP FST pi))) (MAP SND pi)’
 >- (POP_ASSUM MP_TAC \\
     rw [EVERY_MEM, MEM_MAP])
 >> DISCH_THEN (fs o wrap)
 >> qabbrev_tac ‘vs = MAP FST pi’
 >> qabbrev_tac ‘Ns = MAP SND pi’
 >> qabbrev_tac ‘v = FST h’
 >> qabbrev_tac ‘N = SND h’
 >> ‘h = (v,N)’ by rw [Abbr ‘v’, Abbr ‘N’] >> POP_ORW
 (* stage work *)
 >> simp [Once RTC_CASES1]
 >> DISJ2_TAC
 (* preparing for hreduce1_appstar *)
 >> Q.EXISTS_TAC ‘[N/v] (LAMl vs t) @* Ns @* args’
 >> CONJ_TAC
 >- (REWRITE_TAC [GSYM appstar_APPEND] \\
     MATCH_MP_TAC hreduce1_appstar >> simp [] \\
     rw [Once hreduce1_cases] \\
     qexistsl_tac [‘v’, ‘LAMl vs t’] >> rw [])
 >> Know ‘FEMPTY |+ (v,N) |++ pi = (FEMPTY |++ pi) |+ (v,N)’
 >- (MATCH_MP_TAC FUPDATE_FUPDATE_LIST_COMMUTES >> rw [])
 >> Rewr'
 (* applying FUPDATE_FUPDATE_LIST_COMMUTES *)
 >> qabbrev_tac ‘fm = FEMPTY |++ pi’
 >> ‘FDOM fm = set vs’ by rw [Abbr ‘fm’, FDOM_FUPDATE_LIST]
 >> Know ‘[N/v] (LAMl vs t) = LAMl vs ([N/v] t)’
 >- (MATCH_MP_TAC LAMl_SUB >> rw [Once DISJOINT_SYM])
 >> Rewr'
 >> Suff ‘(fm |+ (v,N)) ' t = fm ' ([N/v] t)’ >- rw []
 >> MATCH_MP_TAC ssub_update_apply_SUBST
 >> rw [Once DISJOINT_SYM]
 (* applying FUPDATE_LIST_APPLY_MEM *)
 >> fs [MEM_EL, Abbr ‘fm’]
 >> ‘LENGTH vs = LENGTH pi /\ LENGTH Ns = LENGTH pi’ by rw [Abbr ‘vs’, Abbr ‘Ns’]
 >> Know ‘(FEMPTY |++ pi) ' (EL n vs) = EL n Ns’
 >- (MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM \\
     Q.EXISTS_TAC ‘n’ >> rw [] \\
     CCONTR_TAC >> fs [] \\
    ‘n < LENGTH vs /\ m <> n’ by RW_TAC arith_ss [] \\
     METIS_TAC [ALL_DISTINCT_EL_IMP])
 >> Rewr'
 >> Q.PAT_X_ASSUM ‘EVERY P Ns’ MP_TAC
 >> rw [EVERY_EL]
QED

Theorem hreduce_LAMl_appstar :
    !vs Ns t. ALL_DISTINCT vs /\ LENGTH vs = LENGTH Ns /\
              EVERY (\e. DISJOINT (FV e) (set vs)) Ns
          ==> LAMl vs t @* Ns -h->* fromPairs vs Ns ' t
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘n = LENGTH vs’
 >> qabbrev_tac ‘pi = ZIP (vs,Ns)’
 >> ‘vs = MAP FST pi’ by rw [Abbr ‘pi’, MAP_ZIP]
 >> ‘Ns = MAP SND pi’ by rw [Abbr ‘pi’, MAP_ZIP]
 >> simp [fromPairs_def]
 >> MP_TAC (Q.SPECL [‘pi’, ‘t’, ‘[]’] hreduce_LAMl_appstar_lemma)
 >> rw []
QED

(* NOTE: there's no requirements on ‘args’, which can be empty *)
Theorem hreduce_LAMl_appstar_ext :
    !vs Ns t args.
             ALL_DISTINCT vs /\ LENGTH vs = LENGTH Ns /\
             EVERY (\e. DISJOINT (FV e) (set vs)) Ns
         ==> LAMl vs t @* Ns @* args -h->* fromPairs vs Ns ' t @* args
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘n = LENGTH vs’
 >> qabbrev_tac ‘pi = ZIP (vs,Ns)’
 >> ‘vs = MAP FST pi’ by rw [Abbr ‘pi’, MAP_ZIP]
 >> ‘Ns = MAP SND pi’ by rw [Abbr ‘pi’, MAP_ZIP]
 >> simp [fromPairs_def]
 >> MATCH_MP_TAC hreduce_LAMl_appstar_lemma
 >> rw []
QED

(* This is copied from boehmScript.sml *)
fun RNEWS_TAC (vs, r, n) X :tactic =
    qabbrev_tac ‘^vs = RNEWS ^r ^n ^X’
 >> Know ‘ALL_DISTINCT ^vs /\ DISJOINT (set ^vs) ^X /\ LENGTH ^vs = ^n’
 >- rw [RNEWS_def, Abbr ‘^vs’]
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [DISJOINT_UNION']));

fun NEWS_TAC (vs, n) = RNEWS_TAC (vs, numSyntax.zero_tm, n);

(* NOTE: A problem of (the next) hreduce_permutator_thm is that, the names
   xs and y asserted, do not have a rank-based allocation. As the result,
   two applications of the theorem on two different terms, say, Ns and Ns',
   even they have the same length, do not result in two identical xs/y.

   The present theorem resolved this issue, by using a pre-allocated list
   of names for building xs and y, such that ‘xs ++ [y]’ is the prefix of
   the given list, render them comparable among different applications.

   NOTE: Using [permutator_alt] is a MUST in this proof, for eliminating
   the ugly antecedent ‘DISJOINT (set L) (set (GENLIST n2s (SUC n)))’, which
   comes from [permutator_def].

   NOTE: Usage of input and self-allocated names:

   permutator n @* Ns -h->* LAMl xs (LAM y (VAR y @* Ns @* MAP VAR xs))

                       |<-------------- L ----------------->|
         (NEWS)        |     (user provided, LENGTH L > n)  |
   |<----- vs1 ------->+<------ vs2 (xs) ---->|y|
   |  k = LENGTH Ns    |        n - k         | |
   |<----------------- Y -------------------->|y|
   |<----------------- Z -------------------->|z| (permutator_alt)
 *)
Theorem hreduce_permutator_shared :
    !Ns n L. LENGTH Ns <= n /\ n < LENGTH L /\ ALL_DISTINCT L /\
             DISJOINT (set L) (BIGUNION (IMAGE FV (set Ns))) ==>
             ?xs y. permutator n @* Ns -h->*
                    LAMl xs (LAM y (VAR y @* Ns @* MAP VAR xs)) /\
                    LENGTH xs = n - LENGTH Ns /\ SNOC y xs <<= L
Proof
    rpt STRIP_TAC
 (* allocate vs1 in parallel with L *)
 >> qabbrev_tac ‘X = set L UNION (BIGUNION (IMAGE FV (set Ns)))’
 >> ‘FINITE X’ by (rw [Abbr ‘X’] >> rw [])
 >> qabbrev_tac ‘k = LENGTH Ns’
 >> Q_TAC (NEWS_TAC (“vs1 :string list”, “k :num”)) ‘X’
 (* applying permutator_alt, asserting z and Z *)
 >> MP_TAC (Q.SPECL [‘X UNION set vs1’, ‘n’] permutator_alt) >> simp []
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘Z’ (Q.X_CHOOSE_THEN ‘z’ STRIP_ASSUME_TAC))
 >> Q.PAT_X_ASSUM ‘FINITE X’ K_TAC
 >> FULL_SIMP_TAC list_ss [ALL_DISTINCT_SNOC, DISJOINT_UNION, DISJOINT_UNION',
                           Abbr ‘X’]
 (* stage work *)
 >> qabbrev_tac ‘M = VAR z @* MAP VAR Z’
 (* preparing for LAMl_ALPHA_ssub *)
 >> qabbrev_tac ‘Y = vs1 ++ TAKE (n - k) L’
 >> qabbrev_tac ‘y = EL (n - k) L’
 >> ‘LENGTH Y = n’ by rw [Abbr ‘Y’]
 >> Know ‘ALL_DISTINCT Y’
 >- (simp [Abbr ‘Y’, ALL_DISTINCT_APPEND] \\
     CONJ_TAC >- (MATCH_MP_TAC ALL_DISTINCT_TAKE >> art []) \\
     Suff ‘DISJOINT (set vs1) (set (TAKE (n - k) L))’ >- rw [DISJOINT_ALT] \\
     MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘set L’ >> art [] \\
     rw [LIST_TO_SET_TAKE])
 >> DISCH_TAC
 >> Know ‘~MEM y Y’
 >- (simp [Abbr ‘Y’, MEM_APPEND] \\
     CONJ_TAC
     >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs1) (set L)’ MP_TAC \\
         simp [DISJOINT_ALT'] \\
         DISCH_THEN MATCH_MP_TAC \\
         simp [EL_MEM, Abbr ‘y’]) \\
     qabbrev_tac ‘i = n - k’ \\
     Know ‘ALL_DISTINCT (TAKE i L ++ DROP i L)’ >- simp [TAKE_DROP] \\
     simp [ALL_DISTINCT_APPEND] >> STRIP_TAC \\
     Suff ‘MEM y (DROP i L)’ >- PROVE_TAC [] \\
     simp [Abbr ‘y’, Abbr ‘i’, MEM_DROP] \\
     Q.EXISTS_TAC ‘0’ >> simp [])
 >> DISCH_TAC
 >> qabbrev_tac ‘Y' = SNOC y Y’
 >> qabbrev_tac ‘Z' = SNOC z Z’
 (* NOTE: We need to prove ‘DISJOINT (set Y') (set Z')’, and the idea is to
    prove the two parts (‘vs1’ and the prefix of L) are disjoint with Z',
    separately. For this purpose, it's better to consider put y and Y together
    and prove that Y' is vs1 appended with a prefix of L.
  *)
 >> qabbrev_tac ‘k' = n - k’ (* as the complementation of k *)
 >> Know ‘vs1 ++ TAKE (SUC k') L = Y'’
 >- (simp [Abbr ‘Y'’, Abbr ‘Y’, Abbr ‘y’, TAKE_SUC] \\
     simp [TAKE1, HD_DROP, Abbr ‘k'’])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set Y') (set Z')’
 >- (POP_ASSUM (REWRITE_TAC o wrap o SYM) \\
     simp [DISJOINT_UNION] \\
     MATCH_MP_TAC DISJOINT_SUBSET' \\
     Q.EXISTS_TAC ‘set L’ >> simp [LIST_TO_SET_TAKE])
 >> DISCH_TAC
 (* stage work *)
 >> Know ‘DISJOINT (set Y') (BIGUNION (IMAGE FV (set Ns)))’
 >- (Q.PAT_X_ASSUM ‘_ = Y'’ (REWRITE_TAC o wrap o SYM) \\
     ASM_SIMP_TAC list_ss [DISJOINT_UNION] \\
     MATCH_MP_TAC DISJOINT_SUBSET' \\
     Q.EXISTS_TAC ‘set L’ \\
     ASM_SIMP_TAC list_ss [Abbr ‘Y’, LIST_TO_SET_TAKE])
 >> DISCH_TAC
 >> ASM_SIMP_TAC std_ss [GSYM LAMl_SNOC]
 >> ‘MEM z Z'’ by rw [Abbr ‘Z'’]
 >> ‘LENGTH Z' = SUC (LENGTH Z)’ by rw [Abbr ‘Z'’]
 >> ‘ALL_DISTINCT Z'’ by rw [Abbr ‘Z'’, ALL_DISTINCT_SNOC]
 >> ‘LENGTH Y' = SUC (LENGTH Y)’ by rw [Abbr ‘Y'’]
 >> ‘ALL_DISTINCT Y'’ by rw [Abbr ‘Y'’, ALL_DISTINCT_SNOC]
 (* applying LAMl_ALPHA_ssub, ‘Y = SNOC y xs’ will be there *)
 >> Know ‘LAMl Z' M = LAMl Y' ((FEMPTY |++ ZIP (Z',MAP VAR Y')) ' M)’
 >- (MATCH_MP_TAC LAMl_ALPHA_ssub >> art [] \\
     simp [DISJOINT_UNION'] \\
     Suff ‘FV M = set Z'’ >- simp [] \\
     rw [Abbr ‘M’, Abbr ‘Z'’, FV_appstar] \\
     simp [LIST_TO_SET_SNOC] >> SET_TAC [])
 >> Rewr'
 >> ‘Y' <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> REWRITE_TAC [GSYM fromPairs_def]
 >> qabbrev_tac ‘fm = fromPairs Z' (MAP VAR Y')’
 >> ‘FDOM fm = set Z'’ by rw [FDOM_fromPairs, Abbr ‘fm’]
 >> qunabbrev_tac ‘Y'’
 >> REWRITE_TAC [LAMl_SNOC]
 >> Know ‘fm ' M = VAR y @* MAP VAR Y’
 >- (simp [Abbr ‘M’, ssub_appstar] \\
     Know ‘fm ' z = VAR y’
     >- (‘z = EL n Z'’ by simp [Abbr ‘Z'’, EL_APPEND2] >> POP_ORW \\
         simp [Abbr ‘fm’, LAST_EL] \\
         qabbrev_tac ‘Y' = SNOC y Y’ \\
         Know ‘fromPairs Z' (MAP VAR Y') ' (EL n Z') = EL n (MAP VAR Y')’
         >- (MATCH_MP_TAC fromPairs_FAPPLY_EL >> rw []) >> Rewr' \\
         ASM_SIMP_TAC std_ss [EL_MAP, Abbr ‘Y'’] \\
         Suff ‘EL n (SNOC y Y) = y’ >- rw [] \\
        ‘n = LENGTH Y’ by rw [] >> POP_ORW \\
         REWRITE_TAC [EL_LENGTH_SNOC]) >> Rewr' \\
     Suff ‘MAP ($' fm) (MAP VAR Z) = MAP VAR Y’ >- rw [] \\
     simp [LIST_EQ_REWRITE, LENGTH_FRONT] \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     simp [EL_MAP] \\
    ‘MEM (EL i Z) Z'’ by rw [EL_MEM, Abbr ‘Z'’] \\
     rw [Abbr ‘fm’] \\
     Know ‘EL i Z = EL i Z'’
     >- (simp [Abbr ‘Z'’, EL_APPEND1]) >> Rewr' \\
     qabbrev_tac ‘Y' = SNOC y Y’ \\
     Know ‘EL i Y = EL i Y'’
     >- (SIMP_TAC std_ss [Once EQ_SYM_EQ, Abbr ‘Y'’] \\
         MATCH_MP_TAC EL_SNOC >> art []) >> Rewr' \\
     Know ‘fromPairs Z' (MAP VAR Y') ' (EL i Z') = EL i (MAP VAR Y')’
     >- (MATCH_MP_TAC fromPairs_FAPPLY_EL >> rw []) >> Rewr' \\
     rw [EL_MAP])
 >> Rewr'
 (* stage work *)
 >> qabbrev_tac ‘t = LAM y (VAR y @* MAP VAR Y)’
 (* now break Y into two parts, the first part will match Ns's length *)
 >> qabbrev_tac ‘vs2 = TAKE k' L’
 >> qunabbrev_tac ‘Y’
 >> REWRITE_TAC [LAMl_APPEND]
 >> qabbrev_tac ‘t1 = LAMl vs2 t’
 (* applying hreduce_LAMl_appstar *)
 >> Know ‘LAMl vs1 t1 @* Ns -h->* (FEMPTY |++ ZIP (vs1,Ns)) ' t1’
 >- (MATCH_MP_TAC (REWRITE_RULE [fromPairs_def] hreduce_LAMl_appstar) \\
     simp [] \\
     simp [EVERY_MEM, DISJOINT_ALT] \\
     NTAC 4 STRIP_TAC (* ~MEM x vs1 *) \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs1) (BIGUNION (IMAGE FV (set Ns)))’
       (MP_TAC o REWRITE_RULE [DISJOINT_ALT']) \\
     simp [DISJOINT_ALT] \\
     DISCH_THEN MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘FV e’ >> art [] \\
     Q.EXISTS_TAC ‘e’ >> art [])
 (* stage work *)
 >> simp [GSYM fromPairs_def, Abbr ‘t1’]
 >> ‘FDOM (fromPairs vs1 Ns) = set vs1’
       by rw [Abbr ‘vs1’, Abbr ‘k’, FDOM_fromPairs]
 (* applying LAMl_ssub to move ‘LAMl vs2’ out *)
 >> Know ‘fromPairs vs1 Ns ' (LAMl vs2 t) = LAMl vs2 (fromPairs vs1 Ns ' t)’
 >- (MATCH_MP_TAC LAMl_ssub >> simp [] \\
     CONJ_TAC
     >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT (vs1 ++ vs2)’ MP_TAC \\
         rw [ALL_DISTINCT_APPEND, DISJOINT_ALT]) \\
     Q.X_GEN_TAC ‘v’ >> simp [MEM_EL] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘i’ STRIP_ASSUME_TAC) >> POP_ORW \\
     Know ‘fromPairs vs1 Ns ' (EL i vs1) = EL i Ns’
     >- (MATCH_MP_TAC fromPairs_FAPPLY_EL >> simp []) >> Rewr' \\
     MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘set L’ \\
     reverse CONJ_TAC >- rw [Abbr ‘vs2’, LIST_TO_SET_TAKE] \\
     MATCH_MP_TAC DISJOINT_SUBSET' \\
     Q.EXISTS_TAC ‘BIGUNION (IMAGE FV (set Ns))’ \\
     ASM_SIMP_TAC std_ss [Once DISJOINT_SYM] \\
     rw [SUBSET_DEF] \\
     Q.EXISTS_TAC ‘FV (EL i Ns)’ >> art [] \\
     Q.EXISTS_TAC ‘EL i Ns’ >> art [] \\
     simp [EL_MEM])
 >> Rewr'
 (* stage work *)
 >> qabbrev_tac ‘Y = vs1 ++ vs2’
 >> qunabbrev_tac ‘t’
 >> qabbrev_tac ‘t = VAR y @* MAP VAR Y’
 (* applying ssub_LAM to move ‘LAM y’ out of ssub *)
 >> Know ‘fromPairs vs1 Ns ' (LAM y t) = LAM y (fromPairs vs1 Ns ' t)’
 >- (MATCH_MP_TAC ssub_LAM >> simp [] \\
     CONJ_TAC
     >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs1) (set L)’ MP_TAC \\
         rw [DISJOINT_ALT'] \\
         POP_ASSUM MATCH_MP_TAC \\
         simp [EL_MEM, Abbr ‘y’, Abbr ‘k'’]) \\
     Q.X_GEN_TAC ‘v’ >> simp [MEM_EL] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘i’ STRIP_ASSUME_TAC) >> POP_ORW \\
     Know ‘fromPairs vs1 Ns ' (EL i vs1) = EL i Ns’
     >- (MATCH_MP_TAC fromPairs_FAPPLY_EL >> simp []) >> Rewr' \\
     Q.PAT_X_ASSUM ‘DISJOINT (set L) (BIGUNION (IMAGE FV (set Ns)))’ MP_TAC \\
     rw [DISJOINT_ALT] \\
     POP_ASSUM irule \\
     reverse CONJ_TAC >- rw [Abbr ‘y’, Abbr ‘k'’, EL_MEM] \\
     Q.EXISTS_TAC ‘EL i Ns’ >> simp [EL_MEM])
 >> Rewr'
 >> Know ‘~MEM y vs1’
 >- (Q.PAT_X_ASSUM ‘~MEM y Y’ MP_TAC \\
     simp [Abbr ‘Y’, MEM_APPEND])
 >> DISCH_TAC
 >> simp [Abbr ‘t’, ssub_appstar, Abbr ‘Y’]
 (* stage work *)
 >> Know ‘MAP ($' (fromPairs vs1 Ns)) (MAP VAR vs1) = Ns’
 >- (rw [LIST_EQ_REWRITE] \\
     rename1 ‘i < LENGTH vs1’ \\
     simp [EL_MAP] \\
    ‘MEM (EL i vs1) vs1’ by rw [EL_MEM] >> simp [] \\
     MATCH_MP_TAC fromPairs_FAPPLY_EL >> rw [])
 >> Rewr'
 >> Know ‘MAP ($' (fromPairs vs1 Ns)) (MAP VAR vs2) = MAP VAR vs2’
 >- (rw [LIST_EQ_REWRITE] \\
     rename1 ‘i < LENGTH vs2’ \\
     rw [EL_MAP, MEM_EL] \\
  (* NOTE: below we show conflicts in assumptions *)
     Q.PAT_X_ASSUM ‘ALL_DISTINCT (vs1 ++ vs2)’ MP_TAC \\
     rw [ALL_DISTINCT_APPEND, DISJOINT_ALT] \\
     METIS_TAC [MEM_EL])
 >> Rewr'
 (* final stage *)
 >> REWRITE_TAC [appstar_APPEND]
 >> DISCH_TAC
 >> qexistsl_tac [‘vs2’, ‘y’] >> art []
 (* extra goal: LENGTH vs2 = n - k *)
 >> CONJ_TAC >- rw [Abbr ‘vs2’, LENGTH_TAKE, Abbr ‘k'’]
 >> simp [IS_PREFIX_EQ_TAKE']
 >> Q.EXISTS_TAC ‘SUC k'’
 >> simp [Abbr ‘vs2’, TAKE_SUC]
 >> ‘DROP k' L <> []’ by rw [Abbr ‘k'’]
 >> simp [Abbr ‘y’, TAKE1, Once EQ_SYM_EQ]
 >> MATCH_MP_TAC HD_DROP
 >> simp [Abbr ‘k'’]
QED

(* NOTE: ‘permutator n’ contains n + 1 binding variables. Appending at most n
   arbitrary terms, each head reduction step consumes just one of them,
   eventually there should be one more fresh variable left, forming a hnf.

   NOTE2: added one global excluded list X and more disjointness conclusions.
   NOTE3: added ‘LENGTH xs = n - LENGTH Ns’ for the potential needs.
 *)
Theorem hreduce_permutator_thm :
    !X n Ns. FINITE X /\ LENGTH Ns <= n ==>
             ?xs y. permutator n @* Ns -h->*
                      LAMl xs (LAM y (VAR y @* Ns @* MAP VAR xs)) /\
                    LENGTH xs = n - LENGTH Ns /\
                    ALL_DISTINCT (SNOC y xs) /\
                    DISJOINT X (set (SNOC y xs)) /\
                    !N. MEM N Ns ==> DISJOINT (FV N) (set (SNOC y xs))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> qabbrev_tac ‘Y = GENLIST n2s (SUC n)’
 >> qabbrev_tac ‘Z = X UNION set Y UNION (BIGUNION (IMAGE FV (set Ns)))’
 >> Know ‘FINITE Z’
 >- (rw [Abbr ‘Z’] >> rw [])
 >> DISCH_TAC
 >> Q_TAC (NEWS_TAC (“L :string list”, “SUC n”)) ‘Z’
 >> FULL_SIMP_TAC std_ss [Abbr ‘Z’, DISJOINT_UNION']
 (* applying hreduce_permutator_shared *)
 >> MP_TAC (Q.SPECL [‘Ns’, ‘n’, ‘L’] hreduce_permutator_shared) >> rw []
 >> qexistsl_tac [‘xs’, ‘y’] >> simp []
 >> CONJ_TAC
 >- (MATCH_MP_TAC IS_PREFIX_ALL_DISTINCT \\
     Q.EXISTS_TAC ‘L’ >> art [])
 >> CONJ_TAC
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘set L’ >> rw [Once DISJOINT_SYM] \\
     FULL_SIMP_TAC std_ss [IS_PREFIX_EQ_TAKE', LIST_TO_SET_TAKE])
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC DISJOINT_SUBSET
 >> Q.EXISTS_TAC ‘set L’
 >> reverse CONJ_TAC
 >- FULL_SIMP_TAC std_ss [IS_PREFIX_EQ_TAKE', LIST_TO_SET_TAKE]
 >> ONCE_REWRITE_TAC [DISJOINT_SYM]
 >> MATCH_MP_TAC DISJOINT_SUBSET
 >> Q.EXISTS_TAC ‘BIGUNION (IMAGE FV (set Ns))’ >> art []
 >> rw [SUBSET_DEF]
 >> Q.EXISTS_TAC ‘FV N’ >> art []
 >> Q.EXISTS_TAC ‘N’ >> art []
QED

Theorem permutator_hreduce_lemma[local] :
    ALL_DISTINCT vs /\ ~MEM y vs /\ LENGTH vs = LENGTH Ns /\
    EVERY (\e. DISJOINT (FV e) (set (SNOC y vs))) (SNOC N Ns) ==>
    LAMl vs (LAM y (VAR y @* MAP VAR vs)) @* Ns @@ N @* args -h->*
    N @* Ns @* args
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [GSYM LAMl_SNOC, GSYM appstar_SNOC]
 >> qabbrev_tac ‘vs' = SNOC y vs’
 >> qabbrev_tac ‘Ns' = SNOC N Ns’
 >> qabbrev_tac ‘t = VAR y @* MAP VAR vs’
 >> Suff ‘N @* Ns = fromPairs vs' Ns' ' t’
 >- (Rewr' \\
     MATCH_MP_TAC hreduce_LAMl_appstar_ext \\
     rw [Abbr ‘vs'’, Abbr ‘Ns'’, ALL_DISTINCT_SNOC] \\
     Q.PAT_X_ASSUM ‘EVERY _ (SNOC N Ns)’ MP_TAC \\
     rw [EVERY_MEM, LIST_TO_SET_SNOC] \\ (* 2 subgoals, same tactics *)
     METIS_TAC [])
 >> ‘LENGTH vs' = LENGTH Ns'’ by rw [Abbr ‘vs'’, Abbr ‘Ns'’]
 >> ‘y IN FDOM (fromPairs vs' Ns')’ by rw [FDOM_fromPairs, Abbr ‘vs'’]
 >> simp [Abbr ‘t’, ssub_appstar]
 >> Know ‘fromPairs vs' Ns' ' y = N’
 >- (‘y = LAST vs'’ by rw [Abbr ‘vs'’, LAST_SNOC] >> POP_ORW \\
     ‘vs' <> []’ by rw [Abbr ‘vs'’] \\
     rw [LAST_EL] \\
     qabbrev_tac ‘n = PRE (LENGTH Ns')’ \\
     Know ‘fromPairs vs' Ns' ' (EL n vs') = EL n Ns'’
     >- (MATCH_MP_TAC fromPairs_FAPPLY_EL \\
         rw [Abbr ‘vs'’, Abbr ‘Ns'’, ALL_DISTINCT_SNOC, Abbr ‘n’]) >> Rewr' \\
    ‘Ns' <> []’ by rw [Abbr ‘Ns'’] \\
    ‘EL n Ns' = LAST Ns'’ by rw [LAST_EL, Abbr ‘n’] >> POP_ORW \\
     rw [Abbr ‘Ns'’, LAST_SNOC])
 >> Rewr'
 >> Suff ‘MAP ($' (fromPairs vs' Ns')) (MAP VAR vs) = Ns’ >- rw []
 >> rw [LIST_EQ_REWRITE]
 >> rename1 ‘i < LENGTH Ns’
 >> Know ‘EL i vs IN FDOM (fromPairs vs' Ns')’
 >- (rw [FDOM_fromPairs] \\
     rw [Abbr ‘vs'’, MEM_EL] \\
     DISJ2_TAC >> Q.EXISTS_TAC ‘i’ >> art [])
 >> rw [EL_MAP]
 >> Know ‘(EL i vs = EL i vs') /\ (EL i Ns = EL i Ns')’
 >- ASM_SIMP_TAC std_ss [EL_SNOC, Abbr ‘vs'’, Abbr ‘Ns'’]
 >> rw []
 >> MATCH_MP_TAC fromPairs_FAPPLY_EL
 >> rw [Abbr ‘vs'’, Abbr ‘Ns'’, ALL_DISTINCT_SNOC]
QED

(* NOTE: More arguments remain the same after head reductions *)
Theorem permutator_hreduce_more :
    !n N Ns args. LENGTH Ns = n ==>
                  permutator n @* Ns @@ N @* args -h->* N @* Ns @* args
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘X = BIGUNION (IMAGE FV (set Ns)) UNION FV N’
 >> Know ‘FINITE X’
 >- (rw [Abbr ‘X’] >> REWRITE_TAC [FINITE_FV])
 >> DISCH_THEN (MP_TAC o (MATCH_MP permutator_alt))
 >> DISCH_THEN (STRIP_ASSUME_TAC o (Q.SPEC ‘n’))
 >> POP_ORW
 >> MATCH_MP_TAC permutator_hreduce_lemma
 >> fs [ALL_DISTINCT_SNOC]
 >> POP_ASSUM MP_TAC (* DISJOINT X ... *)
 >> rw [Abbr ‘X’, EVERY_MEM, LIST_TO_SET_SNOC] >> art []
 >| [ (* goal 1 (of 2) *)
      Q.PAT_X_ASSUM ‘!s. P’ (MP_TAC o (Q.SPEC ‘FV (e :term)’)) \\
      impl_tac >- (Q.EXISTS_TAC ‘e’ >> art []) >> rw [],
      (* goal 2 (of 2) *)
      Q.PAT_X_ASSUM ‘!s. P’ (MP_TAC o (Q.SPEC ‘FV (e :term)’)) \\
      impl_tac >- (Q.EXISTS_TAC ‘e’ >> art []) >> rw [] ]
QED

(* NOTE: ‘EL n l’ is undefined without ‘n < LENGTH l’ *)
Theorem permutator_hreduce_more' :
    !n l. n < LENGTH l ==>
          permutator n @* l -h->* EL n l @* TAKE n l @* DROP (SUC n) l
Proof
    rpt STRIP_TAC
 >> Suff ‘permutator n @* l =
          permutator n @* TAKE n l @@ EL n l @* DROP (SUC n) l’
 >- (Rewr' \\
     MATCH_MP_TAC permutator_hreduce_more >> rw [LENGTH_TAKE])
 >> Suff ‘l = TAKE n l ++ [EL n l] ++ DROP (SUC n) l’
 >- (DISCH_THEN
      (GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites o wrap) \\
     REWRITE_TAC [GSYM SNOC_APPEND] \\
     REWRITE_TAC [appstar_APPEND] \\
     REWRITE_TAC [appstar_SNOC])
 >> MATCH_MP_TAC (GSYM TAKE_DROP_SUC) >> art []
QED

Theorem permutator_hreduce_same_length :
    !n N Ns. LENGTH Ns = n ==> permutator n @* Ns @@ N -h->* N @* Ns
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘n’, ‘N’, ‘Ns’, ‘[]’] permutator_hreduce_more)
 >> rw []
QED

(* This is an important theroem, hard to prove.

   To use this theorem, first one defines ‘M0 = principle_hnf M’ as abbreviation,
   then define ‘n = LAMl_size M0’ and ‘vs = NEWS n (FV M)’ (or ‘FV M0’, or
  ‘X UNION FV M0’, ‘X UNION FV M’), and this give us the needed antecedents:

       ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M) /\ LENGTH vs = n

   Then use hnf_cases_shared to derive ‘M0 = LAMl vs (VAR y @* args)’ and then
  ‘M1 = principle_hnf (M0 @* MAP VAR vs) = VAR y @* args’.

   The conclusion is that ‘principle_hnf (M @* MAP VAR vs) = M1’.

   Now ‘principle_hnf’ can be used to "denude" the outer LAMl of a solvable term.

   An extra list of free variables ‘l’ may need to append after MAP VAR vs.
 *)
Theorem hreduce_hnf_appstar_cong :
    !M vs y Ns args. ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M) /\
                     M -h->* LAMl vs (VAR y @* Ns) ==>
                     M @* MAP VAR vs @* args -h->* VAR y @* Ns @* args
Proof
    rpt STRIP_TAC
 >> Know ‘has_hnf M’
 >- (rw [has_hnf_def] \\
     Q.EXISTS_TAC ‘LAMl vs (VAR y @* Ns)’ >> rw [hnf_appstar] \\
     MATCH_MP_TAC hreduces_lameq >> art [])
 >> DISCH_TAC
 (* eliminating MAP VAR l *)
 >> MATCH_MP_TAC hreduce_rules_appstar'
 >> rw [is_abs_appstar]
 >- (fs [] >> CCONTR_TAC >> fs [] \\
    ‘is_abs (VAR y @* Ns)’ by PROVE_TAC [hreduce_abs] >> fs [])
 (* now l is eliminated *)
 >> NTAC 4 (POP_ASSUM MP_TAC)
 >> Suff ‘!M M0. M -h->* M0 ==>
                 has_hnf M ==>
                   !vs t. ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M) /\
                         (M0 = LAMl vs t) /\ ~is_abs t ==>
                          M @* MAP VAR vs -h->* t’
 >- (rpt STRIP_TAC >> FIRST_X_ASSUM irule >> rw [])
 >> HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1
 >> rw [hreduce_BETA] (* only one goal left *)
 >> Q.PAT_X_ASSUM ‘has_hnf M ==> P’ MP_TAC
 >> RW_TAC std_ss []
 (* NOTE: this assumption is only possible with RTC_STRONG_INDUCT, etc. *)
 >> Know ‘DISJOINT (set vs) (FV M0)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘FV M’ >> art [] \\
     MATCH_MP_TAC hreduce_FV_SUBSET >> art [])
 >> DISCH_TAC
 (* stage work.

    Now we need to discuss the possible shapes of M0:

    1. M0 := LAMl vs (P @@ Q), where P @@ Q -h-> t
    2. M0 := LAMl vs1 (P @@ Q), where P @@ Q -h-> LAMl vs2 t, vs = vs1 ++ vs2

    The first case is included in the second case.

    Using IH, we have: M @* MAP VAR vs1 -h->* P @@ Q -h-> LAMl vs2 t (hnf)
    Thus (using RTC transitivity): M @* MAP VAR vs1 -h->* LAMl vs2 t (hnf)

    Since M @* MAP VAR vs = M @* MAP VAR vs1 @* MAP VAR vs2, the head reduction
    process should proceed with the part ‘M @* MAP VAR vs1’ until arrive at
   ‘P @@ Q’ (APP) without showing any LAM (otherwise it cannot be P @@ Q), and
    then do it again to ‘LAMl vs2 t’, i.e.

    M @* MAP VAR vs1 @* MAP VAR vs2 -h->* P @@ Q @* MAP VAR vs2
                                    -h-> LAMl vs2 t @* MAP VAR vs2
                                    -h->* t (QED)

    The possible fact ‘hnf t’ is not used in the above reduction process.
 *)
 (* applying hreduce1_LAMl_cases *)
 >> Know ‘ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M0) /\ M0 -h-> LAMl vs t /\
          ~is_abs t’ >- art []
 >> DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP hreduce1_LAMl_cases))
 (* stage work *)
 >> Q.PAT_X_ASSUM ‘!vs t. P’ (MP_TAC o (Q.SPECL [‘vs1’, ‘N’]))
 >> Know ‘ALL_DISTINCT vs1’
 >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs’ MP_TAC \\
     rw [ALL_DISTINCT_APPEND])
 >> Know ‘DISJOINT (set vs1) (FV M)’
 >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) (FV M)’ MP_TAC \\
     rw [LIST_TO_SET_APPEND])
 >> RW_TAC std_ss []
 >> simp [appstar_APPEND]
 >> MATCH_MP_TAC hreduce_TRANS
 >> Q.EXISTS_TAC ‘LAMl vs2 t @* MAP VAR vs2’
 >> reverse CONJ_TAC >- rw [hreduce_BETA]
 >> rw [Once RTC_CASES2] >> DISJ2_TAC
 >> Q.EXISTS_TAC ‘N @* MAP VAR vs2’
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC hreduce1_appstar >> art [] \\
     fs [is_comb_APP_EXISTS])
 >> MATCH_MP_TAC hreduce_rules_appstar' >> art []
 >> rw [is_abs_appstar]
 >> CCONTR_TAC >> fs []
 >> PROVE_TAC [hreduce_abs] (* is_abs N *)
QED

val _ = export_theory()
val _ = html_theory "head_reduction";

(* References:

   [1] Barendregt, H.P.: The Lambda Calculus, Its Syntax and Semantics.
       College Publications, London (1984).
 *)
