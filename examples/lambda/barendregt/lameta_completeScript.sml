(* ========================================================================== *)
(* FILE    : lameta_completeScript.sml (chap10_4Script.sml)                   *)
(* TITLE   : Completeness of (Untyped) Lambda-Calculus [1, Chapter 10.4]      *)
(*                                                                            *)
(* AUTHORS : 2024-2025 The Australian National University (Chun Tian)         *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open hurdUtils combinTheory tautLib arithmeticTheory pred_setTheory listTheory
     rich_listTheory llistTheory ltreeTheory relationTheory topologyTheory
     iterateTheory optionTheory;

open nomsetTheory basic_swapTheory NEWLib termTheory appFOLDLTheory chap2Theory
     chap3Theory horeductionTheory reductionEval solvableTheory takahashiS3Theory
     head_reductionTheory head_reductionLib standardisationTheory boehmTheory
     chap4Theory;

(* enable basic monad support *)
open monadsyntax;
val _ = enable_monadsyntax ();
val _ = enable_monad "option";

val _ = new_theory "lameta_complete";

val _ = temp_delsimps [
   "lift_disj_eq", "lift_imp_disj",
   "IN_UNION",     (* |- !s t x. x IN s UNION t <=> x IN s \/ x IN t *)
   "APPEND_ASSOC", (* |- !l1 l2 l3. l1 ++ (l2 ++ l3) = l1 ++ l2 ++ l3 *)
   "SNOC_APPEND"   (* |- !x l. SNOC x l = l ++ [x] *)
];

Overload FV  = “supp term_pmact”
Overload VAR = “term$VAR”

val _ = hide "B";
val _ = hide "C";
val _ = hide "W";
val _ = hide "Y";

(* some proofs here are large with too many assumptions *)
val _ = set_trace "Goalstack.print_goal_at_top" 0;

(*---------------------------------------------------------------------------*
 *  An equivalence relation of terms
 *---------------------------------------------------------------------------*)

(* Definition 10.2.19 [1, p. 238]

   M = LAMl v1 (y  @* Ms) @@ (MAP VAR v1) == y  @* Ms'
   N = LAMl v2 (y' @* Ns) @@ (MAP VAR v2) == y' @* Ns'

   LENGTH Ms  = n /\ LENGTH Ns  = n'
   LENGTH Ms' = m /\ LENGTH Ns' = m'

   y = y'
   n - m = n' - m' (possibly negative) <=> n + m' = n' + m (non-negative)
 *)
Definition equivalent_def :
    equivalent M N =
        if solvable M /\ solvable N then
           let M0 = principle_hnf M;
               N0 = principle_hnf N;
               n  = LAMl_size M0;
               n' = LAMl_size N0;
               vs = NEWS (MAX n n') (FV M UNION FV N);
              vsM = TAKE n  vs;
              vsN = TAKE n' vs;
               M1 = principle_hnf (M0 @* MAP VAR vsM);
               N1 = principle_hnf (N0 @* MAP VAR vsN);
               y  = hnf_head M1;
               y' = hnf_head N1;
               m  = LENGTH (hnf_children M1);
               m' = LENGTH (hnf_children N1);
           in
               y = y' /\ n + m' = n' + m
        else
           ~solvable M /\ ~solvable N
End

(* A more general definition (but many existing hard proofs are still
   using the above “equivalent”).
 *)
Definition equivalent2_def :
    equivalent2 X M N r =
        if solvable M /\ solvable N then
           let M0 = principle_hnf M;
               N0 = principle_hnf N;
               n1 = LAMl_size M0;
               n2 = LAMl_size N0;
              vs1 = RNEWS r n1 X;
              vs2 = RNEWS r n2 X;
               M1 = principle_hnf (M0 @* MAP VAR vs1);
               N1 = principle_hnf (N0 @* MAP VAR vs2);
               y1  = hnf_head M1;
               y2 = hnf_head N1;
               m1 = LENGTH (hnf_children M1);
               m2 = LENGTH (hnf_children N1);
           in
               y1 = y2 /\ n1 + m2 = n2 + m1
        else
           ~solvable M /\ ~solvable N
End

Theorem equivalent_alt_equivalent2 :
    !M N. equivalent M N <=> equivalent2 (FV M UNION FV N) M N 0
Proof
    RW_TAC std_ss [equivalent_def, equivalent2_def]
 >> Know ‘vsN = vs2’
 >- (qunabbrevl_tac [‘vsN’, ‘vs’, ‘vs2’] \\
     MATCH_MP_TAC TAKE_RNEWS >> simp [])
 >> DISCH_THEN (fs o wrap)
 >> qunabbrev_tac ‘vsN’
 >> Q.PAT_X_ASSUM ‘n = n1’ (fs o wrap o SYM)
 >> Know ‘vsM = vs1’
 >- (qunabbrevl_tac [‘vsM’, ‘vs’, ‘vs1’] \\
     MATCH_MP_TAC TAKE_RNEWS >> simp [])
 >> DISCH_THEN (fs o wrap)
 >> Q.PAT_X_ASSUM ‘M1' = M1’ (fs o wrap)
 >> Q.PAT_X_ASSUM ‘m = m1’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘y = y1’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘N1' = N1’ (fs o wrap o SYM)
QED

(* NOTE: 0 < r is not necessary but makes the proof easier *)
Theorem equivalent2_thm :
    !X M N r. FINITE X /\ 0 < r /\
              FV M SUBSET X UNION RANK r /\
              FV N SUBSET X UNION RANK r ==>
             (equivalent2 X M N r <=> equivalent M N)
Proof
    rpt STRIP_TAC
 >> reverse (Cases_on ‘solvable M’)
 >- rw [equivalent_def, equivalent2_def]
 >> reverse (Cases_on ‘solvable N’)
 >- rw [equivalent_def, equivalent2_def]
 >> RW_TAC std_ss [equivalent_def, equivalent2_def]
 >> qabbrev_tac ‘Y = FV M UNION FV N’
 (* cleanup duplicated abbreviations *)
 >> simp [Abbr ‘n1’]
 >> fs [Abbr ‘n’, Abbr ‘n'’]
 >> qabbrev_tac ‘n1 = LAMl_size M0’
 >> qabbrev_tac ‘n2 = LAMl_size N0’
 >> rfs [Abbr ‘vs1’, Abbr ‘vs2’]
 >> Q_TAC (RNEWS_TAC (“vs3 :string list”, “r :num”, “n1 :num”)) ‘X’
 >> Q_TAC (RNEWS_TAC (“vs4 :string list”, “r :num”, “n2 :num”)) ‘X’
 (* stage work *)
 >> qabbrev_tac ‘n = MAX n1 n2’
 >> ‘n1 <= n /\ n2 <= n’ by rw [Abbr ‘n’, MAX_LE]
 >> ‘FINITE Y’ by rw [Abbr ‘Y’]
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (NEWS_TAC (“vs :string list”, “n :num”)) ‘Y’
 (* vs0 includes both vs3 and vs4 *)
 >> Q_TAC (RNEWS_TAC (“vs0 :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘TAKE n1 vs0 = vs3’ by rw [Abbr ‘vs0’, Abbr ‘vs3’, TAKE_RNEWS]
 >> ‘TAKE n2 vs0 = vs4’ by rw [Abbr ‘vs0’, Abbr ‘vs4’, TAKE_RNEWS]
 >> Know ‘DISJOINT (set vs) (FV M0)’
 >- (MATCH_MP_TAC subterm_disjoint_lemma' \\
     qexistsl_tac [‘Y’, ‘M’, ‘0’, ‘n’] >> simp [Abbr ‘Y’])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set vs) (FV N0)’
 >- (MATCH_MP_TAC subterm_disjoint_lemma' \\
     qexistsl_tac [‘Y’, ‘N’, ‘0’, ‘n’] >> simp [Abbr ‘Y’])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set vs0) (FV M0)’
 >- (MATCH_MP_TAC subterm_disjoint_lemma' \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’] >> simp [])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set vs0) (FV N0)’
 >- (MATCH_MP_TAC subterm_disjoint_lemma' \\
     qexistsl_tac [‘X’, ‘N’, ‘r’, ‘n’] >> simp [])
 >> DISCH_TAC
 >> qunabbrevl_tac [‘vsM’, ‘vsN’]
 >> qabbrev_tac ‘vs1 = TAKE n1 vs’
 >> qabbrev_tac ‘vs2 = TAKE n2 vs’
 >> ‘LENGTH vs1 = n1 /\ LENGTH vs2 = n2 /\
     ALL_DISTINCT vs1 /\ ALL_DISTINCT vs2’
      by simp [Abbr ‘vs1’, Abbr ‘vs2’, ALL_DISTINCT_TAKE]
 >> qunabbrev_tac ‘y1’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y1 :string”, “args1 :term list”)) ‘M1’ >> rfs []
 >> qunabbrev_tac ‘y2’
 >> Q_TAC (HNF_TAC (“N0 :term”, “vs :string list”,
                    “y2 :string”, “args2 :term list”)) ‘N1’ >> rfs []
 >> simp [Abbr ‘m1’, Abbr ‘m2’]
 >> Q.PAT_X_ASSUM ‘M0 = _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘N0 = _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘N1 = _’ (ASSUME_TAC o SYM)
 >> qunabbrevl_tac [‘y’, ‘y'’]
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs0 :string list”,
                    “y3 :string”, “args3 :term list”)) ‘M1'’ >> rfs []
 >> Q_TAC (HNF_TAC (“N0 :term”, “vs0 :string list”,
                    “y4 :string”, “args4 :term list”)) ‘N1'’ >> rfs []
 >> simp [Abbr ‘m’, Abbr ‘m'’]
 >> Q.PAT_X_ASSUM ‘M0  = _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M1' = _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘N0  = _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘N1' = _’ (ASSUME_TAC o SYM)
 >> fs []
 >> Know ‘DISJOINT (set vs3) (set vs1)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘set vs’ >> simp [Abbr ‘vs1’, LIST_TO_SET_TAKE] \\
     qunabbrevl_tac [‘vs’, ‘vs3’] \\
     MATCH_MP_TAC DISJOINT_RNEWS >> simp [])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set vs4) (set vs2)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘set vs’ >> simp [Abbr ‘vs2’, LIST_TO_SET_TAKE] \\
     qunabbrevl_tac [‘vs’, ‘vs4’] \\
     MATCH_MP_TAC DISJOINT_RNEWS >> simp [])
 >> DISCH_TAC
 (* NOTE: Two explicit HNFs for M0/N0 by vs1/vs2 and vs3/vs4

    LAMl vs1 M1 = M0 = LAMl vs3 M1'
    LAMl vs2 M2 = N0 = LAMl vs4 M2'

    vs1/vs2 is in ROW 0, while vs3/vs4 is in ROW r (0 < r).

    Now prove upper bounds of FV M1/N1 for disjointness with vs3/vs4 (ROW r)
  *)
 >> Know ‘FV M1 SUBSET FV (M0 @* MAP VAR vs1)’
 >- (qunabbrev_tac ‘M1’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET \\
     simp [has_hnf_def] \\
     qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs1)’ \\
     Q.EXISTS_TAC ‘M1’ \\
     Q.PAT_X_ASSUM ‘LAMl vs1 M1 = M0’ (REWRITE_TAC o wrap o SYM) \\
     simp [] \\
     Q.PAT_X_ASSUM ‘_ = M1’ (REWRITE_TAC o wrap o SYM) \\
     simp [hnf_appstar])
 >> DISCH_TAC
 >> Know ‘FV M1 SUBSET X UNION RANK r’
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV (M0 @* MAP VAR vs1)’ >> simp [] \\
     CONJ_TAC
     >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M’ >> art [] \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) \\
     Suff ‘set vs1 SUBSET RANK r’ >- SET_TAC [] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs’ \\
     simp [Abbr ‘vs1’, LIST_TO_SET_TAKE] \\
     qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC RNEWS_SUBSET_RANK >> art [])
 >> DISCH_TAC
 >> Know ‘FV N1 SUBSET FV (N0 @* MAP VAR vs2)’
 >- (qunabbrev_tac ‘N1’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET \\
     simp [has_hnf_def] \\
     qabbrev_tac ‘N1 = principle_hnf (N0 @* MAP VAR vs2)’ \\
     Q.EXISTS_TAC ‘N1’ \\
     Q.PAT_X_ASSUM ‘LAMl vs2 N1 = N0’ (REWRITE_TAC o wrap o SYM) \\
     simp [] \\
     Q.PAT_X_ASSUM ‘_ = N1’ (REWRITE_TAC o wrap o SYM) \\
     simp [hnf_appstar])
 >> DISCH_TAC
 >> Know ‘FV N1 SUBSET X UNION RANK r’
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV (N0 @* MAP VAR vs2)’ >> simp [] \\
     CONJ_TAC
     >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV N’ >> art [] \\
         qunabbrev_tac ‘N0’ \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) \\
     Suff ‘set vs2 SUBSET RANK r’ >- SET_TAC [] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs’ \\
     simp [Abbr ‘vs2’, LIST_TO_SET_TAKE] \\
     qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC RNEWS_SUBSET_RANK >> art [])
 >> DISCH_TAC
 (* preparing for LAMl_ALPHA *)
 >> Know ‘DISJOINT (set vs3) (set vs1 UNION FV M1)’
 >- (simp [DISJOINT_UNION'] \\
     MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘X UNION RANK r’ >> art [] \\
     simp [DISJOINT_UNION'] \\
     qunabbrev_tac ‘vs3’ \\
     MATCH_MP_TAC DISJOINT_RNEWS_RANK >> simp [])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set vs4) (set vs2 UNION FV N1)’
 >- (simp [DISJOINT_UNION'] \\
     MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘X UNION RANK r’ >> art [] \\
     simp [DISJOINT_UNION'] \\
     qunabbrev_tac ‘vs4’ \\
     MATCH_MP_TAC DISJOINT_RNEWS_RANK >> simp [])
 >> DISCH_TAC
 (* applying LAMl_ALPHA_tpm *)
 >> Know ‘LAMl vs1 M1 = LAMl vs3 (tpm (ZIP (vs1,vs3)) M1)’
 >- (MATCH_MP_TAC LAMl_ALPHA_tpm >> art [])
 >> DISCH_THEN (ASSUME_TAC o SYM)
 >> Know ‘LAMl vs2 N1 = LAMl vs4 (tpm (ZIP (vs2,vs4)) N1)’
 >- (MATCH_MP_TAC LAMl_ALPHA_tpm >> art [])
 >> DISCH_THEN (ASSUME_TAC o SYM)
 >> qabbrev_tac ‘pm1 = ZIP (vs1,vs3)’
 >> qabbrev_tac ‘pm2 = ZIP (vs2,vs4)’
 >> Know ‘LAMl vs3 (tpm pm1 M1) = LAMl vs3 M1' /\
          LAMl vs4 (tpm pm2 N1) = LAMl vs4 N1'’
 >- PROVE_TAC []
 >> simp [] >> STRIP_TAC
 >> qabbrev_tac ‘pm0 = ZIP (vs,vs0)’
 >> Suff ‘tpm pm1 M1 = tpm pm0 M1 /\ tpm pm2 N1 = tpm pm0 N1’
 >- (Q.PAT_X_ASSUM ‘tpm pm1 M1 = M1'’ (REWRITE_TAC o wrap) \\
     Q.PAT_X_ASSUM ‘tpm pm2 N1 = N1'’ (REWRITE_TAC o wrap) \\
     Q.PAT_X_ASSUM ‘_ = M1’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = N1’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = M1'’ (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = N1'’ (REWRITE_TAC o wrap o SYM) \\
     simp [tpm_appstar])
 (* clean useless assumptions (mostly about M1' and N1') *)
 >> Q.PAT_X_ASSUM ‘tpm pm1 M1 = M1'’        K_TAC
 >> Q.PAT_X_ASSUM ‘tpm pm2 N1 = N1'’        K_TAC
 >> Q.PAT_X_ASSUM ‘LAMl vs3 _ = LAMl vs1 _’ K_TAC
 >> Q.PAT_X_ASSUM ‘LAMl vs4 _ = LAMl vs2 _’ K_TAC
 >> Q.PAT_X_ASSUM ‘LAMl vs3 M1' = M0’       K_TAC
 >> Q.PAT_X_ASSUM ‘VAR y3 @* args3 = M1'’   K_TAC
 >> Q.PAT_X_ASSUM ‘LAMl vs4 N1' = N0’       K_TAC
 >> Q.PAT_X_ASSUM ‘VAR y4 @* args4 = N1'’   K_TAC
 >> fs [Abbr ‘M1'’, Abbr ‘N1'’]
 (* stage work, two ending symmetric subgoals *)
 >> CONJ_TAC
 >| [ (* goal 1 (of 2) *)
      simp [Abbr ‘pm0’, Abbr ‘pm1’] \\
      qabbrev_tac ‘vs1' = DROP n1 vs’ \\
      qabbrev_tac ‘vs3' = DROP n1 vs0’ \\
     ‘vs = vs1 ++ vs1'’ by rw [TAKE_DROP, Abbr ‘vs1’, Abbr ‘vs1'’] \\
      Know ‘DISJOINT (set vs1) (set vs1')’
      >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs’ MP_TAC \\
          rw [Abbr ‘vs’, ALL_DISTINCT_APPEND']) >> DISCH_TAC \\
     ‘vs0 = vs3 ++ vs3'’ by rw [TAKE_DROP, Abbr ‘vs3'’] \\
      Q.PAT_X_ASSUM ‘vs  = _’ (REWRITE_TAC o wrap) \\
      Q.PAT_X_ASSUM ‘vs0 = _’ (REWRITE_TAC o wrap) \\
     ‘LENGTH vs1' = n - n1’ by rw [Abbr ‘vs1'’, LENGTH_DROP] \\
     ‘LENGTH vs3' = n - n1’ by rw [Abbr ‘vs3'’, LENGTH_DROP] \\
      simp [GSYM ZIP_APPEND, pmact_decompose, Once EQ_SYM_EQ] \\
      MATCH_MP_TAC tpm_unchanged \\
      simp [MAP_ZIP] \\
      reverse CONJ_TAC
      >- (MATCH_MP_TAC DISJOINT_SUBSET \\
          Q.EXISTS_TAC ‘X UNION RANK r’ >> art [] \\
          MATCH_MP_TAC DISJOINT_SUBSET' \\
          Q.EXISTS_TAC ‘set vs0’ \\
          reverse CONJ_TAC >- simp [Abbr ‘vs3'’, LIST_TO_SET_DROP] \\
          rw [Once DISJOINT_SYM, Abbr ‘vs0’] \\
          MATCH_MP_TAC DISJOINT_RANK_RNEWS >> simp []) \\
   (* applying SET_TAC [] with sufficient conditions *)
      Q.PAT_X_ASSUM ‘FV M1 SUBSET FV M0 UNION set vs1’ MP_TAC \\
      Q.PAT_X_ASSUM ‘DISJOINT (set vs) (FV M0)’ MP_TAC \\
      Q.PAT_X_ASSUM ‘DISJOINT (set vs1) (set vs1')’ MP_TAC \\
      Know ‘set vs1' SUBSET set vs’ >- rw [Abbr ‘vs1'’, LIST_TO_SET_DROP] \\
      SET_TAC [],
      (* goal 2 (of 2) *)
      simp [Abbr ‘pm0’, Abbr ‘pm2’] \\
      qabbrev_tac ‘vs2' = DROP n2 vs’ \\
      qabbrev_tac ‘vs4' = DROP n2 vs0’ \\
     ‘vs = vs2 ++ vs2'’ by rw [TAKE_DROP, Abbr ‘vs2’, Abbr ‘vs2'’] \\
      Know ‘DISJOINT (set vs2) (set vs2')’
      >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs’ MP_TAC \\
          rw [Abbr ‘vs’, ALL_DISTINCT_APPEND']) >> DISCH_TAC \\
     ‘vs0 = vs4 ++ vs4'’ by rw [TAKE_DROP, Abbr ‘vs4'’] \\
      Q.PAT_X_ASSUM ‘vs  = _’ (REWRITE_TAC o wrap) \\
      Q.PAT_X_ASSUM ‘vs0 = _’ (REWRITE_TAC o wrap) \\
     ‘LENGTH vs2' = n - n2’ by rw [Abbr ‘vs2'’, LENGTH_DROP] \\
     ‘LENGTH vs4' = n - n2’ by rw [Abbr ‘vs4'’, LENGTH_DROP] \\
      simp [GSYM ZIP_APPEND, pmact_decompose, Once EQ_SYM_EQ] \\
      MATCH_MP_TAC tpm_unchanged \\
      simp [MAP_ZIP] \\
      reverse CONJ_TAC
      >- (MATCH_MP_TAC DISJOINT_SUBSET \\
          Q.EXISTS_TAC ‘X UNION RANK r’ >> art [] \\
          MATCH_MP_TAC DISJOINT_SUBSET' \\
          Q.EXISTS_TAC ‘set vs0’ \\
          reverse CONJ_TAC >- simp [Abbr ‘vs4'’, LIST_TO_SET_DROP] \\
          rw [Once DISJOINT_SYM, Abbr ‘vs0’] \\
          MATCH_MP_TAC DISJOINT_RANK_RNEWS >> simp []) \\
   (* applying SET_TAC [] with sufficient conditions *)
      Q.PAT_X_ASSUM ‘FV N1 SUBSET FV N0 UNION set vs2’ MP_TAC \\
      Q.PAT_X_ASSUM ‘DISJOINT (set vs) (FV N0)’ MP_TAC \\
      Q.PAT_X_ASSUM ‘DISJOINT (set vs2) (set vs2')’ MP_TAC \\
      Know ‘set vs2' SUBSET set vs’ >- rw [Abbr ‘vs2'’, LIST_TO_SET_DROP] \\
      SET_TAC [] ]
QED

Theorem equivalent_reflexive :
    reflexive equivalent
Proof
    rw [reflexive_def, equivalent_def]
QED

(* |- equivalent x x *)
Theorem equivalent_refl[simp] =
    SPEC_ALL (REWRITE_RULE [reflexive_def] equivalent_reflexive)

Theorem equivalent_symmetric :
    symmetric equivalent
Proof
    RW_TAC std_ss [symmetric_def, equivalent_def, Once MAX_COMM, Once UNION_COMM]
 >> reverse (Cases_on ‘solvable x /\ solvable y’) >- fs []
 >> simp []
 >> rename1 ‘y1 = y2 /\ m1 + n = m + n1 <=> y3 = y4 /\ m3 + n1 = m2 + n3’
 >> ‘n3 = n’ by rw [Abbr ‘n3’, Abbr ‘n’] >> gs []
 >> EQ_TAC >> rw []
QED

(* |- !x y. equivalent x y <=> equivalent y x *)
Theorem equivalent_comm = REWRITE_RULE [symmetric_def] equivalent_symmetric

Theorem equivalent_of_solvables :
    !M N. solvable M /\ solvable N ==>
         (equivalent M N <=>
          let M0 = principle_hnf M;
              N0 = principle_hnf N;
              n  = LAMl_size M0;
              n' = LAMl_size N0;
              vs = NEWS (MAX n n') (FV M UNION FV N);
             vsM = TAKE n  vs;
             vsN = TAKE n' vs;
              M1 = principle_hnf (M0 @* MAP VAR vsM);
              N1 = principle_hnf (N0 @* MAP VAR vsN);
              y  = hnf_head M1;
              y' = hnf_head N1;
              m  = LENGTH (hnf_children M1);
              m' = LENGTH (hnf_children N1);
           in
              y = y' /\ n + m' = n' + m)
Proof
    RW_TAC std_ss [equivalent_def]
QED

Theorem equivalent2_of_solvables :
    !X M N r. solvable M /\ solvable N ==>
          (equivalent2 X M N r =
           let M0 = principle_hnf M;
               N0 = principle_hnf N;
               n1 = LAMl_size M0;
               n2 = LAMl_size N0;
              vs1 = RNEWS r n1 X;
              vs2 = RNEWS r n2 X;
               M1 = principle_hnf (M0 @* MAP VAR vs1);
               N1 = principle_hnf (N0 @* MAP VAR vs2);
               y1  = hnf_head M1;
               y2 = hnf_head N1;
               m1 = LENGTH (hnf_children M1);
               m2 = LENGTH (hnf_children N1);
           in
               y1 = y2 /\ n1 + m2 = n2 + m1)
Proof
    RW_TAC std_ss [equivalent2_def]
QED

(* beta-equivalent terms are also equivalent here *)
Theorem lameq_imp_equivalent :
    !M N. M == N ==> equivalent M N
Proof
    rpt STRIP_TAC
 >> reverse (Cases_on ‘solvable M’)
 >- (‘unsolvable N’ by METIS_TAC [lameq_solvable_cong] \\
     rw [equivalent_def])
 >> ‘solvable N’ by METIS_TAC [lameq_solvable_cong]
 >> qabbrev_tac ‘X = FV M UNION FV N’
 >> ‘FINITE X’ by rw [Abbr ‘X’]
 >> ‘LAMl_size (principle_hnf M) = LAMl_size (principle_hnf N)’
       by METIS_TAC [lameq_principle_hnf_size_eq']
 (* stage work *)
 >> RW_TAC std_ss [equivalent_of_solvables] (* 2 subgoals, same tactics *)
 >> ‘ALL_DISTINCT vs /\ DISJOINT (set vs) X /\ LENGTH vs = n’
       by (rw [Abbr ‘vs’, NEWS_def])
 >> ‘vsM = vs’ by rw [Abbr ‘vsM’, TAKE_LENGTH_ID_rwt]
 >> POP_ASSUM (fs o wrap)
 >> Q.PAT_X_ASSUM ‘vs = vsN’ (fs o wrap o SYM)
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘N’, ‘M0’, ‘N0’, ‘n’, ‘vs’, ‘M1’, ‘N1’]
                    lameq_principle_hnf_thm_simple)
 >> simp [Abbr ‘X’, GSYM solvable_iff_has_hnf]
QED

Theorem lameq_imp_equivalent2 :
    !X M N r. FINITE X /\ FV M UNION FV N SUBSET X UNION RANK r /\
              M == N ==> equivalent2 X M N r
Proof
    rpt STRIP_TAC
 >> reverse (Cases_on ‘solvable M’)
 >- (‘unsolvable N’ by METIS_TAC [lameq_solvable_cong] \\
     rw [equivalent2_def])
 >> ‘solvable N’ by METIS_TAC [lameq_solvable_cong]
 >> ‘LAMl_size (principle_hnf M) = LAMl_size (principle_hnf N)’
       by METIS_TAC [lameq_principle_hnf_size_eq']
 (* stage work *)
 >> RW_TAC std_ss [equivalent2_of_solvables] (* 2 subgoals, same tactics *)
 >> qunabbrev_tac ‘vs1’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n1 :num”)) ‘X’
 >> qunabbrev_tac ‘vs2’
 >> MP_TAC (Q.SPECL [‘r’, ‘X’, ‘M’, ‘N’, ‘M0’, ‘N0’, ‘n1’, ‘vs’, ‘M1’, ‘N1’]
                    lameq_principle_hnf_thm')
 >> simp []
QED

(* NOTE: the initial calls of ‘principle_hnf’ get eliminated if the involved
         terms are already in head normal forms.
 *)
Theorem equivalent_of_hnf :
    !M N. hnf M /\ hnf N ==>
         (equivalent M N <=>
          let n  = LAMl_size M;
              n' = LAMl_size N;
              vs = NEWS (MAX n n') (FV M UNION FV N);
             vsM = TAKE n  vs;
             vsN = TAKE n' vs;
              M1 = principle_hnf (M @* MAP VAR vsM);
              N1 = principle_hnf (N @* MAP VAR vsN);
              y  = hnf_head M1;
              y' = hnf_head N1;
              m  = LENGTH (hnf_children M1);
              m' = LENGTH (hnf_children N1)
           in
              y = y' /\ n + m' = n' + m)
Proof
    rpt STRIP_TAC
 >> ‘solvable M /\ solvable N’ by PROVE_TAC [hnf_solvable]
 >> RW_TAC std_ss [equivalent_def, principle_hnf_reduce]
 >> METIS_TAC []
QED

Theorem equivalent2_of_hnf :
    !X M N r. hnf M /\ hnf N ==>
          (equivalent2 X M N r <=>
           let n1 = LAMl_size M;
               n2 = LAMl_size N;
              vs1 = RNEWS r n1 X;
              vs2 = RNEWS r n2 X;
               M1 = principle_hnf (M @* MAP VAR vs1);
               N1 = principle_hnf (N @* MAP VAR vs2);
               y1 = hnf_head M1;
               y2 = hnf_head N1;
               m1 = LENGTH (hnf_children M1);
               m2 = LENGTH (hnf_children N1);
           in
               y1 = y2 /\ n1 + m2 = n2 + m1)

Proof
    rpt STRIP_TAC
 >> ‘solvable M /\ solvable N’ by PROVE_TAC [hnf_solvable]
 >> RW_TAC std_ss [equivalent2_def, principle_hnf_reduce]
 >> METIS_TAC []
QED

(* From [1, p.238]. This concerte example shows that dB encoding is not easy in
   defining this "concept": the literal encoding of inner head variables are not
   the same for equivalent terms.
 *)
Theorem not_equivalent_example :
    !x y. x <> y ==> ~equivalent (LAM x (VAR y @@ t)) (LAM y (VAR y @@ t))
Proof
    qx_genl_tac [‘x’, ‘v’] >> DISCH_TAC
 >> ‘hnf (LAM x (VAR v @@ t)) /\ hnf (LAM v (VAR v @@ t))’ by rw []
 >> ‘solvable (LAM x (VAR v @@ t)) /\ solvable (LAM v (VAR v @@ t))’
       by rw [hnf_solvable]
 >> RW_TAC std_ss [equivalent_of_solvables, principle_hnf_reduce]
 (* fix M0 *)
 >> qunabbrev_tac ‘M0’ >> qabbrev_tac ‘M0 = LAM x (VAR v @@ t)’
 >> ‘ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M0 UNION FV N0) /\
     LENGTH vs = MAX n n'’ by rw [Abbr ‘vs’, NEWS_def]
 >> ‘DISJOINT (set vs) (FV M0) /\ DISJOINT (set vs) (FV N0)’
      by METIS_TAC [DISJOINT_SYM, DISJOINT_UNION]
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y1 :string”, “args1 :term list”)) ‘M1’
 >> Q_TAC (HNF_TAC (“N0 :term”, “vs :string list”,
                    “y2 :string”, “args2 :term list”)) ‘N1’
 >> ‘TAKE (LAMl_size M0) vs = vsM’ by rw [Abbr ‘vsM’, Abbr ‘n’]
 >> ‘TAKE (LAMl_size N0) vs = vsN’ by rw [Abbr ‘vsN’, Abbr ‘n'’]
 >> NTAC 2 (POP_ASSUM (rfs o wrap))
 (* reshaping and reordering assumptions *)
 >> qunabbrev_tac ‘M1’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vsM)’
 >> qunabbrev_tac ‘N1’
 >> qabbrev_tac ‘N1 = principle_hnf (N0 @* MAP VAR vsN)’
 >> Q.PAT_X_ASSUM ‘M0 = _’ ASSUME_TAC
 >> Q.PAT_X_ASSUM ‘N0 = _’ ASSUME_TAC
 >> Q.PAT_X_ASSUM ‘M1 = _’ ASSUME_TAC
 >> Q.PAT_X_ASSUM ‘N1 = _’ ASSUME_TAC
 >> ‘VAR y1 = y’  by rw [Abbr ‘y’ , absfree_hnf_head]
 >> ‘VAR y2 = y'’ by rw [Abbr ‘y'’, absfree_hnf_head]
 >> qunabbrevl_tac [‘n’, ‘n'’]
 >> Know ‘LAMl_size M0 = 1 /\ LAMl_size N0 = 1’
 >- (rw [Abbr ‘M0’, Abbr ‘N0’, LAMl_size_def])
 >> DISCH_THEN (rfs o wrap)
 >> ‘vsN = vs’ by rw [Abbr ‘vsN’, TAKE_LENGTH_ID_rwt]
 >> POP_ASSUM (rfs o wrap)
 >> Q.PAT_X_ASSUM ‘vs = vsM’ (rfs o wrap o SYM)
 >> qunabbrev_tac ‘vsN’
 (* stage work *)
 >> qabbrev_tac ‘z = HD vs’
 >> ‘vs = [z]’ by METIS_TAC [SING_HD]
 >> POP_ASSUM (rfs o wrap)
 >> qunabbrevl_tac [‘M0’, ‘N0’]
 >> DISJ1_TAC
 >> qunabbrevl_tac [‘y’, ‘y'’]
 >> Q.PAT_X_ASSUM ‘VAR y1 = hnf_head M1’ (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘_ = LAM z (VAR y1 @* args1)’ (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘_ = LAM z (VAR y2 @* args2)’ (rfs o wrap o SYM)
 (* now the goal is ‘y1 <> y2’ *)
 >> qabbrev_tac ‘u = VAR v @@ t’
 >> ‘hnf u’ by rw [Abbr ‘u’]
 >> Know ‘M1 = [VAR z/x] u’
 >- (qunabbrev_tac ‘M1’ \\
     Cases_on ‘z = x’ >- (POP_ASSUM (gs o wrap) \\
                          fs [principle_hnf_beta_reduce1]) \\
     MATCH_MP_TAC principle_hnf_beta >> simp [Abbr ‘u’] \\
     rfs [FV_thm])
 >> DISCH_THEN (rfs o wrap)
 >> Know ‘N1 = [VAR z/v] u’
 >- (qunabbrev_tac ‘N1’ \\
     Cases_on ‘z = v’ >- (POP_ASSUM (rfs o wrap)) \\
     MATCH_MP_TAC principle_hnf_beta >> simp [Abbr ‘u’] \\
     rfs [FV_thm])
 >> DISCH_THEN (rfs o wrap)
 >> qunabbrevl_tac [‘M1’, ‘N1’]
 >> rfs [Abbr ‘u’, app_eq_appstar]
 >> METIS_TAC []
QED

Theorem equivalent_of_unsolvables :
    !M N. unsolvable M /\ unsolvable N ==> equivalent M N
Proof
    rw [equivalent_def]
QED

Theorem equivalent2_of_unsolvables :
    !X M N r. unsolvable M /\ unsolvable N ==> equivalent2 X M N r
Proof
    rw [equivalent2_def]
QED

Theorem subtree_equiv_alt_equivalent2 :
    !X M N r. FINITE X /\
              FV M SUBSET X UNION RANK r /\
              FV N SUBSET X UNION RANK r ==>
             (subtree_equiv X M N [] r <=> equivalent2 X M N r)
Proof
    rpt STRIP_TAC
 (* special cases (unsolvable) *)
 >> reverse (Cases_on ‘solvable M’)
 >- (rw [subtree_equiv_def, equivalent2_def, BT_of_unsolvables, ltree_el_def] \\
     reverse EQ_TAC
     >- rw [BT_of_unsolvables, ltree_el_def] \\
     DISCH_TAC \\
     Know ‘ltree_el (BT' X N r) [] = SOME bot’
     >- (MATCH_MP_TAC ltree_equiv_some_bot_imp >> art []) \\
     simp [Once MONO_NOT_EQ] >> DISCH_TAC \\
     rw [BT_def, Once ltree_unfold, BT_generator_def, ltree_el_def])
 >> reverse (Cases_on ‘solvable N’)
 >- (rw [subtree_equiv_def, equivalent2_def, BT_of_unsolvables, ltree_el_def] \\
     CCONTR_TAC >> fs [] \\
     Know ‘ltree_el (BT' X M r) [] = SOME bot’
     >- (MATCH_MP_TAC ltree_equiv_some_bot_imp' >> art []) \\
     rw [BT_def, Once ltree_unfold, BT_generator_def, ltree_el_def])
 (* stage work, now both M and N are solvable *)
 >> RW_TAC std_ss [subtree_equiv_def, equivalent2_def]
 >> Q_TAC (UNBETA_TAC [BT_def, Once ltree_unfold, BT_generator_def]) ‘BT' X M r’
 >> Q_TAC (UNBETA_TAC [BT_def, Once ltree_unfold, BT_generator_def]) ‘BT' X N r’
 >> simp [GSYM BT_def, LMAP_fromList]
 >> rw [ltree_el_def, Abbr ‘l’, Abbr ‘l'’, head_equivalent_def]
 >> qunabbrevl_tac [‘n’, ‘n'’, ‘n2’, ‘M0'’]
 >> qabbrev_tac ‘N0 = principle_hnf N’
 >> qabbrev_tac ‘n1 = LAMl_size M0’
 >> qabbrev_tac ‘n2 = LAMl_size N0’
 >> fs []
 >> Q.PAT_X_ASSUM ‘vs2 = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs = vs1’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘N1 = M1''’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1' = M1’ (fs o wrap o SYM)
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs1 :string list”, “r :num”, “n1 :num”)) ‘X’
 >> qunabbrev_tac ‘vs2’
 >> Q_TAC (RNEWS_TAC (“vs2 :string list”, “r :num”, “n2 :num”)) ‘X’
 >> ‘DISJOINT (set vs1) (FV M0)’ by PROVE_TAC [subterm_disjoint_lemma']
 >> ‘DISJOINT (set vs2) (FV N0)’ by PROVE_TAC [subterm_disjoint_lemma']
 (* decompose M0 *)
 >> qunabbrev_tac ‘y1’
 >> qunabbrev_tac ‘M1'’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs1)’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs1 :string list”,
                    “y1 :string”, “args1 :term list”)) ‘M1’
 >> ‘TAKE n1 vs1 = vs1’ by rw []
 >> POP_ASSUM (rfs o wrap)
 (* decompose N0 *)
 >> qunabbrev_tac ‘y2’
 >> Q_TAC (HNF_TAC (“N0 :term”, “vs2 :string list”,
                    “y2 :string”, “args2 :term list”)) ‘N1’
 >> ‘TAKE n2 vs2 = vs2’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> simp [Abbr ‘y’, Abbr ‘y'’]
QED

(* NOTE: ‘0 < r’ is not necessary but makes this proof much easier. *)
Theorem subtree_equiv_alt_equivalent :
    !X M N r. FINITE X /\ 0 < r /\
              FV M SUBSET X UNION RANK r /\
              FV N SUBSET X UNION RANK r ==>
             (subtree_equiv X M N [] r <=> equivalent M N)
Proof
    rpt STRIP_TAC
 >> ASM_SIMP_TAC std_ss [subtree_equiv_alt_equivalent2]
 >> MATCH_MP_TAC equivalent2_thm >> art []
QED

(*---------------------------------------------------------------------------*
 *  BT_paths and BT_valid_paths
 *---------------------------------------------------------------------------*)

Definition BT_paths_def :
    BT_paths M = ltree_paths (BT' (FV M) M 0)
End

Theorem NIL_IN_BT_paths[simp] :
    [] IN BT_paths M
Proof
    rw [BT_paths_def]
QED

Theorem BT_paths_thm :
    !X M r. FINITE X /\ FV M SUBSET X UNION RANK r ==>
            BT_paths M = ltree_paths (BT' X M r)
Proof
    rw [BT_paths_def]
 >> MATCH_MP_TAC BT_ltree_paths_cong >> simp []
QED

Theorem BT_paths_alt :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r ==>
             (p IN BT_paths M <=> subterm X M p r <> NONE)
Proof
    rw [GSYM BT_ltree_paths_thm, GSYM BT_paths_thm]
QED

(* NOTE: "valid" paths are paths leading to non-bottom nodes. *)
Definition BT_valid_paths_def :
    BT_valid_paths M =
      {p | p IN BT_paths M /\ ltree_el (BT' (FV M) M 0) p <> SOME bot}
End

Theorem BT_valid_paths_nil[simp] :
    [] IN BT_valid_paths M <=> solvable M
Proof
    rw [BT_valid_paths_def]
 >> Suff ‘unsolvable (subterm' (FV M) M [] 0) <=>
          ltree_el (BT' (FV M) M 0) [] = SOME bot’
 >- (simp [] >> PROVE_TAC [])
 >> MATCH_MP_TAC BT_ltree_el_of_unsolvables >> simp []
QED

(* By subterm_tpm_cong and BT_ltree_el_of_unsolvables, etc. *)
Theorem BT_valid_paths_thm :
    !X M r. FINITE X /\ FV M SUBSET X UNION RANK r ==>
            BT_valid_paths M =
           {p | p IN ltree_paths (BT' X M r) /\
                ltree_el (BT' X M r) p <> SOME bot}
Proof
    rw [BT_valid_paths_def, Once EXTENSION]
 >> simp [GSYM BT_paths_thm]
 >> Cases_on ‘x IN BT_paths M’ >> rw []
 >> rename1 ‘p IN BT_paths M’
 >> Know ‘ltree_el (BT' X M r) p = SOME bot <=> unsolvable (subterm' X M p r)’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC BT_ltree_el_of_unsolvables >> art [] \\
     Know ‘subterm X M p r <> NONE <=> p IN ltree_paths (BT' X M r)’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC BT_ltree_paths_thm >> art []) >> Rewr' \\
     rw [GSYM BT_paths_thm])
 >> Rewr'
 >> Know ‘ltree_el (BT' (FV M) M 0) p = SOME bot <=>
          unsolvable (subterm' (FV M) M p 0)’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC BT_ltree_el_of_unsolvables >> simp [] \\
     Know ‘subterm (FV M) M p 0 <> NONE <=> p IN ltree_paths (BT' (FV M) M 0)’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC BT_ltree_paths_thm >> simp []) >> Rewr' \\
     rw [GSYM BT_paths_thm])
 >> Rewr'
 >> Suff ‘tpm_rel (subterm' (FV M) M p 0) (subterm' X M p r)’
 >- (rw [tpm_rel_alt] >> POP_ORW \\
     rw [solvable_tpm])
 >> irule (cj 2 subterm_tpm_cong) >> simp []
 >> Know ‘subterm (FV M) M p 0 <> NONE <=> p IN ltree_paths (BT' (FV M) M 0)’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC BT_ltree_paths_thm >> simp [])
 >> Rewr'
 >> rw [GSYM BT_paths_thm]
QED

(* By BT_ltree_paths_thm and BT_ltree_el_of_unsolvables, etc. *)
Theorem BT_valid_paths_thm' :
    !X M r. FINITE X /\ FV M SUBSET X UNION RANK r ==>
            BT_valid_paths M =
           {p | subterm X M p r <> NONE /\ solvable (subterm' X M p r)}
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘r’] BT_valid_paths_thm) >> rw []
 >> rw [Once EXTENSION]
 >> simp [GSYM BT_ltree_paths_thm]
 >> Cases_on ‘x IN ltree_paths (BT' X M r)’ >> rw []
 >> rename1 ‘p IN ltree_paths (BT' X M r)’
 >> Suff ‘unsolvable (subterm' X M p r) <=> ltree_el (BT' X M r) p = SOME bot’
 >- PROVE_TAC []
 >> MATCH_MP_TAC BT_ltree_el_of_unsolvables
 >> rw [GSYM BT_ltree_paths_thm]
QED

Theorem BT_ltree_el_cases :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\ bnf M /\
              p IN ltree_paths (BT' X M r) ==>
             ?vs y m. ltree_el (BT' X M r) p = SOME (SOME (vs,y),SOME m)
Proof
    rpt GEN_TAC
 >> qid_spec_tac ‘r’
 >> qid_spec_tac ‘M’
 >> Induct_on ‘p’
 >- (rpt STRIP_TAC \\
    ‘solvable M’ by PROVE_TAC [bnf_solvable] \\
     Q_TAC (UNBETA_TAC [BT_def, BT_generator_def, Once ltree_unfold])
           ‘BT' X M r’ \\
     simp [GSYM BT_def, ltree_el_def, Abbr ‘l’, LMAP_fromList])
 >> rpt STRIP_TAC
 >> POP_ASSUM MP_TAC
 >> ‘solvable M’ by PROVE_TAC [bnf_solvable]
 >> Q_TAC (UNBETA_TAC [BT_def, BT_generator_def, Once ltree_unfold])
          ‘BT' X M r’
 >> simp [GSYM BT_def, ltree_el_def, Abbr ‘l’, LMAP_fromList, LNTH_fromList,
          EL_MAP, ltree_paths_alt_ltree_el]
 >> qabbrev_tac ‘m = LENGTH Ms’
 >> Cases_on ‘h < m’ >> simp []
 >> DISCH_TAC
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> simp [ltree_paths_alt_ltree_el]
 >> CONJ_TAC
 >- (MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
     simp [Abbr ‘m’, Once EQ_SYM_EQ] \\
     MATCH_MP_TAC hnf_children_size_alt \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘vs’, ‘M1’] >> simp [])
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> qunabbrev_tac ‘y’
 >> ‘DISJOINT (set vs) (FV M0)’ by PROVE_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> Q.PAT_X_ASSUM ‘h < m’ MP_TAC
 >> simp [Abbr ‘Ms’, Abbr ‘m’] >> DISCH_TAC
 >> MATCH_MP_TAC hnf_children_bnf >> art []
 >> qexistsl_tac [‘vs’, ‘y’] >> art []
 >> Q.PAT_X_ASSUM ‘M0 = _’ (REWRITE_TAC o wrap o SYM)
 >> Suff ‘M0 = M’ >- rw []
 >> qunabbrev_tac ‘M0’
 >> MATCH_MP_TAC principle_hnf_bnf >> art []
QED

Theorem BT_ltree_el_cases' :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\ has_bnf M /\
              p IN ltree_paths (BT' X M r) ==>
             ?vs y m. ltree_el (BT' X M r) p = SOME (SOME (vs,y),SOME m)
Proof
    rw [has_bnf_thm]
 >> ‘M == N’ by PROVE_TAC [betastar_lameq]
 >> Know ‘FV N SUBSET X UNION RANK r’
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M’ >> art [] \\
     MATCH_MP_TAC betastar_FV_SUBSET >> art [])
 >> DISCH_TAC
 >> Know ‘BT' X M r = BT' X N r’
 >- (MATCH_MP_TAC lameq_BT_cong >> art [])
 >> DISCH_THEN (fs o wrap)
 >> MP_TAC (Q.SPECL [‘X’, ‘N’, ‘p’, ‘r’] BT_ltree_el_cases)
 >> simp []
QED

Theorem BT_ltree_el_neq_bot :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\ bnf M /\
              p IN ltree_paths (BT' X M r) ==>
              ltree_el (BT' X M r) p <> SOME bot
Proof
    rpt GEN_TAC
 >> STRIP_TAC
 >> ‘?vs y m. ltree_el (BT' X M r) p = SOME (SOME (vs,y),SOME m)’
      by METIS_TAC [BT_ltree_el_cases]
 >> simp []
QED

Theorem BT_valid_paths_bnf :
    !X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\ bnf M ==>
            BT_valid_paths M = BT_paths M
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘r’] BT_valid_paths_thm)
 >> simp []
 >> DISCH_THEN K_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘r’] BT_paths_thm)
 >> simp []
 >> DISCH_THEN K_TAC
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw []
 >> MATCH_MP_TAC BT_ltree_el_neq_bot >> art []
QED

Theorem lameq_BT_paths_cong :
    !X M N r. FINITE X /\ FV M UNION FV N SUBSET X UNION RANK r /\ M == N ==>
              BT_paths M = BT_paths N
Proof
    rw [SUBSET_UNION]
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘r’] BT_paths_thm)
 >> simp [] >> DISCH_THEN K_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘N’, ‘r’] BT_paths_thm)
 >> simp [] >> DISCH_THEN K_TAC
 >> Suff ‘BT' X M r = BT' X N r’ >- rw []
 >> MATCH_MP_TAC lameq_BT_cong >> art []
QED

Theorem lameq_BT_valid_paths_cong :
    !X M N r. FINITE X /\ FV M UNION FV N SUBSET X UNION RANK r /\ M == N ==>
              BT_valid_paths M = BT_valid_paths N
Proof
    rw [SUBSET_UNION]
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘r’] BT_valid_paths_thm)
 >> simp [] >> DISCH_THEN K_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘N’, ‘r’] BT_valid_paths_thm)
 >> simp [] >> DISCH_THEN K_TAC
 >> Suff ‘BT' X M r = BT' X N r’ >- rw []
 >> MATCH_MP_TAC lameq_BT_cong >> art []
QED

Theorem BT_valid_paths_has_bnf :
    !X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\ has_bnf M ==>
            BT_valid_paths M = BT_paths M
Proof
    rw [has_bnf_thm]
 >> ‘M == N’ by PROVE_TAC [betastar_lameq]
 >> ‘FV N SUBSET FV M’ by PROVE_TAC [betastar_FV_SUBSET]
 >> ‘FV N SUBSET X UNION RANK r’ by PROVE_TAC [SUBSET_TRANS]
 >> Know ‘BT_valid_paths M = BT_valid_paths N’
 >- (MATCH_MP_TAC lameq_BT_valid_paths_cong \\
     qexistsl_tac [‘X’, ‘r’] >> rw [SUBSET_UNION])
 >> Rewr'
 >> Know ‘BT_paths M = BT_paths N’
 >- (MATCH_MP_TAC lameq_BT_paths_cong \\
     qexistsl_tac [‘X’, ‘r’] >> rw [SUBSET_UNION])
 >> Rewr'
 >> MATCH_MP_TAC BT_valid_paths_bnf
 >> qexistsl_tac [‘X’, ‘r’] >> art []
QED

(*---------------------------------------------------------------------------*
 *  subtree_equiv_lemma
 *---------------------------------------------------------------------------*)

Theorem FV_apply_Boehm_construction :
    !X Ms p r.
       FINITE X /\ p <> [] /\ 0 < r /\ Ms <> [] /\
       BIGUNION (IMAGE FV (set Ms)) SUBSET X UNION RANK r ==>
       !M. MEM M Ms ==>
           FV (apply (Boehm_construction X Ms p) M) SUBSET X UNION RANK r
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Q.X_GEN_TAC ‘N’
 >> DISCH_TAC
 >> UNBETA_TAC [Boehm_construction_def] “Boehm_construction X Ms p”
 >> qunabbrev_tac ‘X'’
 >> qabbrev_tac ‘Y = BIGUNION (IMAGE FV (set Ms))’
 >> ‘FINITE Y’ by (rw [Abbr ‘Y’] >> rw [])
 >> simp [Boehm_apply_APPEND]
 (* eliminate p3 *)
 >> simp [Abbr ‘p3’, Boehm_apply_MAP_rightctxt']
 >> reverse CONJ_TAC
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs0’ \\
     rw [Abbr ‘xs’, LIST_TO_SET_DROP] \\
     Suff ‘set vs0 SUBSET RANK r’ >- SET_TAC [] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ >> rw [ROW_SUBSET_RANK] \\
     qunabbrev_tac ‘vs0’ \\
     MATCH_MP_TAC RNEWS_SUBSET_ROW >> rw [])
 (* eliminate p2 *)
 >> qabbrev_tac ‘sub = \k. GENLIST (\i. (P i,y i)) k’
 >> Know ‘!t. apply p2 t = t ISUB sub k’
 >- (simp [Abbr ‘p2’, Abbr ‘sub’] \\
     Q.SPEC_TAC (‘k’, ‘j’) \\
     Induct_on ‘j’ >- rw [] \\
     rw [GENLIST, REVERSE_SNOC, ISUB_SNOC])
 >> DISCH_TAC
 >> simp []
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV (apply p1 N) UNION FVS (sub k)’
 >> CONJ_TAC >- rw [FV_ISUB_upperbound]
 >> Know ‘!j. DOM (sub j) = IMAGE y (count j) /\ FVS (sub j) = {}’
 >- (simp [Abbr ‘sub’] \\
     Induct_on ‘j’ >- rw [DOM_DEF, FVS_DEF] \\
     rw [GENLIST, REVERSE_SNOC, DOM_DEF, FVS_DEF, COUNT_SUC, DOM_SNOC, FVS_SNOC]
     >- SET_TAC [] \\
     rw [Abbr ‘P’, FV_permutator])
 >> DISCH_TAC
 >> simp []
 (* eliminate p1 *)
 >> simp [Abbr ‘p1’, Boehm_apply_MAP_rightctxt']
 >> reverse CONJ_TAC
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs0’ \\
     rw [Abbr ‘vs’, LIST_TO_SET_TAKE] \\
     Suff ‘set vs0 SUBSET RANK r’ >- SET_TAC [] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ >> rw [ROW_SUBSET_RANK] \\
     qunabbrev_tac ‘vs0’ \\
     MATCH_MP_TAC RNEWS_SUBSET_ROW >> rw [])
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘Y’ >> art []
 >> rw [Abbr ‘Y’, SUBSET_DEF]
 >> Q.EXISTS_TAC ‘FV N’ >> art []
 >> Q.EXISTS_TAC ‘N’ >> art []
QED

Theorem subtree_equiv_lemma_explicit'[local] =
        subtree_equiv_lemma_explicit |> SIMP_RULE std_ss [LET_DEF]

Theorem subtree_equiv_lemma :
    !X Ms p r.
       FINITE X /\ p <> [] /\ 0 < r /\ Ms <> [] /\
       BIGUNION (IMAGE FV (set Ms)) SUBSET X UNION RANK r /\
       EVERY (\M. p IN ltree_paths (BT' X M r)) Ms ==>
      ?pi. Boehm_transform pi /\ EVERY is_ready' (apply pi Ms) /\
           EVERY (\M. FV M SUBSET X UNION RANK r) (apply pi Ms) /\
           EVERY (\M. p IN ltree_paths (BT' X M r)) (apply pi Ms) /\
          (!q M. MEM M Ms /\ q <<= p ==>
                (solvable (subterm' X M q r) <=>
                 solvable (subterm' X (apply pi M) q r))) /\
          (!q M N. MEM M Ms /\ MEM N Ms /\ q <<= p ==>
                  (subtree_equiv X M N q r <=>
                   subtree_equiv X (apply pi M) (apply pi N) q r))
Proof
    rpt STRIP_TAC
 >> Know ‘EVERY (\M. subterm X M p r <> NONE) Ms’
 >- (POP_ASSUM MP_TAC \\
     rw [EVERY_MEM] \\
     Know ‘FV M SUBSET X UNION RANK r’
     >- (Q_TAC (TRANS_TAC SUBSET_TRANS)
               ‘BIGUNION (IMAGE FV (set Ms))’ >> art [] \\
         rw [SUBSET_DEF] \\
         Q.EXISTS_TAC ‘FV M’ >> art [] \\
         Q.EXISTS_TAC ‘M’ >> art []) >> DISCH_TAC \\
     METIS_TAC [BT_ltree_paths_thm])
 >> DISCH_TAC
 >> Q.EXISTS_TAC ‘Boehm_construction X Ms p’
 >> Suff ‘EVERY (\M. FV M SUBSET X UNION RANK r)
                (MAP (apply (Boehm_construction X Ms p)) Ms)’
 >- (Rewr \\
     MATCH_MP_TAC subtree_equiv_lemma_explicit' >> art [])
 >> simp [EVERY_MEM, MEM_MAP]
 >> rw []
 >> irule FV_apply_Boehm_construction >> art []
QED

(* Definition 10.3.10 (iii) and (iv) [1, p.251]

   NOTE: The purpose of X is to make sure all terms in Ms share the same exclude
         set (and thus perhaps also the same initial binding list).
 *)
Definition agree_upto_def :
    agree_upto X Ms p r <=>
    !q M N. q <<= p /\ q <> p /\ MEM M Ms /\ MEM N Ms ==> subtree_equiv X M N q r
End

Theorem agree_upto_two :
    !X M N p r. agree_upto X [M; N] p r <=>
               !q. q <<= p /\ q <> p ==> subtree_equiv X M N q r
Proof
    rw [agree_upto_def]
 >> EQ_TAC >> rw [] >> rw []
 >> rw [Once subtree_equiv_comm]
QED

(* NOTE: subtree_equiv_lemma and this theorem together implies the original
   agree_upto_lemma (see below).
 *)
Theorem subtree_equiv_imp_agree_upto :
    !X Ms p r pi.
      (!q M N. q <<= p /\ MEM M Ms /\ MEM N Ms /\
               subtree_equiv X M N q r ==>
               subtree_equiv X (apply pi M) (apply pi N) q r) /\
       agree_upto X Ms p r ==> agree_upto X (apply pi Ms) p r
Proof
    RW_TAC std_ss [agree_upto_def, MEM_MAP]
 >> LAST_X_ASSUM MATCH_MP_TAC >> art []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

(* Lemma 10.3.11 [1. p.251]

   NOTE: This theorem is weaker than subtree_equiv_lemma, but is tailored to
   prove [agree_upto_thm].
 *)
Theorem agree_upto_lemma :
    !X Ms p r.
       FINITE X /\ Ms <> [] /\ p <> [] /\ 0 < r /\ agree_upto X Ms p r /\
      (!M. MEM M Ms ==> FV M SUBSET X UNION RANK r) /\
      (!M. MEM M Ms ==> p IN ltree_paths (BT' X M r)) ==>
       ?pi. Boehm_transform pi /\
           (!M. MEM M Ms ==> is_ready' (apply pi M)) /\
            agree_upto X (apply pi Ms) p r /\
           (!M. MEM M Ms ==> (solvable (subterm' X M p r) <=>
                              solvable (subterm' X (apply pi M) p r))) /\
           (!M N. MEM M Ms /\ MEM N Ms ==>
                 (subtree_equiv X M N p r <=>
                  subtree_equiv X (apply pi M) (apply pi N) p r)) /\
           (!M. MEM M Ms ==> FV (apply pi M) SUBSET X UNION RANK r) /\
           (!M. MEM M Ms ==> p IN ltree_paths (BT' X (apply pi M) r))
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘Ms’, ‘p’, ‘r’] subtree_equiv_lemma)
 >> simp [BIGUNION_IMAGE_SUBSET, EVERY_MEM, MEM_MAP]
 >> STRIP_TAC
 >> Q.EXISTS_TAC ‘pi’ >> rw []
 >| [ (* goal 1 (of 4): is_ready' *)
      FIRST_X_ASSUM MATCH_MP_TAC \\
      Q.EXISTS_TAC ‘M’ >> art [],
      (* goal 2 (of 4): agree_upto *)
      MATCH_MP_TAC subtree_equiv_imp_agree_upto >> rw [] \\
      METIS_TAC [],
      (* goal 3 (of 4) *)
      FIRST_X_ASSUM MATCH_MP_TAC \\
      Q.EXISTS_TAC ‘M’ >> art [],
      (* goal 4 (of 4) *)
      FIRST_X_ASSUM MATCH_MP_TAC \\
      Q.EXISTS_TAC ‘M’ >> art [] ]
QED

(* Definition 10.3.10 (ii) [1, p.251]

   NOTE: This definition now assumes ’p IN ltree_paths (BT' X M r)’.
 *)
Definition faithful_def :
    faithful p X Ms pi r <=>
        (!M. MEM M Ms ==> (p IN BT_valid_paths M <=> solvable (apply pi M))) /\
         !M N. MEM M Ms /\ MEM N Ms ==>
              (subtree_equiv X M N p r <=>
               equivalent (apply pi M) (apply pi N))
End

Theorem faithful_two :
    !X M N p r pi.
       faithful p X [M; N] pi r <=>
         (p IN BT_valid_paths M <=> solvable (apply pi M)) /\
         (p IN BT_valid_paths N <=> solvable (apply pi N)) /\
         (subtree_equiv X M N p r <=> equivalent (apply pi M) (apply pi N))
Proof
    rpt STRIP_TAC
 >> EQ_TAC >> rw [faithful_def] >> rw []
 >> simp [Once subtree_equiv_comm, Once equivalent_comm]
QED

Overload faithful' = “faithful []”

Theorem faithful' :
    !X Ms pi r. FINITE X /\ 0 < r /\
               (!M. MEM M Ms ==> FV M SUBSET X UNION RANK r) ==>
      (faithful' X Ms pi r <=>
        (!M. MEM M Ms ==> (solvable M <=> solvable (apply pi M))) /\
         !M N. MEM M Ms /\ MEM N Ms ==>
              (equivalent (apply pi M) (apply pi N) <=> equivalent M N))
Proof
    rw [faithful_def]
 >> Suff ‘!M N. MEM M Ms /\ MEM N Ms ==>
               (subtree_equiv X M N [] r <=> equivalent M N)’
 >- METIS_TAC []
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC subtree_equiv_alt_equivalent >> rw []
QED

Theorem faithful_two' :
    !X Ms pi r.
       FINITE X /\ FV M UNION FV N SUBSET X UNION RANK r /\ 0 < r ==>
      (faithful' X [M; N] pi r <=>
         (solvable M <=> solvable (apply pi M)) /\
         (solvable N <=> solvable (apply pi N)) /\
         (equivalent (apply pi M) (apply pi N) <=> equivalent M N))
Proof
    rw [UNION_SUBSET]
 >> MP_TAC (Q.SPECL [‘X’, ‘[M; N]’, ‘pi’, ‘r’] faithful')
 >> simp []
 >> impl_tac >- METIS_TAC []
 >> Rewr'
 >> EQ_TAC >> rw [] >> rw []
 >> simp [Once equivalent_comm]
 >> simp [Once equivalent_comm]
QED

(* Proposition 10.3.13 [1, p.253]

   NOTE: In the base case ‘p = []’, terms in Ms are either all solvable or
   all unsolvable. In the induction case, however, p IN BT_paths M, p <> []
   implies M solvable.
 *)
Theorem agree_upto_thm :
    !X p Ms r. FINITE X /\ Ms <> [] /\ 0 < r /\
              (!M. MEM M Ms ==> FV M SUBSET X UNION RANK r) /\
              (!M. MEM M Ms ==> p IN ltree_paths (BT' X M r)) /\
               agree_upto X Ms p r ==>
               ?pi. Boehm_transform pi /\ faithful p X Ms pi r
Proof
    Q.X_GEN_TAC ‘X’
 >> Induct_on ‘p’
 >- (rpt STRIP_TAC >> Q.EXISTS_TAC ‘[]’ >> rw [faithful'])
 (* stage work *)
 >> rw [faithful_def]
 (* trivial case: all unsolvable *)
 >> Cases_on ‘!M. MEM M Ms ==> unsolvable M’
 >- (Q.EXISTS_TAC ‘[]’ \\
     reverse (rw [])
     >- (rw [equivalent_of_unsolvables] \\
         rw [subtree_equiv_def, BT_of_unsolvables]) \\
     MP_TAC (Q.SPECL [‘X’, ‘M’, ‘r’] BT_valid_paths_thm') >> rw [] \\
     Know ‘subterm X M (h::p) r = NONE <=> h::p NOTIN ltree_paths (BT' X M r)’
     >- (Suff ‘h::p IN ltree_paths (BT' X M r) <=> subterm X M (h::p) r <> NONE’
         >- PROVE_TAC [] \\
         MATCH_MP_TAC BT_ltree_paths_thm >> simp []) >> Rewr' \\
     STRONG_DISJ_TAC \\
     Suff ‘solvable M’ >- METIS_TAC [] \\
     MATCH_MP_TAC ltree_paths_imp_solvable \\
     qexistsl_tac [‘h::p’, ‘X’, ‘r’] >> simp [])
 (* one is solvable, all are solvable *)
 >> Know ‘!M. MEM M Ms ==> solvable M’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC ltree_paths_imp_solvable \\
     qexistsl_tac [‘h::p’, ‘X’, ‘r’] >> simp [GSYM BT_paths_thm])
 >> POP_ASSUM K_TAC >> DISCH_TAC
 (* applying agree_upto_lemma *)
 >> MP_TAC (Q.SPECL [‘X’, ‘Ms’, ‘h::p’, ‘r’] agree_upto_lemma) >> rw []
 (* p0 is asserted *)
 >> rename1 ‘Boehm_transform p0’
 >> fs [is_ready_alt']
 (* decomposing Ms *)
 >> qabbrev_tac ‘k = LENGTH Ms’
 >> ‘k <> 0’ by rw [Abbr ‘k’, LENGTH_NIL]
 >> qabbrev_tac ‘M = \i. EL i Ms’
 >> Know ‘!P. (!N. MEM N Ms ==> P N) <=> !i. i < k ==> P (M i)’
 >- (Q.X_GEN_TAC ‘P’ \\
     reverse EQ_TAC >> rw [MEM_EL] >- simp [] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘i’ >> art [])
 >> DISCH_THEN (fs o wrap)
 >> qabbrev_tac ‘M1 = \i. principle_hnf (apply p0 (M i))’
 >> Know ‘!i. i < k ==> ?y Ns. M1 i = VAR y @* Ns /\ EVERY (\e. y # e) Ns’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> solvable (apply p0 (M i)) /\ _’ drule \\
     rw [Abbr ‘M1’] \\
     qexistsl_tac [‘y’, ‘Ns’] >> art [] \\
     rw [principle_hnf_thm', hnf_appstar])
 >> DISCH_TAC
 (* NOTE: take the head variable and children terms from ‘N 0’ *)
 >> Know ‘?y Ns. M1 0 = VAR y @* Ns’
 >- (POP_ASSUM (MP_TAC o Q.SPEC ‘0’) >> rw [] \\
     qexistsl_tac [‘y’, ‘Ns’] >> art [])
 >> STRIP_TAC
 >> qabbrev_tac ‘m = LENGTH Ns’
 >> Know ‘!i. i < k ==> ?Ns. M1 i = VAR y @* Ns /\ EVERY (\e. y # e) Ns /\
                             LENGTH Ns = m’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> ?y Ns. P’ drule >> rw [] \\
     Q.EXISTS_TAC ‘Ns'’ \\
     Suff ‘y = y' /\ LENGTH Ns' = m’ >- rw [] \\
     Cases_on ‘i = 0’ >- fs [] \\
     FULL_SIMP_TAC std_ss [agree_upto_def] \\
     Q.PAT_X_ASSUM ‘!q M N. q <<= h::p /\ q <> h::p /\
                            MEM M (apply p0 Ms) /\ _ ==> _’
       (MP_TAC o Q.SPECL [‘[]’, ‘apply p0 ((M :num -> term) 0)’,
                                ‘apply p0 ((M :num -> term) i)’]) \\
     simp [subtree_equiv_def, MEM_MAP] \\
     impl_tac
     >- (CONJ_TAC >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           Q.EXISTS_TAC ‘M 0’ >> simp [MEM_EL] \\
           Q.EXISTS_TAC ‘0’ >> rw [],
           (* goal 2 (of 2) *)
           Q.EXISTS_TAC ‘M i’ >> simp [MEM_EL] \\
           Q.EXISTS_TAC ‘i’ >> rw [] ]) \\
     Know ‘BT' X (apply p0 (M 0)) r = BT' X (M1 0) r’
     >- (SIMP_TAC std_ss [Once EQ_SYM_EQ, Abbr ‘M1’] \\
         MATCH_MP_TAC BT_of_principle_hnf >> simp []) >> Rewr' \\
     Know ‘BT' X (apply p0 (M i)) r = BT' X (M1 i) r’
     >- (SIMP_TAC std_ss [Once EQ_SYM_EQ, Abbr ‘M1’] \\
         MATCH_MP_TAC BT_of_principle_hnf >> simp []) >> Rewr' \\
     REWRITE_TAC [BT_def] \\
     NTAC 2 (simp [Once ltree_unfold, BT_generator_def, LMAP_fromList,
                   ltree_el_def]) \\
     simp [head_equivalent_def])
 >> simp [EXT_SKOLEM_THM']
 >> STRIP_TAC (* this assert f as the children function of all Ms *)
 >> Q.PAT_X_ASSUM ‘!i. i < k ==> ?y Ns. _’ K_TAC
 >> Know ‘Ns = f 0’ (* eliminate Ns by f *)
 >- (POP_ASSUM (MP_TAC o Q.SPEC ‘0’) >> rw [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> ‘!i. i < k ==> solvable (apply p0 (M i))’ by PROVE_TAC []
 >> Q.PAT_X_ASSUM ‘!i. i < k ==> solvable (apply p0 (M i)) /\ _’ K_TAC
 >> Know ‘!i. i < k ==> apply p0 (M i) -h->* VAR y @* f i’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> M1 i = VAR y @* f i /\ _’ drule \\
     simp [Abbr ‘M1’, principle_hnf_thm'])
 >> DISCH_TAC
 (* Now we use ‘h::p IN BT_paths (apply p0 (M i))’ (and ‘M 0’) to show that
   ‘h < m’, as otherwise p1 (the selector) cannot be properly defined.
  *)
 >> Know ‘h < m’
 >- (Q.PAT_X_ASSUM ‘!i. i < k ==> h::p IN ltree_paths (BT' X (apply p0 (M i)) r)’
       (MP_TAC o Q.SPEC ‘0’) >> simp [] \\
     MP_TAC (Q.SPECL [‘X’, ‘apply p0 ((M :num -> term) 0)’, ‘r’ ] BT_paths_thm) \\
     simp [] >> DISCH_THEN K_TAC \\
     Know ‘BT' X (apply p0 (M 0)) r = BT' X (M1 0) r’
     >- (SIMP_TAC std_ss [Once EQ_SYM_EQ, Abbr ‘M1’] \\
         MATCH_MP_TAC BT_of_principle_hnf >> simp []) >> Rewr' \\
     Q.PAT_X_ASSUM ‘M1 0 = _’ (REWRITE_TAC o wrap) \\
     simp [BT_def, Once ltree_unfold, BT_generator_def, LMAP_fromList,
           ltree_paths_alt_ltree_el, ltree_el_def] \\
     simp [GSYM BT_def, LNTH_fromList, MAP_MAP_o] \\
     Cases_on ‘h < m’ >> rw [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘M1 0 = _’ K_TAC
 (* p1 is defined as a selector *)
 >> qabbrev_tac ‘p1 = [[selector h m/y]]’
 >> ‘Boehm_transform p1’ by rw [Boehm_transform_def, Abbr ‘p1’]
 >> Know ‘!i. i < k ==> apply (p1 ++ p0) (M i) -h->* EL h (f i)’
 >- (rw [Boehm_transform_APPEND, Abbr ‘p1’] \\
     MATCH_MP_TAC hreduce_TRANS \\
     Q.EXISTS_TAC ‘[selector h m/y] (VAR y @* f i)’ \\
     CONJ_TAC
     >- (MATCH_MP_TAC hreduce_substitutive \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> M1 i = VAR y @* f i /\ _’ drule \\
         simp [Abbr ‘M1’, principle_hnf_thm']) \\
     simp [appstar_SUB] \\
     Know ‘MAP [selector h m/y] (f i) = f i’
     >- (rw [Once LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC lemma14b \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> M1 i = VAR y @* f i /\ _’ drule \\
         rw [EVERY_MEM] \\
         POP_ASSUM MATCH_MP_TAC >> rw [EL_MEM]) >> Rewr' \\
     MATCH_MP_TAC hreduce_selector >> rw [])
 >> DISCH_TAC
 (* redefine Ns as the h-subterms of Ms

    NOTE: So far we don't know if any “EL h (f i)” is solvable, thus it's not
    sure whether “principle_hnf (apply (p1 ++ p0) (M i)) = EL h (f i)”.
  *)
 >> qabbrev_tac ‘Ns = GENLIST (EL h o f) k’
 >> ‘LENGTH Ns = k’ by rw [Abbr ‘Ns’, LENGTH_GENLIST]
 >> Know ‘!i. i < k ==> MEM (EL h (f i)) Ns’
 >- (rw [Abbr ‘Ns’, MEM_GENLIST] \\
     Q.EXISTS_TAC ‘i’ >> art [])
 >> DISCH_TAC
 (* proving one antecedent of IH *)
 >> Know ‘agree_upto X Ns p (SUC r)’
 >- (fs [agree_upto_def] \\
     rw [Abbr ‘Ns’, MEM_GENLIST] \\
     NTAC 2 (POP_ASSUM MP_TAC) \\
     rename1 ‘a < k ==> b < k ==> _’ >> NTAC 2 STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!q M N. q <<= h::p /\ q <> h::p /\ MEM M (apply p0 Ms) /\ _ ==> _’
       (MP_TAC o Q.SPECL [‘h::q’, ‘apply p0 ((M :num -> term) a)’,
                                  ‘apply p0 ((M :num -> term) b)’]) \\
     simp [MEM_MAP] \\
     impl_tac
     >- (CONJ_TAC >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           Q.EXISTS_TAC ‘M a’ >> rw [EL_MEM, Abbr ‘M’],
           (* goal 2 (of 2) *)
           Q.EXISTS_TAC ‘M b’ >> rw [EL_MEM, Abbr ‘M’] ]) \\
     simp [subtree_equiv_def] \\
     Know ‘BT' X (apply p0 (M a)) r = BT' X (M1 a) r’
     >- (SIMP_TAC std_ss [Once EQ_SYM_EQ, Abbr ‘M1’] \\
         MATCH_MP_TAC BT_of_principle_hnf >> simp []) >> Rewr' \\
     Know ‘BT' X (apply p0 (M b)) r = BT' X (M1 b) r’
     >- (SIMP_TAC std_ss [Once EQ_SYM_EQ, Abbr ‘M1’] \\
         MATCH_MP_TAC BT_of_principle_hnf >> simp []) >> Rewr' \\
     simp [] \\
    ‘!i. solvable (VAR y @* f i)’ by rw [] \\
    ‘!i. principle_hnf (VAR y @* f i) = VAR y @* f i’ by rw [] \\
     Q_TAC (UNBETA_TAC [BT_def, BT_generator_def, Once ltree_unfold,
                        LMAP_fromList]) ‘BT' X (VAR y @* f a) r’ \\
     simp [Abbr ‘M0’, GSYM appstar_APPEND, LNTH_fromList, ltree_el_def,
           GSYM BT_def, Abbr ‘y'’, Abbr ‘Ms'’, Abbr ‘n’, Abbr ‘l’, Abbr ‘M1'’,
           Abbr ‘vs’, EL_MAP] \\
     Q_TAC (UNBETA_TAC [BT_def, BT_generator_def, Once ltree_unfold,
                        LMAP_fromList]) ‘BT' X (VAR y @* f b) r’ \\
     simp [Abbr ‘M0’, GSYM appstar_APPEND, LNTH_fromList, ltree_el_def,
           GSYM BT_def, Abbr ‘y'’, Abbr ‘Ms'’, Abbr ‘n’, Abbr ‘l’, Abbr ‘M1'’,
           Abbr ‘vs’, EL_MAP])
 >> DISCH_TAC
 >> qabbrev_tac ‘pi' = p1 ++ p0’
 >> ‘Boehm_transform pi'’ by rw [Abbr ‘pi'’, Boehm_transform_APPEND]
 >> Know ‘agree_upto X (apply pi' Ms) p (SUC r)’
 >- (Q.PAT_X_ASSUM ‘agree_upto X Ns p (SUC r)’ MP_TAC \\
     rw [agree_upto_def, MEM_MAP, Abbr ‘Ns’, MEM_GENLIST, MEM_EL] \\
     Know ‘subtree_equiv X (apply pi' (M n)) (apply pi' (M n')) q (SUC r) <=>
           subtree_equiv X (EL h (f n)) (EL h (f n')) q (SUC r)’
     >- (MATCH_MP_TAC hreduce_subtree_equiv_cong >> simp []) >> Rewr' \\
     FIRST_X_ASSUM MATCH_MP_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC ‘n’ >> art [],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC ‘n'’ >> art [] ])
 >> DISCH_TAC
 (* proving antecedents of IH *)
 >> Know ‘!N. MEM N Ns ==> FV N SUBSET X UNION RANK (SUC r)’
 >- (simp [MEM_EL, Abbr ‘Ns’] \\
     NTAC 2 STRIP_TAC \\
     POP_ORW >> simp [EL_GENLIST] \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘apply p0 (M n)’, ‘M1 n’, ‘0’, ‘m’, ‘[]’, ‘M1 n’] \\
     simp [])
 >> DISCH_TAC
 >> Know ‘!N. MEM N Ns ==> p IN ltree_paths (BT' X N (SUC r))’
 >- (NTAC 2 STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!N. MEM N Ns ==> FV N SUBSET X UNION RANK (SUC r)’ drule \\
     POP_ASSUM MP_TAC \\
     simp [MEM_EL, Abbr ‘Ns’] \\
     STRIP_TAC >> POP_ORW \\
     simp [EL_GENLIST] >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> h::p IN ltree_paths (BT' X (apply p0 (M i)) r)’
       (MP_TAC o Q.SPEC ‘n’) >> simp [] \\
     MP_TAC (Q.SPECL [‘X’, ‘apply p0 ((M :num -> term) n)’, ‘r’] BT_paths_thm) \\
     simp [] >> DISCH_THEN K_TAC \\
     MP_TAC (Q.SPECL [‘X’, ‘EL h (f (n :num))’, ‘SUC r’] BT_paths_thm) \\
     simp [] >> DISCH_THEN K_TAC \\
     Know ‘BT' X (apply p0 (M n)) r = BT' X (M1 n) r’
     >- (SIMP_TAC std_ss [Once EQ_SYM_EQ, Abbr ‘M1’] \\
         MATCH_MP_TAC BT_of_principle_hnf >> simp []) >> Rewr' \\
    ‘!i. solvable (VAR y @* f i)’ by rw [] \\
    ‘!i. principle_hnf (VAR y @* f i) = VAR y @* f i’ by rw [] \\
     Q_TAC (UNBETA_TAC [BT_def, Once ltree_unfold, BT_generator_def])
           ‘BT' X (M1 (n :num)) r’ \\
     simp [LMAP_fromList, ltree_paths_alt_ltree_el, ltree_el_def, GSYM BT_def] \\
     simp [Abbr ‘M0’, GSYM appstar_APPEND, LNTH_fromList, EL_MAP,
           Abbr ‘y'’, Abbr ‘Ms'’, Abbr ‘n'’, Abbr ‘l’, Abbr ‘M1'’, Abbr ‘vs’])
 >> DISCH_TAC
 >> Know ‘!N. MEM N (apply pi' Ms) ==> p IN ltree_paths (BT' X N (SUC r))’
 >- (rw [MEM_MAP, MEM_EL] \\
     Know ‘BT' X (apply pi' (M n)) (SUC r) = BT' X (EL h (f n)) (SUC r)’
     >- (MATCH_MP_TAC hreduce_BT_cong >> simp []) >> Rewr' \\
     FIRST_X_ASSUM MATCH_MP_TAC >> simp [])
 >> DISCH_TAC
 >> Know ‘!N. MEM N (apply pi' Ms) ==> FV N SUBSET X UNION RANK (SUC r)’
 >- (rw [MEM_MAP, MEM_EL, Abbr ‘pi'’, Boehm_apply_APPEND, Abbr ‘p1’] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV (apply p0 (M n))’ \\
     CONJ_TAC >- (MATCH_MP_TAC FV_SUB_SUBSET >> simp [closed_def]) \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘X UNION RANK r’ >> simp [] \\
     Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
     simp [RANK_MONO])
 >> DISCH_TAC
 (* using IH *)
 >> Q.PAT_X_ASSUM
      ‘!Ms' r'. Ms' <> [] /\ 0 < r' /\ _ /\ _ /\ agree_upto X Ms' p r' ==>
               ?pi. Boehm_transform pi /\ faithful p X Ms' pi r'’
      (MP_TAC o Q.SPECL [‘apply pi' Ms’, ‘SUC r’])
 >> simp [faithful_def]
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘p2’ STRIP_ASSUME_TAC)
 >> qabbrev_tac ‘pi = p2 ++ p1 ++ p0’
 >> Q.EXISTS_TAC ‘pi’
 >> CONJ_TAC (* Boehm_transform pi *)
 >- (qunabbrev_tac ‘pi’ \\
     MATCH_MP_TAC Boehm_transform_APPEND >> art [] \\
     MATCH_MP_TAC Boehm_transform_APPEND >> art [])
 >> simp [Abbr ‘pi’, GSYM APPEND_ASSOC]
 >> REWRITE_TAC [Boehm_apply_APPEND]
 >> Know ‘!i. i < k ==> MEM (apply pi' (M i)) (apply pi' Ms)’
 >- (rw [MEM_MAP] \\
     Q.EXISTS_TAC ‘M i’ >> simp [EL_MEM, Abbr ‘M’])
 >> DISCH_TAC
 (* stage work, the 2nd part is easier following textbook *)
 >> reverse CONJ_TAC
 >- (simp [MEM_EL] \\
     qx_genl_tac [‘t1’, ‘t2’] (* temporary names, to be consumed soon *) \\
     ONCE_REWRITE_TAC [TAUT ‘P /\ Q ==> R <=> P ==> Q ==> R’] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘a’ STRIP_ASSUME_TAC) \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘b’ STRIP_ASSUME_TAC) \\
     Q.PAT_X_ASSUM ‘_ = M a’ (ONCE_REWRITE_TAC o wrap) \\
     Q.PAT_X_ASSUM ‘_ = M b’ (ONCE_REWRITE_TAC o wrap) \\
     qabbrev_tac ‘t1 = apply pi' (M a)’ \\
     qabbrev_tac ‘t2 = apply pi' (M b)’ \\
  (* eliminating “equivalent” *)
     Q.PAT_X_ASSUM ‘!M N. _ ==> (subtree_equiv X M N p (SUC r) <=>
                                 equivalent (apply p2 M) (apply p2 N))’
                   (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ] o
                    Q.SPECL [‘t1’, ‘t2’]) \\
     simp [Abbr ‘t1’, Abbr ‘t2’] >> DISCH_THEN K_TAC \\
     rpt (Q.PAT_X_ASSUM ‘agree_upto X _ _ _’ K_TAC) \\
  (* applying hreduce_subtree_equiv_cong *)
     Know ‘subtree_equiv X (apply p0 (M a)) (apply p0 (M b)) (h::p) r <=>
           subtree_equiv X (VAR y @* f a) (VAR y @* f b) (h::p) r’
     >- (MATCH_MP_TAC hreduce_subtree_equiv_cong >> simp []) >> Rewr' \\
     Know ‘subtree_equiv X (apply pi' (M a)) (apply pi' (M b)) p (SUC r) <=>
           subtree_equiv X (EL h (f a)) (EL h (f b)) p (SUC r)’
     >- (MATCH_MP_TAC hreduce_subtree_equiv_cong >> simp []) >> Rewr' \\
     simp [subtree_equiv_def] \\
    ‘!i. solvable (VAR y @* f i)’ by rw [] \\
    ‘!i. principle_hnf (VAR y @* f i) = VAR y @* f i’ by rw [] \\
     Q_TAC (UNBETA_TAC [BT_def, BT_generator_def, Once ltree_unfold,
                        LMAP_fromList, LET_DEF]) ‘BT' X (VAR y @* f a) r’ \\
     simp [GSYM BT_def, LMAP_fromList, ltree_el_def, LNTH_fromList, EL_MAP] \\
     Q_TAC (UNBETA_TAC [BT_def, BT_generator_def, Once ltree_unfold,
                        LMAP_fromList, LET_DEF]) ‘BT' X (VAR y @* f b) r’ \\
     simp [GSYM BT_def, LMAP_fromList, ltree_el_def, LNTH_fromList, EL_MAP])
 (* final goal *)
 >> rpt STRIP_TAC
 (* clean up all assumptions involving term equivalences *)
 >> rpt (Q.PAT_X_ASSUM ‘agree_upto X _ _ _’ K_TAC)
 >> qabbrev_tac ‘N = apply pi' (M i)’
 >> Q.PAT_X_ASSUM ‘!M. MEM M (apply pi' Ms) ==>
                      (p IN BT_valid_paths M <=> solvable (apply p2 M))’
                  (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ] o Q.SPEC ‘N’)
 >> simp [Abbr ‘N’]
 >> DISCH_THEN K_TAC
 >> qabbrev_tac ‘N = apply pi' (M i)’
 (* applying BT_valid_paths_thm' to turn the goal to subterm arguments *)
 >> Know ‘BT_valid_paths N = {p | subterm X N p (SUC r) <> NONE /\
                                  solvable (subterm' X N p (SUC r))}’
 >- (MATCH_MP_TAC BT_valid_paths_thm' >> simp [Abbr ‘N’])
 >> Rewr'
 >> Know ‘BT_valid_paths (M i) = {p | subterm X (M i) p r <> NONE /\
                                      solvable (subterm' X (M i) p r)}’
 >- (MATCH_MP_TAC BT_valid_paths_thm' >> simp [])
 >> Rewr'
 >> simp [Abbr ‘N’]
 (* applying BT_ltree_paths_thm *)
 >> ‘subterm X (M i) (h::p) r <> NONE’ by simp [GSYM BT_ltree_paths_thm]
 >> ‘subterm X (apply pi' (M i)) p (SUC r) <> NONE’
      by simp [GSYM BT_ltree_paths_thm]
 >> simp []
 (* applying hreduce_subterm_cong *)
 >> Know ‘subterm X (apply p0 (M i)) (h::p) r =
          subterm X (VAR y @* f i) (h::p) r’
 >- (MATCH_MP_TAC hreduce_subterm_cong >> simp [])
 >> Rewr'
 (* NOTE: To apply hreduce_subterm_cong to “subterm' X (apply pi' (M i)”,
   ‘p <> []’ is required. The case ‘p = []’ is trivial.
  *)
 >> Cases_on ‘p = []’
 >- (simp [] \\
     Know ‘solvable (apply pi' (M i)) <=> solvable (EL h (f i))’
     >- (MATCH_MP_TAC hreduce_solvable_cong >> simp []) >> Rewr' \\
     Suff ‘subterm' X (VAR y @* f i) [h] r = EL h (f i)’ >- rw [] \\
     rw [subterm_def])
 >> Know ‘subterm X (apply pi' (M i)) p (SUC r) =
          subterm X (EL h (f i)) p (SUC r)’
 >- (MATCH_MP_TAC hreduce_subterm_cong >> simp [])
 >> Rewr'
 >> Suff ‘subterm' X (VAR y @* f i) (h::p) r =
          subterm' X (EL h (f i)) p (SUC r)’ >- rw []
 >> ‘!i. solvable (VAR y @* f i)’ by rw []
 >> ‘!i. principle_hnf (VAR y @* f i) = VAR y @* f i’ by rw []
 >> Q_TAC (UNBETA_TAC [subterm_def]) ‘subterm X (VAR y @* f i) (h::p) r’
 >> simp []
QED

(*---------------------------------------------------------------------------*
 * Distinct beta-eta-NFs are not everywhere (subtree) equivalent
 *---------------------------------------------------------------------------*)

Theorem ltree_finite_BT_bnf :
    !X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\ bnf M ==>
            ltree_finite (BT' X M r)
Proof
    RW_TAC std_ss [BT_def]
 (* applying ltree_finite_by_unfolding *)
 >> irule ltree_finite_by_unfolding
 >> Q.EXISTS_TAC ‘\(M,r). FV M SUBSET X UNION RANK r /\ bnf M’
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC ‘size o FST’ (* size M, with r abandoned *)
 >> rpt GEN_TAC
 >> simp [every_LNTH, o_DEF]
 >> PairCases_on ‘seed’
 >> simp []
 >> NTAC 2 STRIP_TAC
 >> rename1 ‘FV N SUBSET X UNION RANK r'’
 >> ‘solvable N /\ hnf N’ by PROVE_TAC [bnf_solvable, bnf_hnf]
 >> Q.PAT_X_ASSUM ‘_ = (a,seeds)’ MP_TAC
 >> Q_TAC (UNBETA_TAC [BT_generator_of_hnf]) ‘BT_generator X (N,r')’
 >> STRIP_TAC
 >> POP_ASSUM (REWRITE_TAC o wrap o SYM)
 >> REWRITE_TAC [LFINITE_fromList]
 >> POP_ASSUM K_TAC (* SOME (vs,y) = a *)
 >> rpt GEN_TAC
 >> simp [LNTH_fromList, Abbr ‘l’, EL_MAP, Abbr ‘y’]
 >> STRIP_TAC >> rename1 ‘i < LENGTH Ms’
 >> POP_ASSUM (SIMP_TAC std_ss o wrap o SYM)
 (* decompose M0 by HNF_TAC *)
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r' :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV N)’ by PROVE_TAC [subterm_disjoint_lemma]
 >> Q_TAC (HNF_TAC (“N :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> Q.PAT_X_ASSUM ‘i < LENGTH Ms’ MP_TAC
 >> simp [Abbr ‘Ms’, GSYM CONJ_ASSOC]
 >> DISCH_TAC
 >> qabbrev_tac ‘m = LENGTH args’
 >> CONJ_TAC
 >- (MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘N’, ‘N’, ‘n’, ‘m’, ‘vs’, ‘M1’] \\
     simp [principle_hnf_reduce])
 >> reverse CONJ_TAC
 >- (simp [size_appstar] \\
     Suff ‘size (EL i args) <= SUM (MAP size args)’ >- rw [] \\
     MATCH_MP_TAC SUM_MAP_MEM_bound >> simp [EL_MEM])
 >> MATCH_MP_TAC hnf_children_bnf
 >> qexistsl_tac [‘vs’, ‘y’] >> art []
 >> Q.PAT_X_ASSUM ‘N = _’ (REWRITE_TAC o wrap o SYM)
 >> simp []
QED

Theorem ltree_finite_BT_has_bnf :
    !X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\ has_bnf M ==>
            ltree_finite (BT' X M r)
Proof
    rw [has_bnf_thm] >> rename1 ‘bnf N’
 >> ‘M == N’ by PROVE_TAC [betastar_lameq]
 >> ‘FV N SUBSET FV M’ by PROVE_TAC [betastar_FV_SUBSET]
 (* applying ltree_finite_BT_bnf *)
 >> Suff ‘BT' X M r = BT' X N r’
 >- (Rewr' \\
     MATCH_MP_TAC ltree_finite_BT_bnf >> art [] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M’ >> art [])
 (* applying lameq_BT_cong *)
 >> MATCH_MP_TAC lameq_BT_cong >> art []
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M’ >> art []
QED

Theorem ltree_finite_BT_has_benf :
    !X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\ has_benf M ==>
            ltree_finite (BT' X M r)
Proof
    rw [has_benf_has_bnf]
 >> MATCH_MP_TAC ltree_finite_BT_has_bnf >> art []
QED

Theorem ltree_finite_BT_benf :
    !X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\ benf M ==>
            ltree_finite (BT' X M r)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC ltree_finite_BT_has_benf
 >> rw [has_benf_def]
 >> Q.EXISTS_TAC ‘M’ >> rw [lameta_REFL]
QED

(* NOTE: All bottoms ($\bot$) are translated to “Omega” (Omega_def). If a term
   is bnf (or has_bnf), then all terms are solvable, and there's no bottom in
   the resulting Boehm tree.
 *)
Definition rose_to_term_def :
    rose_to_term =
    rose_reduce (\x args. case x of
                            SOME (vs,y) => LAMl vs (VAR y @* args)
                          | NONE => Omega)
End

(* NOTE: This assumes that the input Boehm tree is finite (ltree_finite). *)
Overload BT_to_term = “\t. rose_to_term (to_rose t)”

Theorem BT_to_term_def :
    !t. BT_to_term t =
          rose_reduce
            (\x args. case x of
                        NONE => Omega
                      | SOME (vs,y) => LAMl vs (VAR y @* args)) (to_rose t)
Proof
    rw [rose_to_term_def, o_DEF]
QED

(* Boehm trees of single variables are is involved as base cases of
   BT_expand lemmas.
 *)
Definition BT_VAR_def :
    BT_VAR y :boehm_tree = Branch (SOME ([],y)) LNIL
End

Theorem ltree_finite_BT_VAR[simp] :
    ltree_finite (BT_VAR x)
Proof
    rw [ltree_finite, IN_LSET, BT_VAR_def]
QED

Theorem BT_VAR_thm[simp] :
    BT' X (VAR v) r = BT_VAR v
Proof
    rw [BT_def, BT_generator_def, Once ltree_unfold]
 >> ‘principle_hnf (VAR v) = VAR v’
      by (MATCH_MP_TAC principle_hnf_reduce >> simp [])
 >> POP_ORW
 >> simp [BT_VAR_def]
QED

Theorem BT_to_term_BT_VAR[simp] :
    BT_to_term (BT_VAR v) = VAR v
Proof
   ‘ltree_finite (BT_VAR v)’ by rw [Once ltree_finite, IN_LSET]
 >> simp [BT_to_term_def, rose_node_to_rose, rose_children_to_rose,
          Once rose_reduce]
 >> simp [BT_VAR_def, ltree_node_def, ltree_children_def]
 >> simp [toList]
QED

Theorem ltree_paths_BT_VAR[simp] :
    ltree_paths (BT_VAR v) = {[]}
Proof
    rw [BT_VAR_def, ltree_paths_alt_ltree_el]
 >> rw [Once EXTENSION]
 >> Cases_on ‘x’ >> simp [ltree_el_def]
QED

(* This is the fundamental property of ‘to_term’ recovering the "original" term *)
Theorem BT_to_term_bnf :
    !X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\ bnf M ==>
            BT_to_term (BT' X M r) = M
Proof
    rw []
 >> Suff ‘!R M. (?r. FINITE X /\ FV M SUBSET X UNION RANK r /\ bnf M /\
                     R = to_rose (BT' X M r)) ==> rose_to_term R = M’
 >- (DISCH_THEN MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘r’ >> art [])
 >> NTAC 2 (POP_ASSUM K_TAC) (* only keep ‘FINITE X’ *)
 >> HO_MATCH_MP_TAC rose_tree_induction
 >> rw [rose_to_term_def, Once rose_reduce_def]
 >> POP_ASSUM (MP_TAC o AP_TERM “from_rose :BT_node rose_tree -> BT_node ltree”)
 >> ‘ltree_finite (BT' X M r)’ by PROVE_TAC [ltree_finite_BT_bnf]
 >> simp [from_rose_def, to_rose_def]
 (* stage work *)
 >> ‘solvable M’ by rw [bnf_solvable]
 >> simp [BT_def, BT_generator_def, Once ltree_unfold, Once ltree_finite]
 >> Q.PAT_X_ASSUM ‘ltree_finite _’
      (MP_TAC o REWRITE_RULE [BT_def, BT_generator_def, Once ltree_unfold])
 >> simp [IN_LSET, LNTH_fromList]
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> qabbrev_tac ‘m = LENGTH args’
 >> simp [GSYM BT_def, LMAP_fromList, MAP_MAP_o, o_DEF, Once ltree_finite, MEM_MAP]
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘a = SOME (vs,y)’ K_TAC
 >> Know ‘M = M0’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principle_hnf_bnf >> art [])
 >> DISCH_TAC
 >> rfs []
 >> Q.PAT_X_ASSUM ‘MAP from_rose ts = _’ MP_TAC
 >> simp [LIST_EQ_REWRITE, EL_MAP]
 >> rpt STRIP_TAC
 >> rename1 ‘i < m’
 >> Q.PAT_X_ASSUM ‘!R. MEM R ts ==> P’ (MP_TAC o Q.SPEC ‘EL i ts’)
 >> simp [EL_MEM]
 >> DISCH_THEN (MP_TAC o Q.SPEC ‘EL i args’)
 >> Suff ‘?r. FV (EL i args) SUBSET X UNION RANK r /\ bnf (EL i args) /\
              EL i ts = to_rose (BT' X (EL i args) r)’ >- rw []
 >> Q.EXISTS_TAC ‘SUC r’
 >> CONJ_TAC
 >- (MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [])
 >> CONJ_TAC (* bnf (EL x args) *)
 >- (MATCH_MP_TAC hnf_children_bnf \\
     qexistsl_tac [‘vs’, ‘y’] \\
     Q.PAT_X_ASSUM ‘M = _’ (REWRITE_TAC o wrap o SYM) \\
     simp [])
 >> simp [GSYM from_rose_11]
 >> Suff ‘from_rose (to_rose (BT' X (EL i args) (SUC r))) =
          BT' X (EL i args) (SUC r)’ >- rw [EL_MAP]
 >> MATCH_MP_TAC to_rose_def
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘EL i args’ >> rw [EL_MEM]
QED

Theorem BT_to_term_has_bnf :
    !X M M0 r. FINITE X /\ FV M SUBSET X UNION RANK r /\ has_bnf M /\
               M0 = BT_to_term (BT' X M r) ==> M -b->* M0 /\ bnf M0
Proof
    rpt GEN_TAC
 >> REWRITE_TAC [has_bnf_thm]
 >> STRIP_TAC
 >> ‘M == N’ by PROVE_TAC [betastar_lameq]
 >> Know ‘FV N SUBSET X UNION RANK r’
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M’ >> art [] \\
     MATCH_MP_TAC betastar_FV_SUBSET >> art [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘M0 = _’ (REWRITE_TAC o wrap)
 >> Know ‘BT' X M r = BT' X N r’
 >- (MATCH_MP_TAC lameq_BT_cong >> rw [])
 >> Rewr'
 >> Suff ‘BT_to_term (BT' X N r) = N’ >- rw []
 >> MATCH_MP_TAC BT_to_term_bnf >> art []
QED

Theorem BT_to_term_has_bnf' :
    !X M M0 r. FINITE X /\ FV M SUBSET X UNION RANK r /\ has_bnf M /\
               M0 = BT_to_term (BT' X M r) ==> M == M0 /\ bnf M0
Proof
    rpt GEN_TAC
 >> STRIP_TAC
 >> ‘M -b->* M0 /\ bnf M0’ by PROVE_TAC [BT_to_term_has_bnf]
 >> simp []
 >> MATCH_MP_TAC betastar_lameq >> rw []
QED

Theorem lameq_BT_cong_has_bnf :
    !X M N r.
        FINITE X /\ FV M SUBSET X UNION RANK r /\
        FV N SUBSET X UNION RANK r /\ has_bnf M /\ has_bnf N ==>
       (BT' X M r = BT' X N r <=> M == N)
Proof
    rpt STRIP_TAC
 >> reverse EQ_TAC >- rw [lameq_BT_cong]
 >> DISCH_THEN (MP_TAC o AP_TERM “BT_to_term”)
 >> simp []
 >> DISCH_TAC
 >> Know ‘BT_to_term (BT' X M r) == M’
 >- (MATCH_MP_TAC lameq_SYM \\
     MATCH_MP_TAC (cj 1 BT_to_term_has_bnf') \\
     qexistsl_tac [‘X’, ‘r’] >> art [])
 >> POP_ORW
 >> DISCH_TAC
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘BT_to_term (BT' X N r)’
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC lameq_SYM \\
     MATCH_MP_TAC (cj 1 BT_to_term_has_bnf') \\
     qexistsl_tac [‘X’, ‘r’] >> art [])
 >> MATCH_MP_TAC lameq_SYM >> art []
QED

Definition subtree_equal_def :
    subtree_equal X M N p r <=> ltree_el (BT' X M r) p = ltree_el (BT' X N r) p
End

Theorem distinct_bnf_imp_not_subtree_equal :
    !X M N r. FINITE X /\
              FV M UNION FV N SUBSET X UNION RANK r /\
              has_bnf M /\ has_bnf N /\ ~(M == N) /\
              ltree_paths (BT' X M r) = ltree_paths (BT' X N r)
          ==> ?p. p IN ltree_paths (BT' X M r) /\
                 ~subtree_equal X M N p r /\
                 !q. q <<= p /\ q <> p ==> subtree_equal X M N q r
Proof
    RW_TAC std_ss [subtree_equal_def, UNION_SUBSET]
 >> Q.PAT_X_ASSUM ‘~(M == N)’ MP_TAC
 >> Know ‘M == N <=> BT' X M r = BT' X N r’
 >- (MATCH_MP_TAC (GSYM lameq_BT_cong_has_bnf) >> art [])
 >> Rewr'
 >> rw [ltree_el_eqv]
 >> rename1 ‘ltree_el (BT' X M r) p0 <> ltree_el (BT' X N r) p0’
 >> qabbrev_tac ‘s = {p | p IN ltree_paths (BT' X N r) /\
                          ltree_el (BT' X M r) p <> ltree_el (BT' X N r) p}’
 >> Know ‘s <> {}’
 >- (rw [NOT_IN_EMPTY, Once EXTENSION, Abbr ‘s’] \\
     Q.EXISTS_TAC ‘p0’ >> art [] \\
     CCONTR_TAC \\
     gs [ltree_paths_alt_ltree_el, Once EXTENSION])
 >> DISCH_TAC
 (* applying WOP_measure *)
 >> Know ‘?b. b IN s /\ !c. c IN s ==> LENGTH b <= LENGTH c’
 >- (REWRITE_TAC [IN_APP] \\
     MATCH_MP_TAC WOP_measure \\
     simp [REWRITE_RULE [IN_APP] MEMBER_NOT_EMPTY])
 >> STRIP_TAC
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> POP_ASSUM K_TAC (* s <> [] *)
 >> rw [Abbr ‘s’]
 >> Q.EXISTS_TAC ‘b’ >> rw []
 >> Know ‘q IN ltree_paths (BT' X N r)’
 >- (MATCH_MP_TAC ltree_paths_inclusive \\
     Q.EXISTS_TAC ‘b’ >> art [])
 >> DISCH_TAC
 >> CCONTR_TAC
 >> Q.PAT_X_ASSUM ‘!c. P’ (MP_TAC o Q.SPEC ‘q’) >> rw []
 >> fs [IS_PREFIX_EQ_TAKE]
 >> Suff ‘n <> LENGTH b’ >- rw []
 >> CCONTR_TAC >> gs []
QED

(* Key bridging theorem between the old and new worlds *)
Theorem subtree_equal_alt_subtree_equiv :
    !X p M N r. FINITE X /\
                FV M UNION FV N SUBSET X UNION RANK r /\
                ltree_paths (BT' X M r) = ltree_paths (BT' X N r) ==>
               (subtree_equal X M N p r <=> subtree_equiv X M N p r)
Proof
    Q.X_GEN_TAC ‘X’
 >> REWRITE_TAC [UNION_SUBSET, GSYM CONJ_ASSOC]
 >> Induct_on ‘p’
 >- (rw [subtree_equal_def, subtree_equiv_def] \\
     POP_ASSUM MP_TAC \\
     Q_TAC (UNBETA_TAC [BT_def, BT_generator_def, Once ltree_unfold]) ‘BT' X M r’ \\
     Q_TAC (UNBETA_TAC [BT_def, BT_generator_def, Once ltree_unfold]) ‘BT' X N r’ >|
     [ (* goal 1 (of 4) *)
       simp [head_equivalent_def, ltree_el_def, LMAP_fromList, LLENGTH_fromList] \\
       rw [ltree_paths_alt_ltree_el, Once EXTENSION] \\
       fs [Abbr ‘l’, Abbr ‘l'’, GSYM BT_def, MAP_MAP_o, o_DEF] \\
       qunabbrevl_tac [‘vs’, ‘vs'’] \\
       Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’ \\
       Q_TAC (RNEWS_TAC (“vs' :string list”, “r :num”, “n' :num”)) ‘X’ \\
       simp [] \\
       EQ_TAC
       >- (STRIP_TAC >> art [] \\
          ‘n = n'’ by METIS_TAC [RNEWS_11'] \\
           simp []) \\
       Suff ‘LENGTH Ms = LENGTH Ms'’
       >- (rw [] >> METIS_TAC []) \\
       qabbrev_tac ‘m  = LENGTH Ms’ \\
       qabbrev_tac ‘m' = LENGTH Ms'’ \\
       CCONTR_TAC \\
      ‘m < m' \/ m' < m’ by rw [] >| (* 2 subgoals *)
       [ (* goal 1 (of 2) *)
         Q.PAT_X_ASSUM ‘!x. P’ (MP_TAC o Q.SPEC ‘[m]’) \\
         simp [ltree_el_def, LMAP_fromList, LLENGTH_fromList, LNTH_fromList,
               EL_MAP] \\
         simp [ltree_el],
         (* goal 2 (of 2) *)
         Q.PAT_X_ASSUM ‘!x. P’ (MP_TAC o Q.SPEC ‘[m']’) \\
         simp [ltree_el_def, LMAP_fromList, LLENGTH_fromList, LNTH_fromList,
               EL_MAP] \\
         simp [ltree_el] ],
       (* goal 2 (of 4) *)
       simp [head_equivalent_def, ltree_el_def, LMAP_fromList, LLENGTH_fromList],
       (* goal 3 (of 4) *)
       simp [head_equivalent_def, ltree_el_def, LMAP_fromList, LLENGTH_fromList],
       (* goal 4 (of 4) *)
       simp [head_equivalent_def, ltree_el_def, LMAP_fromList, LLENGTH_fromList] ])
 (* stage work *)
 >> rpt STRIP_TAC
 >> fs [subtree_equal_def, subtree_equiv_def]
 >> POP_ASSUM MP_TAC
 >> Q_TAC (UNBETA_TAC [BT_def, BT_generator_def, Once ltree_unfold]) ‘BT' X M r’
 >> Q_TAC (UNBETA_TAC [BT_def, BT_generator_def, Once ltree_unfold]) ‘BT' X N r’
 >| [ (* goal 1 (of 4) *)
      simp [head_equivalent_def, ltree_el_def, LMAP_fromList, LLENGTH_fromList,
            LNTH_fromList, Abbr ‘l’, Abbr ‘l'’, EL_MAP, GSYM BT_def,
            ltree_paths_alt_ltree_el, Once EXTENSION, MAP_MAP_o, o_DEF] \\
      DISCH_TAC \\
      qabbrev_tac ‘m  = LENGTH Ms’ \\
      qabbrev_tac ‘m' = LENGTH Ms'’ \\
      Know ‘m = m'’
      >- (CCONTR_TAC \\
         ‘m < m' \/ m' < m’ by rw [] >| (* 2 subgoals *)
          [ (* goal 1 (of 2) *)
            Q.PAT_X_ASSUM ‘!x. P’ (MP_TAC o Q.SPEC ‘[m]’) \\
            simp [ltree_el_def, LMAP_fromList, LLENGTH_fromList, LNTH_fromList,
                  EL_MAP] \\
            simp [ltree_el],
            (* goal 2 (of 2) *)
            Q.PAT_X_ASSUM ‘!x. P’ (MP_TAC o Q.SPEC ‘[m']’) \\
            simp [ltree_el_def, LMAP_fromList, LLENGTH_fromList, LNTH_fromList,
                  EL_MAP] \\
            simp [ltree_el] ]) >> DISCH_THEN (ASSUME_TAC o SYM) \\
      simp [] \\
      Cases_on ‘h < m’ >> simp [] \\
      FIRST_X_ASSUM MATCH_MP_TAC \\
      CONJ_TAC
      >- (MATCH_MP_TAC subterm_induction_lemma' \\
          qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
          simp [Abbr ‘m’, Once EQ_SYM_EQ] \\
          MATCH_MP_TAC hnf_children_size_alt \\
          qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘vs’, ‘M1’] >> simp []) \\
      CONJ_TAC
      >- (MATCH_MP_TAC subterm_induction_lemma' \\
          qexistsl_tac [‘N’, ‘M0'’, ‘n'’, ‘m'’, ‘vs'’, ‘M1'’] >> simp [] \\
          Q.PAT_X_ASSUM ‘m' = m’ (REWRITE_TAC o wrap o SYM) \\
          simp [Abbr ‘m'’, Once EQ_SYM_EQ] \\
          MATCH_MP_TAC hnf_children_size_alt \\
          qexistsl_tac [‘X’, ‘N’, ‘r’, ‘n'’, ‘vs'’, ‘M1'’] >> simp []) \\
      rw [ltree_paths_alt_ltree_el, Once EXTENSION] \\
      Q.PAT_X_ASSUM ‘!x. P’ (MP_TAC o Q.SPEC ‘h::x’) \\
      simp [ltree_el_def, LMAP_fromList, LNTH_fromList, EL_MAP],
      (* goal 2 (of 4) *)
      simp [head_equivalent_def, ltree_el_def, LMAP_fromList, LLENGTH_fromList,
            LNTH_fromList, Abbr ‘l’, EL_MAP, GSYM BT_def,
            ltree_paths_alt_ltree_el, Once EXTENSION, MAP_MAP_o, o_DEF],
      (* goal 3 (of 4) *)
      simp [head_equivalent_def, ltree_el_def, LMAP_fromList, LLENGTH_fromList,
            LNTH_fromList, Abbr ‘l’, EL_MAP, GSYM BT_def,
            ltree_paths_alt_ltree_el, Once EXTENSION, MAP_MAP_o, o_DEF],
      (* goal 4 (of 4) *)
      simp [head_equivalent_def, ltree_el_def, LMAP_fromList, LLENGTH_fromList] ]
QED

Theorem distinct_bnf_imp_not_subtree_equiv :
    !X M N r. FINITE X /\
              FV M UNION FV N SUBSET X UNION RANK r /\
              has_bnf M /\ has_bnf N /\ ~(M == N) /\
              ltree_paths (BT' X M r) = ltree_paths (BT' X N r)
          ==> ?p. p IN ltree_paths (BT' X M r) /\
                 ~subtree_equiv X M N p r /\
                 !q. q <<= p /\ q <> p ==> subtree_equiv X M N q r
Proof
    RW_TAC std_ss [GSYM subtree_equal_alt_subtree_equiv]
 >> POP_ASSUM (ASSUME_TAC o SYM)
 >> simp []
 >> MATCH_MP_TAC distinct_bnf_imp_not_subtree_equal >> art []
QED

Theorem distinct_bnf_imp_agree_upto :
    !X M N r. FINITE X /\
              FV M UNION FV N SUBSET X UNION RANK r /\
              has_bnf M /\ has_bnf N /\ ~(M == N) /\
              ltree_paths (BT' X M r) = ltree_paths (BT' X N r)
          ==> ?p. p IN ltree_paths (BT' X M r) /\
                 ~subtree_equiv X M N p r /\ agree_upto X [M; N] p r
Proof
    RW_TAC std_ss [agree_upto_two]
 >> POP_ASSUM (ASSUME_TAC o SYM)
 >> simp []
 >> MATCH_MP_TAC distinct_bnf_imp_not_subtree_equiv >> art []
QED

(*---------------------------------------------------------------------------*
 *  Separability of (two) lambda terms
 *---------------------------------------------------------------------------*)

Theorem separability_lemma0_case2[local] :
    !y args1 args2 k. 0 < k /\ LENGTH args1 = LENGTH args2 + k ==>
       !P Q. ?pi. Boehm_transform pi /\
                  apply pi (VAR y @* args1) == P /\
                  apply pi (VAR y @* args2) == Q
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘M1 = VAR y @* args1’
 >> qabbrev_tac ‘N1 = VAR y @* args2’
 >> qabbrev_tac ‘p  = LENGTH args1’
 >> qabbrev_tac ‘p' = LENGTH args2’
 >> qabbrev_tac ‘vs = NEWS (k + 1) (y INSERT FV P UNION FV Q)’
 >> ‘ALL_DISTINCT vs /\ DISJOINT (set vs) (y INSERT FV P UNION FV Q)’
      by rw [Abbr ‘vs’, NEWS_def]
 >> qabbrev_tac ‘a = HD vs’
 >> qabbrev_tac ‘bs = DROP 1 vs’
 >> Know ‘LENGTH bs + 1 = LENGTH vs /\ 1 < LENGTH vs’
 >- (‘LENGTH vs = k + 1’ by rw [Abbr ‘vs’, NEWS_def] \\
     rw [Abbr ‘bs’])
 >> STRIP_TAC
 >> ‘vs <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 (* p1 = ()a b_1 b_2 ... b_k *)
 >> qabbrev_tac ‘p1 = MAP rightctxt (REVERSE (MAP VAR vs))’
 >> ‘Boehm_transform p1’ by rw [Boehm_transform_def, Abbr ‘p1’, EVERY_MAP]
 >> ‘apply p1 M1 = VAR y @* (args1 ++ MAP VAR vs)’
      by (rw [Abbr ‘M1’, Abbr ‘p1’, Boehm_apply_MAP_rightctxt', appstar_APPEND])
 >> ‘apply p1 N1 = VAR y @* (args2 ++ MAP VAR vs)’
      by (rw [Abbr ‘N1’, Abbr ‘p1’, Boehm_apply_MAP_rightctxt', appstar_APPEND])
 (* p2 *)
 >> qabbrev_tac ‘Z = NEWS (p + 1) {}’
 >> ‘ALL_DISTINCT Z /\ LENGTH Z = p + 1’ by rw [Abbr ‘Z’, NEWS_def]
 >> ‘Z <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> qabbrev_tac ‘z = LAST Z’
 >> qabbrev_tac ‘p2 = [[LAMl Z (VAR z)/y]]’
 >> ‘Boehm_transform p2’ by rw [Boehm_transform_def, Abbr ‘p2’]
 >> Know ‘apply p2 (VAR y @* (args1 ++ MAP VAR vs)) == VAR a @* MAP VAR bs’
 >- (simp [Abbr ‘p2’, appstar_SUB] \\
     Know ‘MAP [LAMl Z (VAR z)/y] (MAP VAR vs) = MAP VAR vs’
     >- (rw [LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC lemma14b \\
         Q.PAT_X_ASSUM ‘DISJOINT (set vs) _’ MP_TAC \\
         rw [DISJOINT_ALT', MEM_EL] >> METIS_TAC []) >> Rewr' \\
     qabbrev_tac ‘args1' = MAP [LAMl Z (VAR z)/y] args1’ \\
     Know ‘LAMl Z (VAR z) = LAMl (FRONT Z) (LAM z (VAR z))’
     >- (REWRITE_TAC [GSYM LAMl_SNOC] \\
         Suff ‘SNOC z (FRONT Z) = Z’ >- Rewr \\
         qunabbrev_tac ‘z’ >> MATCH_MP_TAC SNOC_LAST_FRONT >> art []) >> Rewr' \\
     REWRITE_TAC [appstar_APPEND] \\
     qabbrev_tac ‘t :term = LAM z (VAR z)’ \\
     MATCH_MP_TAC lameq_TRANS >> Q.EXISTS_TAC ‘t @* MAP VAR vs’ \\
     CONJ_TAC >- (MATCH_MP_TAC lameq_appstar_cong \\
                  MATCH_MP_TAC lameq_LAMl_appstar_reduce \\
                  rw [Abbr ‘t’, Abbr ‘args1'’, LENGTH_FRONT]) \\
     qunabbrev_tac ‘t’ \\
     Know ‘MAP VAR vs = (VAR a::MAP VAR bs) :term list’
     >- (rw [Abbr ‘a’, Abbr ‘bs’, LIST_EQ_REWRITE, MAP_DROP] \\
         Cases_on ‘x’ >- rw [EL_MAP] \\
         rw [EL_MAP, EL_DROP, ADD1]) >> Rewr' \\
     rw [GSYM I_thm] \\
     MATCH_MP_TAC lameq_appstar_cong >> rw [lameq_I])
 >> DISCH_TAC
 >> qabbrev_tac ‘b0 = LAST bs’
 >> Know ‘apply p2 (VAR y @* (args2 ++ MAP VAR vs)) == VAR b0’
 >- (simp [Abbr ‘p2’, appstar_SUB] \\
     Know ‘MAP [LAMl Z (VAR z)/y] (MAP VAR vs) = MAP VAR vs’
     >- (rw [LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC lemma14b \\
         Q.PAT_X_ASSUM ‘DISJOINT (set vs) _’ MP_TAC \\
         rw [DISJOINT_ALT', MEM_EL] >> METIS_TAC []) >> Rewr' \\
     qabbrev_tac ‘args2' = MAP [LAMl Z (VAR z)/y] args2’ \\
     Know ‘LAMl Z (VAR z) = LAMl (FRONT Z) (LAM z (VAR z))’
     >- (REWRITE_TAC [GSYM LAMl_SNOC] \\
         Suff ‘SNOC z (FRONT Z) = Z’ >- Rewr \\
         qunabbrev_tac ‘z’ >> MATCH_MP_TAC SNOC_LAST_FRONT >> art []) >> Rewr' \\
     Know ‘args2' ++ MAP VAR vs = SNOC (VAR b0) (args2' ++ MAP VAR (FRONT vs))’
     >- (qunabbrev_tac ‘b0’ \\
         Know ‘VAR (LAST bs) :term = LAST (MAP VAR vs)’
         >- (rw [Abbr ‘bs’, listTheory.last_drop, LAST_MAP]) >> Rewr' \\
         Know ‘args2' ++ MAP VAR (FRONT vs) = FRONT (args2' ++ MAP VAR vs)’
         >- (rw [MAP_FRONT] \\
             MATCH_MP_TAC (GSYM FRONT_APPEND_NOT_NIL) >> rw []) >> Rewr' \\
         Suff ‘LAST (MAP VAR vs) = LAST (args2' ++ MAP VAR vs)’
         >- (Rewr' >> qabbrev_tac ‘l = args2' ++ MAP VAR vs’ \\
             MATCH_MP_TAC SNOC_LAST_FRONT' >> rw [Abbr ‘l’]) \\
         MATCH_MP_TAC (GSYM LAST_APPEND_NOT_NIL) >> rw []) >> Rewr' \\
     REWRITE_TAC [appstar_SNOC] \\
     qabbrev_tac ‘t :term = LAM z (VAR z)’ \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘t @@ VAR b0’ \\
     CONJ_TAC >- (MATCH_MP_TAC lameq_APPL \\
                  MATCH_MP_TAC lameq_LAMl_appstar_reduce \\
                  rw [Abbr ‘t’, Abbr ‘args2'’, LENGTH_FRONT] \\
                 ‘LENGTH vs = k + 1’ by rw [Abbr ‘vs’, NEWS_def] >> rw []) \\
     rw [Abbr ‘t’, GSYM I_thm, lameq_I])
 >> DISCH_TAC
 (* p3 *)
 >> qabbrev_tac ‘f1 = [LAMl bs P/a]’
 >> qabbrev_tac ‘f2 = [Q/b0]’
 >> qabbrev_tac ‘p3 = [f2; f1]’
 >> Know ‘Boehm_transform p3’
 >- (rw [Abbr ‘p3’, Abbr ‘f1’, Abbr ‘f2’, Boehm_transform_def, EVERY_DEF])
 >> DISCH_TAC
 >> Know ‘f1 (VAR a @* MAP VAR bs) == P’
 >- (rw [Abbr ‘f1’, appstar_SUB] \\
     Know ‘MAP [LAMl bs P/a] (MAP VAR bs) = MAP VAR bs’
     >- (rw [LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC lemma14b >> simp [FV_thm] \\
         Q.PAT_X_ASSUM ‘ALL_DISTINCT vs’ MP_TAC \\
         Cases_on ‘vs’ >- FULL_SIMP_TAC std_ss [] \\
         fs [Abbr ‘a’, Abbr ‘bs’, LENGTH_DROP] \\
         METIS_TAC [MEM_EL]) >> Rewr' \\
     MATCH_MP_TAC lameq_LAMl_appstar_reduce >> simp [] \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs) _’ MP_TAC \\
     rw [DISJOINT_ALT, Abbr ‘bs’, MEM_DROP, MEM_EL] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> Know ‘f2 P = P’
 >- (rw [Abbr ‘f2’] >> MATCH_MP_TAC lemma14b \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs) _’ MP_TAC \\
     rw [DISJOINT_ALT, Abbr ‘bs’, Abbr ‘b0’, MEM_DROP, MEM_EL, LAST_EL, EL_DROP] \\
     Suff ‘PRE (LENGTH vs - 1) + 1 < LENGTH vs’ >- METIS_TAC [] \\
     rw [])
 >> DISCH_TAC
 >> Know ‘f1 (VAR b0) = VAR b0’
 >- (rw [Abbr ‘f1’] >> MATCH_MP_TAC lemma14b \\
     Q.PAT_X_ASSUM ‘ALL_DISTINCT vs’ MP_TAC \\
     Cases_on ‘vs’ >- FULL_SIMP_TAC std_ss [] \\
     fs [Abbr ‘a’, Abbr ‘bs’, Abbr ‘b0’, LENGTH_DROP] \\
     ‘t <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0] \\
     rw [MEM_EL, LAST_EL] \\
     Suff ‘PRE (LENGTH t) < LENGTH t’ >- METIS_TAC [] \\
     rw [])
 >> DISCH_TAC
 >> ‘f2 (VAR b0) = Q’ by rw [Abbr ‘f2’]
 (* final stage *)
 >> Q.EXISTS_TAC ‘p3 ++ p2 ++ p1’
 >> CONJ_ASM1_TAC
 >- (MATCH_MP_TAC Boehm_transform_APPEND >> art [] \\
     MATCH_MP_TAC Boehm_transform_APPEND >> art [])
 >> CONJ_TAC
 >| [ (* goal 1 (of 2) *)
      rw [Boehm_apply_APPEND] \\
      MATCH_MP_TAC lameq_TRANS \\
      Q.EXISTS_TAC ‘apply p3 (VAR a @* MAP VAR bs)’ \\
      CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> art []) \\
      rw [Abbr ‘p3’] \\
      MATCH_MP_TAC lameq_TRANS >> Q.EXISTS_TAC ‘f2 P’ \\
      reverse CONJ_TAC >- rw [] \\
      MATCH_MP_TAC solving_transform_lameq >> rw [Abbr ‘f2’],
      (* goal 2 (of 2) *)
      REWRITE_TAC [Boehm_apply_APPEND] \\
      Q.PAT_X_ASSUM ‘apply P1 N1 = _’ (ONCE_REWRITE_TAC o wrap) \\
      MATCH_MP_TAC lameq_TRANS \\
      Q.EXISTS_TAC ‘apply p3 (VAR b0)’ \\
      reverse CONJ_TAC >- rw [Abbr ‘p3’] \\
      MATCH_MP_TAC Boehm_apply_lameq_cong >> art [] ]
QED

Theorem separability_lemma0[local] :
    !M N. solvable (M :term) /\ solvable N /\
          LAMl_size (principle_hnf M) <= LAMl_size (principle_hnf N) ==>
          equivalent M N \/
          !P Q. ?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q
Proof
    RW_TAC std_ss [equivalent_of_solvables]
 >> ‘ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M UNION FV N) /\
     LENGTH vs = MAX n n'’ by rw [Abbr ‘vs’, NEWS_def]
 >> ‘DISJOINT (set vs) (FV M) /\ DISJOINT (set vs) (FV N)’
      by METIS_TAC [DISJOINT_SYM, DISJOINT_UNION]
 (* applying principle_hnf_FV_SUBSET' *)
 >> Know ‘DISJOINT (set vs) (FV M0)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET >> Q.EXISTS_TAC ‘FV M’ >> art [] \\
     qunabbrev_tac ‘M0’ >> MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set vs) (FV N0)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET >> Q.EXISTS_TAC ‘FV N’ >> art [] \\
     qunabbrev_tac ‘N0’ >> MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y1 :string”, “args1 :term list”)) ‘M1’
 >> Q_TAC (HNF_TAC (“N0 :term”, “vs :string list”,
                    “y2 :string”, “args2 :term list”)) ‘N1’
 >> ‘TAKE (LAMl_size M0) vs = vsM’ by rw [Abbr ‘vsM’, Abbr ‘n’]
 >> ‘TAKE (LAMl_size N0) vs = vsN’ by rw [Abbr ‘vsN’, Abbr ‘n'’]
 >> NTAC 2 (POP_ASSUM (rfs o wrap))
 (* reshaping and reordering assumptions *)
 >> qunabbrev_tac ‘M1’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vsM)’
 >> qunabbrev_tac ‘N1’
 >> qabbrev_tac ‘N1 = principle_hnf (N0 @* MAP VAR vsN)’
 >> Q.PAT_X_ASSUM ‘M0 = _’ ASSUME_TAC
 >> Q.PAT_X_ASSUM ‘N0 = _’ ASSUME_TAC
 >> Q.PAT_X_ASSUM ‘M1 = _’ ASSUME_TAC
 >> Q.PAT_X_ASSUM ‘N1 = _’ ASSUME_TAC
 >> ‘VAR y1 = y’  by rw [Abbr ‘y’ , absfree_hnf_head]
 >> ‘VAR y2 = y'’ by rw [Abbr ‘y'’, absfree_hnf_head]
 (* cleanup MAX and vsN *)
 >> ‘MAX n n' = n'’ by rw [MAX_DEF]
 >> POP_ASSUM (REV_FULL_SIMP_TAC std_ss o wrap)
 >> ‘vsN = vs’ by rw [Abbr ‘vsN’, TAKE_LENGTH_ID_rwt]
 >> qunabbrev_tac ‘vsN’
 >> POP_ASSUM (REV_FULL_SIMP_TAC std_ss o wrap)
 (* Case 1 *)
 >> Cases_on ‘y <> y'’
 >- (simp [] >> rpt GEN_TAC \\
    ‘y1 <> y2’ by (CCONTR_TAC >> fs []) \\
     qabbrev_tac ‘k = n' - n’ \\
    ‘n + k = n'’ by rw [Abbr ‘k’] \\
     qabbrev_tac ‘p0 = MAP rightctxt (REVERSE (MAP VAR vs))’ \\
  (* properties of p0 *)
    ‘Boehm_transform p0’ by rw [Boehm_transform_def, Abbr ‘p0’, EVERY_MAP] \\
     Know ‘apply p0 N0 == N1’
     >- (rw [Abbr ‘p0’, Boehm_apply_MAP_rightctxt']) >> DISCH_TAC \\
     Know ‘apply p0 M0 == M1 @* DROP n (MAP VAR vs)’
     >- (qabbrev_tac ‘l :term list = MAP VAR vs’ \\
         qunabbrev_tac ‘p0’ \\
         Know ‘REVERSE l = REVERSE (TAKE n l ++ DROP n l)’
         >- REWRITE_TAC [TAKE_DROP] >> Rewr' \\
         REWRITE_TAC [REVERSE_APPEND, MAP_APPEND, Boehm_apply_APPEND] \\
         REWRITE_TAC [Boehm_apply_MAP_rightctxt'] \\
         MATCH_MP_TAC lameq_appstar_cong \\
         rw [Abbr ‘l’, Abbr ‘vsM’, GSYM MAP_TAKE]) >> DISCH_TAC \\
  (* now use P and Q

     NOTE: This Z = [z1;z2] contains two fresh variables fixing the textbook
     proof, where [1, p.254] the iterated substition "[LAMl as P/y1] [LAMl as' Q/y2]"
     must be fixed to act as a simultaneous substitution:

    [LAMl as [VAR z2/y2]P/y1] [LAMl as' [VAR z1/y1]Q/y2] [VAR y1/z1] [VAR y2/z2]
   *)
     qabbrev_tac ‘Z = NEWS 2 (FV P UNION FV Q)’ \\
    ‘ALL_DISTINCT Z /\ DISJOINT (set Z) (FV P UNION FV Q) /\ LENGTH Z = 2’
       by rw [NEWS_def, Abbr ‘Z’] \\
     qabbrev_tac ‘z1 = EL 0 Z’ \\
     qabbrev_tac ‘z2 = EL 1 Z’ \\
    ‘MEM z1 Z /\ MEM z2 Z’
       by (rw [MEM_EL, Abbr ‘z1’, Abbr ‘z2’] >| (* 2 subgoals *)
           [ Q.EXISTS_TAC ‘0’ >> rw [],
             Q.EXISTS_TAC ‘1’ >> rw [] ]) \\
    ‘z1 <> z2’ by (rw [Abbr ‘z1’, Abbr ‘z2’, ALL_DISTINCT_EL_IMP]) \\
     qabbrev_tac ‘as = NEWS (m + k) (FV P UNION set Z)’ \\
    ‘LENGTH as = m + k /\ DISJOINT (set as) (FV P UNION set Z)’
       by rw [Abbr ‘as’, NEWS_def] \\
     qabbrev_tac ‘as' = NEWS m' (FV Q UNION set Z)’ \\
    ‘LENGTH as' = m' /\ DISJOINT (set as') (FV Q UNION set Z)’
       by rw [Abbr ‘as'’, NEWS_def] \\
     qabbrev_tac ‘f1 = [LAMl as  ([VAR z2/y2] P)/y1]’ \\
     qabbrev_tac ‘f2 = [LAMl as' ([VAR z1/y1] Q)/y2]’ \\
     qabbrev_tac ‘f3 :term -> term = [VAR y1/z1]’ \\
     qabbrev_tac ‘f4 :term -> term = [VAR y2/z2]’ \\
     qabbrev_tac ‘p1 = [f4; f3; f2; f1]’ \\
  (* properties of p1 *)
    ‘Boehm_transform p1’ by rw [Boehm_transform_def, Abbr ‘p1’,
                                Abbr ‘f1’, Abbr ‘f2’, Abbr ‘f3’, Abbr ‘f4’] \\
     Know ‘DISJOINT (set as) (FV ([VAR z2/y2] P))’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV P UNION set Z’ >> art [] \\
         simp [FV_SUB] \\
         Cases_on ‘y2 IN FV P’ \\
         rw [SUBSET_DEF, IN_UNION, Abbr ‘z2’] >> art []) \\
     DISCH_TAC \\
     Know ‘DISJOINT (set as') (FV ([VAR z1/y1] Q))’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV Q UNION set Z’ >> art [] \\
         simp [FV_SUB] \\
         Cases_on ‘y1 IN FV Q’ \\
         rw [SUBSET_DEF, IN_UNION, Abbr ‘z2’] >> art []) \\
     DISCH_TAC \\
  (* stage work *)
     Q.EXISTS_TAC ‘p1 ++ p0’ \\
     CONJ_ASM1_TAC >- rw [Boehm_transform_APPEND] \\
     reverse CONJ_TAC >| (* 2 subgoals, Q part seems easier *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply (p1 ++ p0) N0’ \\
       CONJ_TAC
       >- (MATCH_MP_TAC Boehm_apply_lameq_cong \\
           POP_ASSUM (REWRITE_TAC o wrap) \\
           qunabbrev_tac ‘N0’ >> MATCH_MP_TAC lameq_SYM \\
           MATCH_MP_TAC lameq_principle_hnf >> art [GSYM solvable_iff_has_hnf]) \\
    (* eliminating p0 *)
       REWRITE_TAC [Boehm_apply_APPEND] \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply p1 N1’ \\
       CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> art []) \\
       SIMP_TAC (srw_ss()) [Abbr ‘p1’] (* f4 (f3 (f2 (f1 N1))) == Q *) \\
    (* eliminating f1 *)
      ‘f1 N1 = VAR y2 @* (MAP f1 args2)’
          by (rw [appstar_SUB, Abbr ‘f1’]) >> POP_ORW \\
    (* eliminating f2 *)
       qunabbrev_tac ‘f2’ \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘f4 (f3 ([VAR z1/y1] Q))’ \\
       CONJ_TAC >- (MATCH_MP_TAC solving_transform_lameq \\
                    CONJ_TAC >- rw [Abbr ‘f4’] \\
                    MATCH_MP_TAC solving_transform_lameq \\
                    CONJ_TAC >- rw [Abbr ‘f3’] \\
                    MATCH_MP_TAC lameq_hnf_fresh_subst >> art [] \\
                    rw [Abbr ‘m'’, hnf_children_hnf]) \\
    (* eliminating f3 *)
       qunabbrev_tac ‘f3’ \\
       Know ‘[VAR y1/z1] ([VAR z1/y1] Q) = Q’
       >- (MATCH_MP_TAC lemma15b \\
           Q.PAT_X_ASSUM ‘DISJOINT (set Z) (FV P UNION FV Q)’ MP_TAC \\
           rw [DISJOINT_ALT] >> METIS_TAC []) >> Rewr' \\
    (* eliminating f4 *)
       qunabbrev_tac ‘f4’ \\
       Suff ‘[VAR y2/z2] Q = Q’ >- rw [] \\
       MATCH_MP_TAC lemma14b \\
       Q.PAT_X_ASSUM ‘DISJOINT (set Z) (FV P UNION FV Q)’ MP_TAC \\
       rw [DISJOINT_ALT] >> METIS_TAC [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply (p1 ++ p0) M0’ \\
       CONJ_TAC
       >- (MATCH_MP_TAC Boehm_apply_lameq_cong \\
           POP_ASSUM (REWRITE_TAC o wrap) \\
           qunabbrev_tac ‘M0’ \\
           MATCH_MP_TAC lameq_SYM \\
           MATCH_MP_TAC lameq_principle_hnf >> art [GSYM solvable_iff_has_hnf]) \\
    (* eliminating p0 *)
       REWRITE_TAC [Boehm_apply_APPEND] \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply p1 (M1 @* DROP n (MAP VAR vs))’ \\
       CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> art []) \\
       SIMP_TAC (srw_ss()) [Abbr ‘p1’] (* f4 (f3 (f2 (f1 M1))) == P *) \\
    (* eliminating f1 *)
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘f4 (f3 (f2 ([VAR z2/y2] P)))’ \\
       CONJ_TAC >- (MATCH_MP_TAC solving_transform_lameq \\
                    CONJ_TAC >- rw [Abbr ‘f4’] \\
                    MATCH_MP_TAC solving_transform_lameq \\
                    CONJ_TAC >- rw [Abbr ‘f3’] \\
                    MATCH_MP_TAC solving_transform_lameq \\
                    CONJ_TAC >- rw [Abbr ‘f2’] \\
                    rw [appstar_SUB, GSYM appstar_APPEND, Abbr ‘f1’] \\
                    MATCH_MP_TAC lameq_LAMl_appstar_reduce >> art [] \\
                    rw [Abbr ‘m’, hnf_children_hnf]) \\
    (* eliminating f2 *)
       Know ‘f2 ([VAR z2/y2] P) = [VAR z2/y2] P’
       >- (qunabbrev_tac ‘f2’ \\
           MATCH_MP_TAC lemma14b >> rw [FV_SUB, IN_UNION] \\
           CCONTR_TAC >> ‘MEM y2 Z’ by METIS_TAC [] \\
           Q.PAT_X_ASSUM ‘DISJOINT (set Z) (FV P UNION FV Q)’ MP_TAC \\
           rw [DISJOINT_ALT'] >> METIS_TAC []) >> Rewr' \\
    (* eliminating f3 *)
       Know ‘f3 ([VAR z2/y2] P) = [VAR z2/y2] P’
       >- (qunabbrev_tac ‘f3’ \\
           MATCH_MP_TAC lemma14b \\
           Suff ‘z1 # P’ >- rw [FV_SUB, IN_UNION] \\
           Q.PAT_X_ASSUM ‘DISJOINT (set Z) (FV P UNION FV Q)’ MP_TAC \\
           rw [DISJOINT_ALT] >> METIS_TAC []) >> Rewr' \\
    (* eliminating f4 *)
       qunabbrev_tac ‘f4’ \\
       Suff ‘[VAR y2/z2] ([VAR z2/y2] P) = P’ >- rw [] \\
       MATCH_MP_TAC lemma15b \\
       Q.PAT_X_ASSUM ‘DISJOINT (set Z) (FV P UNION FV Q)’ MP_TAC \\
       rw [DISJOINT_ALT] >> METIS_TAC [] ])
 (* Case 2 *)
 >> REWRITE_TAC [DECIDE “P \/ Q <=> ~P ==> Q”]
 >> rfs [] >> DISCH_TAC (* m' + n <> m + n' *)
 >> rpt GEN_TAC
 (* p0 is the same as in case 1 *)
 >> qabbrev_tac ‘p0 = MAP rightctxt (REVERSE (MAP VAR vs))’
 (* properties of p0 *)
 >> ‘Boehm_transform p0’ by rw [Boehm_transform_def, Abbr ‘p0’, EVERY_MAP]
 >> Know ‘apply p0 N0 == N1’
 >- rw [Abbr ‘p0’, Boehm_apply_MAP_rightctxt']
 >> ‘LENGTH args2 = m'’ by rw [Abbr ‘m'’, hnf_children_hnf]
 >> Q.PAT_X_ASSUM ‘N1 = _’ (ONCE_REWRITE_TAC o wrap)
 >> DISCH_TAC
 >> Know ‘apply p0 M0 == M1 @* DROP n (MAP VAR vs)’
 >- (qabbrev_tac ‘l :term list = MAP VAR vs’ \\
     qunabbrev_tac ‘p0’ \\
     Know ‘REVERSE l = REVERSE (TAKE n l ++ DROP n l)’
     >- REWRITE_TAC [TAKE_DROP] >> Rewr' \\
     REWRITE_TAC [REVERSE_APPEND, MAP_APPEND, Boehm_apply_APPEND] \\
     REWRITE_TAC [Boehm_apply_MAP_rightctxt'] \\
     MATCH_MP_TAC lameq_appstar_cong \\
     rw [Abbr ‘l’, Abbr ‘vsM’, GSYM MAP_TAKE])
 >> ‘LENGTH args1 = m’ by rw [Abbr ‘m’, hnf_children_hnf]
 >> Q.PAT_X_ASSUM ‘M1 = _’ (ONCE_REWRITE_TAC o wrap)
 >> ‘VAR y1 = VAR y2 :term’ by PROVE_TAC [] >> POP_ORW
 >> REWRITE_TAC [GSYM appstar_APPEND]
 >> qabbrev_tac ‘args1' = args1 ++ DROP n (MAP VAR vs)’
 >> DISCH_TAC
 >> qabbrev_tac ‘l = LENGTH args1'’
 >> ‘l <> m'’ by rw [Abbr ‘l’, Abbr ‘args1'’]
 (* stage work *)
 >> ‘m' < l \/ l < m'’ by rw [] (* 2 subgoals, same ending tactics *)
 >| [ (* goal 1 (of 2) *)
      MP_TAC (Q.SPECL [‘y2’, ‘args1'’, ‘args2’, ‘l - m'’]
                      separability_lemma0_case2) \\
      simp [] \\
      DISCH_THEN (STRIP_ASSUME_TAC o (Q.SPECL [‘P’, ‘Q’])),
      (* goal 2 (of 2) *)
      MP_TAC (Q.SPECL [‘y2’, ‘args2’, ‘args1'’, ‘m' - l’]
                      separability_lemma0_case2) \\
      simp [] \\
      DISCH_THEN (STRIP_ASSUME_TAC o (Q.SPECL [‘Q’, ‘P’])) ]
 (* shared tactics *)
 >> (Q.EXISTS_TAC ‘pi ++ p0’ \\
     CONJ_ASM1_TAC >- rw [Boehm_transform_APPEND] \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1.1 (of 2) *)
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply (pi ++ p0) M0’ \\
       CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong \\
                    POP_ASSUM (REWRITE_TAC o wrap) \\
                    qunabbrev_tac ‘M0’ >> MATCH_MP_TAC lameq_SYM \\
                    MATCH_MP_TAC lameq_principle_hnf \\
                    ASM_REWRITE_TAC [GSYM solvable_iff_has_hnf]) \\
       REWRITE_TAC [Boehm_apply_APPEND] \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply pi (y' @* args1')’ \\
       reverse CONJ_TAC >- art [] \\
       MATCH_MP_TAC Boehm_apply_lameq_cong \\
       Q.PAT_X_ASSUM ‘VAR y2 = y'’ (ONCE_REWRITE_TAC o wrap o SYM) >> art [],
       (* goal 1.2 (of 2) *)
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply (pi ++ p0) N0’ \\
       CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong \\
                    POP_ASSUM (REWRITE_TAC o wrap) \\
                    qunabbrev_tac ‘N0’ >> MATCH_MP_TAC lameq_SYM \\
                    MATCH_MP_TAC lameq_principle_hnf \\
                    ASM_REWRITE_TAC [GSYM solvable_iff_has_hnf]) \\
       REWRITE_TAC [Boehm_apply_APPEND] \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply pi (y @* args2)’ \\
       reverse CONJ_TAC >- art [] \\
       MATCH_MP_TAC Boehm_apply_lameq_cong \\
       Q.PAT_X_ASSUM ‘y = y'’ (ONCE_REWRITE_TAC o wrap) \\
       Q.PAT_X_ASSUM ‘VAR y2 = y'’ (ONCE_REWRITE_TAC o wrap o SYM) >> art [] ])
QED

(* Lemma 10.4.1 (i) [1, p.254] *)
Theorem separability_lemma1 :
    !M N. solvable (M :term) /\ solvable N /\ ~equivalent M N ==>
          !P Q. ?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘N0 = principle_hnf N’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> qabbrev_tac ‘n' = LAMl_size N0’
 (* applying separability_lemma0 *)
 >> ‘n <= n' \/ n' <= n’ by rw []
 >- METIS_TAC [separability_lemma0]
 >> MP_TAC (Q.SPECL [‘N’, ‘M’] separability_lemma0)
 >> RW_TAC std_ss [Once equivalent_comm]
 >> POP_ASSUM (MP_TAC o Q.SPECL [‘Q’, ‘P’])
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC ‘pi’ >> art []
QED

(* Lemma 10.4.1 (ii) [1, p.254] *)
Theorem separability_lemma2 :
    !M N. solvable M /\ ~equivalent M N ==>
          !P. ?pi. Boehm_transform pi /\ apply pi M == P /\ ~solvable (apply pi N)
Proof
    rpt STRIP_TAC
 (* applying separability_lemma1, ‘~equivalent M N’ is only used here *)
 >> Cases_on ‘solvable N’
 >- (‘!P Q. ?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q’
         by METIS_TAC [separability_lemma1] \\
     POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘P’, ‘Omega’])) \\
     Q.EXISTS_TAC ‘pi’ >> art [] \\
     METIS_TAC [lameq_solvable_cong, unsolvable_Omega])
 (* stage work *)
 >> ‘?M0. M == M0 /\ hnf M0’ by METIS_TAC [has_hnf_def, solvable_iff_has_hnf]
 >> ‘?vs args y. ALL_DISTINCT vs /\ M0 = LAMl vs (VAR y @* args)’
      by METIS_TAC [hnf_cases]
 >> qabbrev_tac ‘as = NEWS (LENGTH args) (FV P)’
 >> qabbrev_tac ‘pi = [LAMl as P/y]::MAP rightctxt (MAP VAR (REVERSE vs))’
 >> Q.EXISTS_TAC ‘pi’
 >> STRONG_CONJ_TAC
 >- rw [Abbr ‘pi’, Boehm_transform_def, EVERY_SNOC, EVERY_MAP]
 >> DISCH_TAC
 (* applying unsolvable_apply *)
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC unsolvable_apply >> art [])
 (* stage work *)
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘apply pi M0’
 >> CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> art [])
 >> POP_ASSUM K_TAC (* ‘Boehm_transform pi’ is not needed here *)
 >> rw [Abbr ‘pi’]
 >> qabbrev_tac ‘pi :transform = MAP rightctxt (MAP VAR (REVERSE (vs)))’
 >> qabbrev_tac ‘t = VAR y @* args’
 (* applying Boehm_apply_MAP_rightctxt *)
 >> Know ‘apply pi (LAMl vs t) = LAMl vs t @* MAP VAR vs’
 >- (rw [Abbr ‘pi’, Boehm_apply_MAP_rightctxt] \\
     rw [MAP_REVERSE, REVERSE_REVERSE])
 >> Rewr'
 (* applying lameq_LAMl_appstar_VAR *)
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘[LAMl as P/y] t’
 >> CONJ_TAC
 >- (irule lameq_sub_cong >> rw [lameq_LAMl_appstar_VAR])
 >> rw [Abbr ‘t’, appstar_SUB]
 >> ‘DISJOINT (set as) (FV P) /\ LENGTH as = LENGTH args’
      by rw [NEWS_def, Abbr ‘as’]
 >> MATCH_MP_TAC lameq_LAMl_appstar_reduce >> rw []
QED

(* Theorem 10.4.2 (i) [1, p.256]

   NOTE: This theorem only depends on [separability_lemma1]. The present version
   is tailored for applying [distinct_bnf_imp_agree_uptp] and [agree_upto_thm].
 *)
Theorem separability_thm :
    !X M N r.
       FINITE X /\ FV M UNION FV N SUBSET X UNION RANK r /\ 0 < r /\
       ltree_paths (BT' X M r) = ltree_paths (BT' X N r) /\
       has_bnf M /\ has_bnf N /\ ~(M == N) ==>
       !P Q. ?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘N’, ‘r’] distinct_bnf_imp_agree_upto)
 >> rw []
 >> Know ‘?p0. Boehm_transform p0 /\ faithful p X [M; N] p0 r’
 >- (MATCH_MP_TAC agree_upto_thm >> simp [] \\
     fs [SUBSET_UNION] >> METIS_TAC [])
 >> rw [faithful_two]
 >> qabbrev_tac ‘M0 = apply p0 M’
 >> qabbrev_tac ‘N0 = apply p0 N’
 >> Suff ‘solvable M0 /\ solvable N0’
 >- (STRIP_TAC \\
    ‘?p1. Boehm_transform p1 /\ apply p1 M0 == P /\ apply p1 N0 == Q’
       by PROVE_TAC [separability_lemma1] \\
     Q.EXISTS_TAC ‘p1 ++ p0’ \\
     fs [Abbr ‘M0’, Abbr ‘N0’, Boehm_transform_APPEND, GSYM Boehm_apply_APPEND])
 (* stage work *)
 >> Q.PAT_X_ASSUM ‘_ <=> solvable M0’ (REWRITE_TAC o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘_ <=> solvable N0’ (REWRITE_TAC o wrap o SYM)
 >> fs [SUBSET_UNION]
 >> Know ‘BT_valid_paths M = BT_paths M’
 >- (MATCH_MP_TAC BT_valid_paths_has_bnf \\
     qexistsl_tac [‘X’, ‘r’] >> art [])
 >> Rewr'
 >> Know ‘BT_valid_paths N = BT_paths N’
 >- (MATCH_MP_TAC BT_valid_paths_has_bnf \\
     qexistsl_tac [‘X’, ‘r’] >> art [])
 >> Rewr'
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘r’] BT_paths_thm)
 >> simp [] >> DISCH_THEN K_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘N’, ‘r’] BT_paths_thm)
 >> simp []
QED

(* A final form of [separability_thm], not used later in this theory *)
Theorem separability_thm_final :
    !M N. has_bnf M /\ has_bnf N /\ ~(M == N) /\ BT_paths M = BT_paths N ==>
         !P Q. ?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘X = FV M UNION FV N’
 >> ‘FINITE X’ by rw [Abbr ‘X’]
 >> ‘FV M SUBSET X UNION RANK 1 /\
     FV N SUBSET X UNION RANK 1’ by (qunabbrev_tac ‘X’ >> SET_TAC [])
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘N’, ‘1’] separability_thm)
 >> simp []
 >> DISCH_THEN MATCH_MP_TAC
 >> Know ‘ltree_paths (BT' X M 1) = BT_paths M’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC BT_paths_thm >> art [])
 >> Rewr'
 >> Know ‘ltree_paths (BT' X N 1) = BT_paths N’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC BT_paths_thm >> art [])
 >> Rewr'
 >> rw []
QED

(* Theorem 10.4.2 (ii) [1, p.256]

   NOTE: This theorem inherited all antecedents of [separability_thm].
 *)
Theorem closed_separability_thm :
    !X M N r.
       FINITE X /\ FV M UNION FV N SUBSET X UNION RANK r /\ 0 < r /\
       ltree_paths (BT' X M r) = ltree_paths (BT' X N r) /\
       has_bnf M /\ has_bnf N /\ ~(M == N) /\
       closed M /\ closed N ==> !P Q. ?L. M @* L == P /\ N @* L == Q
Proof
    rpt STRIP_TAC
 >> ‘?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q’
       by METIS_TAC [separability_thm]
 >> ‘?Ns. !M. closed M ==> apply pi M == M @* Ns’
       by METIS_TAC [Boehm_transform_lameq_appstar]
 >> Q.EXISTS_TAC ‘Ns’
 >> CONJ_TAC (* 2 subgoals, same ending tactics *)
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC lameq_TRANS >> Q.EXISTS_TAC ‘apply pi M’ >> art [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC lameq_TRANS >> Q.EXISTS_TAC ‘apply pi N’ >> art [] ]
 >> rw [lameq_SYM]
QED

(* Corollary 10.4.3 (i) [1, p.256]

   NOTE: This theorem inherited all antecedents of [separability_thm].
 *)
Theorem distinct_bnf_imp_inconsistent :
    !X M N r.
       FINITE X /\ FV M UNION FV N SUBSET X UNION RANK r /\ 0 < r /\
       ltree_paths (BT' X M r) = ltree_paths (BT' X N r) /\
       has_bnf M /\ has_bnf N /\ ~(M == N) ==> inconsistent (asmlam {(M,N)})
Proof
    rw [inconsistent_def]
 >> rename1 ‘asmlam {(M,N)} P Q’
 >> Know ‘?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q’
 >- (MATCH_MP_TAC separability_thm \\
     qexistsl_tac [‘X’, ‘r’] >> simp [])
 >> STRIP_TAC
 >> qabbrev_tac ‘eqns = {(M,N)}’
 >> MATCH_MP_TAC asmlam_trans
 >> Q.EXISTS_TAC ‘apply pi M’
 >> CONJ_TAC >- (MATCH_MP_TAC lameq_asmlam >> rw [lameq_SYM])
 >> MATCH_MP_TAC asmlam_trans
 >> Q.EXISTS_TAC ‘apply pi N’
 >> reverse CONJ_TAC >- (MATCH_MP_TAC lameq_asmlam >> art [])
 >> MATCH_MP_TAC Boehm_apply_asmlam_cong >> art []
 >> Suff ‘(M,N) IN eqns’ >- rw [asmlam_rules]
 >> rw [Abbr ‘eqns’]
QED

(* NOTE: This theorem is used in proving the final lameta completeness *)
Theorem distinct_bnf_imp_incompatible =
        distinct_bnf_imp_inconsistent |> REWRITE_RULE [GSYM incompatible_def]

(* The so called "completeness" of lambda is just another form of the above
   distinct_bnf_imp_inconsistent.
 *)
Theorem lambda_complete :
    !X M N r.
       FINITE X /\ FV M UNION FV N SUBSET X UNION RANK r /\ 0 < r /\
       ltree_paths (BT' X M r) = ltree_paths (BT' X N r) /\
       has_bnf M /\ has_bnf N ==>
       M == N \/ inconsistent (asmlam {(M,N)})
Proof
    METIS_TAC [distinct_bnf_imp_inconsistent]
QED

(* A final form of the above theorem (completeness of lambda) *)
Theorem lambda_complete_final :
    !M N. has_bnf M /\ has_bnf N /\ BT_paths M = BT_paths N ==>
          M == N \/ inconsistent (asmlam {(M,N)})
Proof
    rpt STRIP_TAC
 >> Cases_on ‘M == N’ >> simp []
 >> MATCH_MP_TAC distinct_bnf_imp_inconsistent
 >> qexistsl_tac [‘FV M UNION FV N’, ‘1’] >> simp []
 >> STRONG_CONJ_TAC >- SET_TAC []
 >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘FV M UNION FV N’, ‘M’, ‘1’] (GSYM BT_paths_thm))
 >> simp []
 >> DISCH_THEN K_TAC
 >> MP_TAC (Q.SPECL [‘FV M UNION FV N’, ‘N’, ‘1’] (GSYM BT_paths_thm))
 >> simp []
QED

(*---------------------------------------------------------------------------*
 *  Eta expansion of Boehm trees
 *---------------------------------------------------------------------------*)

(* Definition 10.2.8 [1, p.232] (eta-expansion)

  “BT_expand X M r p” expands the parent path p of “BT' X M r” with one more
   right-most child, maintaining the eta-equivalence to original Boehm tree.

   Assumptions:
   1. FINITE X
   2. FV M SUBSET X UNION RANK r
   3. ltree_finite (BT' X M r) (or “has_bnf M”, or “bnf M”)
   4. p IN ltree_paths (BT' X M r)
   5. THE (ltree_el (BT' X M r) p) <> bot (automatic by “bnf M”)
 *)
Definition BT_expand_def :
    BT_expand X t p r =
       let s = ltree_paths t;
          r' = LENGTH p + r;
     (d,len) = THE (ltree_el t p);
      (vs,y) = THE d;
           m = THE len;
           n = LENGTH vs;
         vs' = RNEWS r' (SUC n) X;
           v = LAST vs';
           f = OPTION_MAP (\(vs,y). (SNOC v vs,y))
        in
           ltree_insert f t p (BT_VAR v)
End

Theorem ltree_finite_BT_expand_lemma[local] :
    !X t p r. ltree_finite t /\
             (?vs y m. ltree_el t p = SOME (SOME (vs,y),SOME m)) ==>
              ltree_finite (BT_expand X t p r)
Proof
    rw [BT_expand_def]
 >> simp []
 >> MATCH_MP_TAC ltree_finite_ltree_insert
 >> rw [ltree_paths_alt_ltree_el]
QED

Theorem ltree_finite_BT_expand :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\ bnf M /\
              p IN ltree_paths (BT' X M r) ==>
              ltree_finite (BT_expand X (BT' X M r) p r)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC ltree_finite_BT_expand_lemma
 >> CONJ_TAC
 >- (MATCH_MP_TAC ltree_finite_BT_bnf >> art [])
 >> MATCH_MP_TAC BT_ltree_el_cases >> art []
QED

(* NOTE: This lemma is not suitable for induction, because (in general),
   if “compat_closure eta N M” and M is bnf, N may have beta-redexes due
   to eta-expansion. Thus, in general we can only say “has_bnf N” instead
   of “bnf N”.

   But, in our case, the term N is “BT_to_term B”, and any term constructed
   from Boehm trees should have NO bete-redex at all, but we don't need to
   spend extra efforts to prove it. Instead, we use the next lemma2.

   compat_closure eta N M' (FV N = FV M') /\
   M == M' (+ FV M' SUBSET FV M) ==> lameta M N (FV N SUBSET FV M)
 *)
Theorem BT_expand_lemma1 :
    !X M p r B N.
       FINITE X /\ FV M SUBSET X UNION RANK r /\ bnf M /\
       p IN ltree_paths (BT' X M r) /\
       BT_expand X (BT' X M r) p r = B /\ N = BT_to_term B ==>
       compat_closure eta N M /\ BT' X N r = B
Proof
    rpt GEN_TAC
 >> STRIP_TAC
 >> simp []
 >> Suff ‘!R M r. (?p B. FV M SUBSET X UNION RANK r /\ bnf M /\
                         p IN ltree_paths (BT' X M r) /\
                         B = BT_expand X (BT' X M r) p r /\ R = to_rose B) ==>
                   compat_closure eta (rose_to_term R) M /\
                   BT' X (rose_to_term R) r = from_rose R’
 >- (Know ‘from_rose (to_rose B) = B’
     >- (MATCH_MP_TAC to_rose_def \\
         Q.PAT_X_ASSUM ‘_ = B’ (REWRITE_TAC o wrap o SYM) \\
         MATCH_MP_TAC ltree_finite_BT_expand >> art []) \\
     DISCH_TAC \\
     Know ‘BT' X (BT_to_term B) r = B <=>
           BT' X (BT_to_term B) r = from_rose (to_rose B)’ >- simp [] \\
     Rewr' \\
     DISCH_THEN MATCH_MP_TAC \\
     qexistsl_tac [‘p’, ‘B’] >> art [])
 (* keep only “FINITE X” in assumptions *)
 >> Q.PAT_X_ASSUM ‘FINITE X’ MP_TAC
 >> KILL_TAC >> DISCH_TAC
 (* applying induction on rose tree *)
 >> HO_MATCH_MP_TAC rose_tree_induction
 >> rpt GEN_TAC >> STRIP_TAC
 >> rpt GEN_TAC >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘Rose a ts = _’ (MP_TAC o SYM)
 >> POP_ORW
 >> DISCH_THEN (MP_TAC o AP_TERM “from_rose :BT_node rose_tree -> boehm_tree”)
 >> simp [to_rose_def, ltree_finite_BT_expand]
 >> simp [from_rose_def]
 >> DISCH_TAC
 >> Q_TAC (UNBETA_TAC [rose_to_term_def, Once rose_reduce_def])
          ‘rose_to_term (Rose a ts)’
 >> simp [GSYM rose_to_term_def]
 (* special case (kind of base case here) *)
 >> Cases_on ‘p’
 >- (POP_ASSUM MP_TAC \\
     simp [BT_expand_def] \\
    ‘solvable M’ by PROVE_TAC [bnf_solvable] \\
     Q_TAC (UNBETA_TAC [BT_def, BT_generator_def, Once ltree_unfold])
           ‘BT' X M r’ \\
     simp [GSYM BT_def, ltree_el_def, Abbr ‘l’, LMAP_fromList, LNTH_fromList,
           EL_MAP, ltree_paths_alt_ltree_el] \\
     simp [ltree_insert_NIL] \\
     qunabbrev_tac ‘vs’ \\
     Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’ \\
     qunabbrev_tac ‘y’ \\
    ‘DISJOINT (set vs) (FV M0)’ by PROVE_TAC [subterm_disjoint_lemma'] \\
     Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                     “y :string”, “args :term list”)) ‘M1’ \\
    ‘TAKE n vs = vs’ by rw [] \\
     POP_ASSUM (rfs o wrap) \\
     simp [Abbr ‘Ms’] \\
     Q_TAC (RNEWS_TAC (“vs' :string list”, “r :num”, “(SUC n)”)) ‘X’ \\
     qabbrev_tac ‘v = LAST vs'’ \\
     qabbrev_tac ‘m = LENGTH args’ \\
     simp [LNTH_EQ, LNTH_LGENLIST, LNTH_fromList, EL_MAP] \\
     STRIP_TAC \\
     Q.PAT_X_ASSUM ‘_ = a’ (simp o wrap o SYM) \\
     Know ‘!i. i < m ==> from_rose (EL i ts) = BT' X (EL i args) (SUC r)’
     >- (rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘!(n :num). P’ (MP_TAC o Q.SPEC ‘i’) \\
         simp []) >> DISCH_TAC \\
     Know ‘from_rose (EL m ts) = BT_VAR v’
     >- (Q.PAT_X_ASSUM ‘!n. (if n < m + 1 then _ else NONE) = _’
           (MP_TAC o Q.SPEC ‘m’) \\
         simp []) >> DISCH_TAC \\
     qabbrev_tac ‘m' = LENGTH ts’ \\
     Know ‘m' = m + 1’
     >- (CCONTR_TAC \\
        ‘m' < m + 1 \/ m + 1 < m'’ by rw [] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           Q.PAT_X_ASSUM ‘!n. (if n < m + 1 then _ else NONE) = _’
             (MP_TAC o Q.SPEC ‘m'’) >> simp [],
           (* goal 2 (of 2) *)
           Q.PAT_X_ASSUM ‘!n. (if n < m + 1 then _ else NONE) = _’
             (MP_TAC o Q.SPEC ‘m + 1’) >> simp [] ]) >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘!n. (if n < m + 1 then _ else NONE) = _’ K_TAC \\
     Know ‘MAP rose_to_term ts = SNOC (VAR v) args’
     >- (simp [LIST_EQ_REWRITE, EL_MAP] \\
         Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
        ‘i = m \/ i < m’ by rw []
         >- (simp [Abbr ‘m’, EL_LENGTH_SNOC] \\
             Q.PAT_X_ASSUM ‘_ = BT_VAR v’
               (MP_TAC o AP_TERM “to_rose :boehm_tree -> BT_node rose_tree”) \\
             simp [to_rose_thm]) \\
         simp [EL_SNOC] \\
         Q.PAT_X_ASSUM ‘!i. i < m ==> from_rose (EL i ts) = _’ drule \\
         DISCH_THEN (MP_TAC o AP_TERM “to_rose :boehm_tree -> BT_node rose_tree”) \\
         simp [to_rose_thm] \\
         DISCH_THEN K_TAC \\
         MATCH_MP_TAC BT_to_term_bnf >> art [] \\
         CONJ_TAC
         >- (MATCH_MP_TAC subterm_induction_lemma' \\
             qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []) \\
         MATCH_MP_TAC hnf_children_bnf \\
         qexistsl_tac [‘vs’, ‘y’] >> art [] \\
         Q.PAT_X_ASSUM ‘M0 = _’ (REWRITE_TAC o wrap o SYM) \\
         simp [] \\
         Suff ‘M0 = M’ >- rw [] \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC principle_hnf_bnf >> art []) >> Rewr' \\
     reverse CONJ_TAC
     >- (REWRITE_TAC [GSYM LAMl_SNOC] \\
         qabbrev_tac ‘xs = SNOC v vs’ \\
         qabbrev_tac ‘args' = SNOC (VAR v) args’ \\
         simp [BT_def, BT_generator_def, Once ltree_unfold] \\
         Know ‘principle_hnf (LAMl xs (VAR y @* args')) =
               LAMl xs (VAR y @* args')’
         >- (MATCH_MP_TAC principle_hnf_reduce \\
             simp [hnf_thm, hnf_appstar]) >> Rewr' \\
         simp [Abbr ‘xs’, GSYM ADD1, GSYM BT_def] \\
         REWRITE_TAC [GSYM LAMl_SNOC, GSYM SNOC_APPEND] \\
         Know ‘SNOC v vs = vs'’
         >- (Know ‘vs <<= vs'’ >- rw [Abbr ‘vs’, Abbr ‘vs'’, RNEWS_prefix] \\
             simp [IS_PREFIX_EQ_TAKE] \\
             DISCH_THEN (Q.X_CHOOSE_THEN ‘i’ STRIP_ASSUME_TAC) \\
             Know ‘LENGTH vs = LENGTH (TAKE i vs')’
             >- POP_ASSUM (REWRITE_TAC o wrap) \\
             simp [] >> DISCH_TAC \\
             Know ‘TAKE i vs' = FRONT vs'’
             >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
                ‘i = LENGTH vs' - 1’ by rw [] >> POP_ORW \\
                 MATCH_MP_TAC FRONT_BY_TAKE >> rw [GSYM LENGTH_NON_NIL]) \\
             Rewr' \\
             REWRITE_TAC [GSYM SNOC_APPEND] \\
             qunabbrev_tac ‘v’ \\
             MATCH_MP_TAC SNOC_LAST_FRONT \\
             rw [GSYM LENGTH_NON_NIL]) >> Rewr \\
         simp [principle_hnf_beta_reduce, hnf_appstar] \\
         simp [LMAP_fromList, MAP_MAP_o, o_DEF] \\
         simp [LIST_EQ_REWRITE, Abbr ‘args'’] \\
         Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
         simp [EL_MAP] \\
        ‘i < m \/ i = m’ by rw [] >- simp [EL_SNOC] \\
        ‘i = LENGTH args’ by rw [] >> POP_ORW \\
         simp [EL_LENGTH_SNOC]) \\
    ‘M = M0’ by METIS_TAC [principle_hnf_bnf] \\
     simp [appstar_SNOC] \\
  (* applying compat_closure rules *)
     MATCH_MP_TAC compat_closure_LAMl \\
     MATCH_MP_TAC compat_closure_R \\
     REWRITE_TAC [eta_def] \\
     Q.EXISTS_TAC ‘v’ >> simp [] \\
     simp [FV_appstar] \\
     Suff ‘{y} UNION BIGUNION (IMAGE FV (set args)) SUBSET FV M UNION set vs’
     >- (DISCH_TAC \\
         Know ‘{y} UNION BIGUNION (IMAGE FV (set args)) SUBSET
               X UNION RANK r UNION set vs’
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M UNION set vs’ \\
             POP_ASSUM (REWRITE_TAC o wrap) \\
             Suff ‘FV M SUBSET X UNION RANK r’ >- SET_TAC [] \\
             simp []) >> DISCH_TAC \\
         Suff ‘v NOTIN X UNION RANK r UNION set vs’
         >- (rpt STRIP_TAC \\
             METIS_TAC [SUBSET_DEF]) \\
         NTAC 2 (POP_ASSUM K_TAC) \\
         Know ‘v = EL n vs'’
         >- (‘vs' <> []’ by rw [GSYM LENGTH_NON_NIL] \\
             simp [LAST_EL, Abbr ‘v’]) >> Rewr' \\
         simp [IN_UNION, GSYM CONJ_ASSOC] \\
         CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs') X’ MP_TAC \\
             rw [DISJOINT_ALT] \\
             POP_ASSUM MATCH_MP_TAC >> rw [EL_MEM]) \\
         CONJ_TAC
         >- (MP_TAC (Q.SPECL [‘r’, ‘SUC n’, ‘X’] DISJOINT_RNEWS_RANK') \\
             simp [] \\
             rw [DISJOINT_ALT] \\
             POP_ASSUM MATCH_MP_TAC >> rw [EL_MEM]) \\
         Know ‘vs <<= vs'’
         >- (qunabbrevl_tac [‘vs’, ‘vs'’] \\
             MATCH_MP_TAC RNEWS_prefix >> rw []) \\
         simp [IS_PREFIX_EQ_TAKE] \\
         DISCH_THEN (Q.X_CHOOSE_THEN ‘i’ STRIP_ASSUME_TAC) \\
         simp [] \\
         POP_ASSUM (MP_TAC o AP_TERM “LENGTH :string list -> num”) \\
         simp [LENGTH_TAKE] >> DISCH_THEN (rfs o wrap o SYM) \\
         qabbrev_tac ‘v' = EL n vs'’ (* this is also “v” *) \\
         Know ‘MEM v' (DROP n vs')’
         >- (simp [Abbr ‘v'’, MEM_DROP] \\
             Q.EXISTS_TAC ‘0’ >> simp []) >> DISCH_TAC \\
         CCONTR_TAC \\
         METIS_TAC [ALL_DISTINCT_TAKE_DROP]) \\
     Q.PAT_X_ASSUM ‘M = _’ K_TAC \\
     simp [UNION_SUBSET, SUBSET_DEF] \\
  (* applying subterm_headvar_lemma' *)
     CONJ_TAC
     >- (MP_TAC (Q.SPECL [‘X’, ‘M’, ‘r’, ‘M0’, ‘n’, ‘vs’, ‘M1’]
                         subterm_headvar_lemma') >> simp []) \\
  (* applying FV_subterm_lemma *)
     simp [MEM_EL] >> rpt STRIP_TAC \\
     gs [] >> rename1 ‘N = EL i args’ \\
     Q.PAT_X_ASSUM ‘x IN FV (EL i args)’ MP_TAC \\
     Suff ‘FV (EL i args) SUBSET FV M UNION set vs’ >- rw [SUBSET_DEF] \\
     MP_TAC (Q.SPECL [‘X’, ‘M’, ‘r’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’, ‘args’, ‘i’]
                     FV_subterm_lemma) >> simp [])
 (* stage work *)
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> ‘solvable M’ by PROVE_TAC [bnf_solvable]
 >> Q_TAC (UNBETA_TAC [BT_def, BT_generator_def, Once ltree_unfold]) ‘BT' X M r’
 >> simp [GSYM BT_def, ltree_el_def, Abbr ‘l’, LMAP_fromList, LNTH_fromList,
          EL_MAP, ltree_paths_alt_ltree_el]
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> qunabbrev_tac ‘y’
 >> ‘DISJOINT (set vs) (FV M0)’ by PROVE_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> simp [Abbr ‘Ms’]
 >> qabbrev_tac ‘m = LENGTH args’
 >> Cases_on ‘h < m’ >> simp []
 >> qabbrev_tac ‘N = EL h args’
 >> DISCH_TAC (* ltree_el (BT' X N (SUC r)) t <> NONE *)
 >> simp [BT_expand_def]
 >> qabbrev_tac ‘r' = r + SUC (LENGTH t)’
 >> Know ‘bnf N’
 >- (qunabbrev_tac ‘N’ \\
     MATCH_MP_TAC hnf_children_bnf \\
     qexistsl_tac [‘vs’, ‘y’] \\
     Q.PAT_X_ASSUM ‘M0 = _’ (REWRITE_TAC o wrap o SYM) >> simp [] \\
     Suff ‘M0 = M’ >- rw [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principle_hnf_bnf >> art [])
 >> DISCH_TAC
 >> Know ‘FV N SUBSET X UNION RANK (SUC r)’
 >- (qunabbrev_tac ‘N’ \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [])
 >> DISCH_TAC
 >> simp [ltree_el_def, LNTH_fromList, EL_MAP]
 (* applying BT_ltree_el_cases *)
 >> Know ‘?vs' y' m'. ltree_el (BT' X N (SUC r)) t = SOME (SOME (vs',y'),SOME m')’
 >- (MATCH_MP_TAC BT_ltree_el_cases \\
     simp [ltree_paths_alt_ltree_el])
 >> STRIP_TAC
 >> simp []
 >> qabbrev_tac ‘n1 = SUC (LENGTH vs')’
 >> Q_TAC (RNEWS_TAC (“vs1 :string list”, “r' :num”, “n1 :num”)) ‘X’
 >> simp [MAP_MAP_o, o_DEF]
 >> qabbrev_tac ‘B = BT' X N (SUC r)’
 >> qabbrev_tac ‘f = OPTION_MAP (\(vs,(y :string)). (SNOC (LAST vs1) vs,y))’
 (* applying ltree_insert_CONS *)
 >> qmatch_abbrev_tac ‘ltree_insert f (Branch a' ts') (h::t) t0 = Branch a _ ==> _’
 >> MP_TAC (Q.SPECL [‘f’, ‘a'’, ‘ts'’, ‘h’, ‘t’, ‘B’, ‘t0’]
                    (INST_TYPE [alpha |-> “:BT_node”] ltree_insert_CONS))
 >> impl_tac >- simp [Abbr ‘ts'’, LNTH_fromList, EL_MAP]
 >> simp [] >> DISCH_THEN K_TAC
 >> simp [Abbr ‘ts'’, LLENGTH_fromList, LNTH_fromList, Abbr ‘a'’]
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘_ = a’ (simp o wrap o SYM)
 >> POP_ASSUM MP_TAC (* LGENLIST _ = fromList (MAP from_rose ts) *)
 >> simp [LNTH_EQ, LNTH_fromList, LNTH_LGENLIST]
 >> DISCH_TAC
 >> qabbrev_tac ‘m0 = LENGTH ts’
 >> Know ‘m0 = m’
 >- (CCONTR_TAC \\
    ‘m0 < m \/ m < m0’ by rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.PAT_X_ASSUM ‘!i. _ = if i < m0 then _ else NONE’ (MP_TAC o Q.SPEC ‘m0’) \\
       simp [],
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM ‘!i. _ = if i < m0 then _ else NONE’ (MP_TAC o Q.SPEC ‘m’) \\
       simp [] ])
 >> DISCH_TAC
 >> Know ‘!i. i < m ==> from_rose (EL i ts) =
                        if i = h then ltree_insert f B t t0
                        else (BT' X (EL i args) (SUC r))’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!i. _ = if i < m0 then _ else NONE’ (MP_TAC o Q.SPEC ‘i’) \\
     simp [EL_MAP])
 >> Q.PAT_X_ASSUM ‘!i. _ = if i < m0 then _ else NONE’ K_TAC
 >> qunabbrev_tac ‘m0’
 >> DISCH_TAC
 (* applying to_rose_thm *)
 >> Know ‘!i. i < m ==> EL i ts =
                        if i = h then to_rose (ltree_insert f B t t0)
                        else to_rose (BT' X (EL i args) (SUC r))’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < m ==> from_rose (EL i ts) = _’ drule \\
     DISCH_THEN (MP_TAC o AP_TERM “to_rose :boehm_tree -> BT_node rose_tree”) \\
     simp [to_rose_thm] >> DISCH_THEN K_TAC \\
     Cases_on ‘i = h’ >> simp [])
 >> POP_ASSUM K_TAC >> DISCH_TAC
 >> Know ‘MAP rose_to_term ts =
          GENLIST (\i. if i = h then (BT_to_term (ltree_insert f B t t0))
                       else EL i args) m’
 >- (simp [LIST_EQ_REWRITE, EL_GENLIST, EL_MAP] \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     Cases_on ‘i = h’ >> simp [] \\
     MATCH_MP_TAC BT_to_term_bnf >> art [] \\
     CONJ_TAC
     >- (MATCH_MP_TAC subterm_induction_lemma' \\
         qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []) \\
     MATCH_MP_TAC hnf_children_bnf \\
     qexistsl_tac [‘vs’, ‘y’] >> art [] \\
     Q.PAT_X_ASSUM ‘M0 = _’ (REWRITE_TAC o wrap o SYM) \\
     simp [] \\
     Suff ‘M0 = M’ >- rw [] \\
     qunabbrev_tac ‘M0’ >> MATCH_MP_TAC principle_hnf_bnf >> art [])
 >> Rewr'
 >> reverse CONJ_TAC
 >- (qmatch_abbrev_tac ‘BT' X (LAMl vs (VAR y @* args')) r = _’ \\
     simp [BT_def, BT_generator_def, Once ltree_unfold] \\
     Know ‘principle_hnf (LAMl vs (VAR y @* args')) = LAMl vs (VAR y @* args')’
     >- (MATCH_MP_TAC principle_hnf_reduce >> simp []) >> Rewr' \\
     simp [GSYM BT_def, principle_hnf_beta_reduce] \\
     simp [LMAP_fromList, MAP_MAP_o, o_DEF] \\
     simp [Abbr ‘args'’, MAP_GENLIST, o_DEF] \\
     simp [LIST_EQ_REWRITE] \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
    ‘i <> h \/ i = h’ by rw []
     >- (simp [EL_MAP, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC to_rose_def \\
         MATCH_MP_TAC ltree_finite_BT_bnf >> art [] \\
         CONJ_TAC
         >- (MATCH_MP_TAC subterm_induction_lemma' \\
             qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []) \\
         MATCH_MP_TAC hnf_children_bnf \\
         qexistsl_tac [‘vs’, ‘y’] >> art [] \\
         Q.PAT_X_ASSUM ‘M0 = _’ (REWRITE_TAC o wrap o SYM) \\
         simp [] \\
         Suff ‘M0 = M’ >- rw [] \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC principle_hnf_bnf >> art []) \\
     simp [EL_MAP] \\
  (* apply IH *)
     FIRST_X_ASSUM (irule o cj 2) \\
     reverse CONJ_TAC
     >- (simp [MEM_EL] \\
         Q.EXISTS_TAC ‘i’ >> art [] \\
         Q.PAT_X_ASSUM ‘!i. i < m ==> _’ (MP_TAC o Q.SPEC ‘i’) \\
         simp []) \\
     qabbrev_tac ‘N = EL h args’ \\
     qexistsl_tac [‘N’, ‘t’] >> simp [ltree_paths_alt_ltree_el] \\
     simp [GSYM from_rose_11] \\
     Know ‘from_rose (to_rose (ltree_insert f B t t0)) = ltree_insert f B t t0’
     >- (MATCH_MP_TAC to_rose_def \\
         MATCH_MP_TAC ltree_finite_ltree_insert \\
         simp [Abbr ‘t0’, ltree_paths_alt_ltree_el, Abbr ‘B’] \\
         MATCH_MP_TAC ltree_finite_BT_bnf >> art []) >> Rewr' \\
     Know ‘from_rose (to_rose (BT_expand X B t (SUC r))) =
           BT_expand X B t (SUC r)’
     >- (MATCH_MP_TAC to_rose_def \\
         qunabbrev_tac ‘B’ \\
         MATCH_MP_TAC ltree_finite_BT_expand \\
         simp [ltree_paths_alt_ltree_el]) >> Rewr' \\
     simp [BT_expand_def, Abbr ‘f’] \\
    ‘LENGTH t + SUC r = r'’ by rw [Abbr ‘r'’] >> POP_ORW \\
     simp [])
 >> Know ‘M = M0’
 >- (qunabbrev_tac ‘M0’ \\
     ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC principle_hnf_bnf >> art [])
 >> Rewr'
 >> simp []
 >> MATCH_MP_TAC compat_closure_LAMl
 >> MATCH_MP_TAC compat_closure_appstar' >> simp []
 (* applying IH (amazing) *)
 >> FIRST_X_ASSUM (fn th => irule (cj 1 th))
 >> reverse CONJ_TAC
 >- (simp [MEM_EL] >> Q.EXISTS_TAC ‘h’ >> simp [])
 >> qexistsl_tac [‘SUC r’, ‘t’]
 >> simp [ltree_paths_alt_ltree_el, Abbr ‘B’]
 >> ONCE_REWRITE_TAC [GSYM from_rose_11]
 >> Know ‘from_rose (to_rose (BT_expand X (BT' X N (SUC r)) t (SUC r))) =
          BT_expand X (BT' X N (SUC r)) t (SUC r)’
 >- (MATCH_MP_TAC to_rose_def \\
     MATCH_MP_TAC ltree_finite_BT_expand \\
     simp [ltree_paths_alt_ltree_el])
 >> Rewr'
 >> Know ‘from_rose (to_rose (ltree_insert f (BT' X N (SUC r)) t t0)) =
          ltree_insert f (BT' X N (SUC r)) t t0’
 >- (MATCH_MP_TAC to_rose_def \\
     MATCH_MP_TAC ltree_finite_ltree_insert \\
     simp [ltree_finite_BT_bnf, Abbr ‘t0’, ltree_paths_alt_ltree_el])
 >> Rewr'
 >> rw [BT_expand_def]
 >> ‘LENGTH t + SUC r = r'’ by rw [Abbr ‘r'’]
 >> POP_ORW >> simp []
QED

(* NOTE: “bnf M” has been weaken to “has_bnf M”, now the conclusions are
   suitable for doing induction (on indexed paths).

   Inputs: FINITE X /\ FV M SUBSET X UNION RANK r /\ has_bnf M

   Outputs: FINITE X /\ FV N (SUBSET FV M) SUBSET X UNION RANK r /\ has_bnf N
           lameta M N /\ BT_paths N = p INSERT BT_paths M
 *)
Theorem BT_expand_lemma2 :
    !X M p r B N.
       FINITE X /\ FV M SUBSET X UNION RANK r /\ has_bnf M /\
       p IN ltree_paths (BT' X M r) /\
       BT_expand X (BT' X M r) p r = B /\ N = BT_to_term B ==>
       lameta M N /\ has_bnf N /\ FV N SUBSET X UNION RANK r /\ BT' X N r = B
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘has_bnf M’ (MP_TAC o REWRITE_RULE [has_bnf_thm])
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘M0’ STRIP_ASSUME_TAC)
 >> Know ‘FV M0 SUBSET X UNION RANK r’
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M’ >> art [] \\
     MATCH_MP_TAC betastar_FV_SUBSET >> art [])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘M0’, ‘p’, ‘r’, ‘B’, ‘N’] BT_expand_lemma1)
 >> simp []
 >> Know ‘BT' X M0 r = BT' X M r’
 >- (MATCH_MP_TAC lameq_BT_cong >> art [] \\
     MATCH_MP_TAC lameq_SYM \\
     MATCH_MP_TAC betastar_lameq >> art [])
 >> Rewr'
 >> Q.PAT_X_ASSUM ‘N = BT_to_term B’ (ASSUME_TAC o SYM)
 >> simp [] >> STRIP_TAC
 (* applying takahashi_3_6_0 !! *)
 >> Know ‘has_bnf N’
 >- (MATCH_MP_TAC takahashi_3_6_0 \\
     Q.EXISTS_TAC ‘M0’ >> art [] \\
     MATCH_MP_TAC cc_eta_peta >> art [])
 >> DISCH_TAC
 >> ‘FV N = FV M0’ by PROVE_TAC [cc_eta_FV_EQN]
 >> simp []
 >> MATCH_MP_TAC lameta_TRANS
 >> Q.EXISTS_TAC ‘M0’
 >> CONJ_TAC
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC lameq_imp_lameta \\
      MATCH_MP_TAC betastar_lameq >> art [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC lameta_SYM \\
      MATCH_MP_TAC etaconversion_imp_lameta \\
      simp [conversion_rules] ]
QED

(* This lemma shows that expanding the Boehm tree at specific path ‘FRONT p’
   indeed extends the set of paths (by p) as expected.

   NOTE: When adding a set of new paths to an existing Boehm tree, the order
   is to make sure ‘ltree_el (BT' X M r) (FRONT p) = SOME (SOME (vs,y),SOME m)’
   and ‘LAST p = m’ always hold when adding the new path p.
 *)
Theorem ltree_paths_BT_expand :
    !X M p r m.
       FINITE X /\ FV M SUBSET X UNION RANK r /\ bnf M /\
       p IN ltree_paths (BT' X M r) /\
       ltree_branching (BT' X M r) p = SOME m ==>
       ltree_paths (BT_expand X (BT' X M r) p r) =
       SNOC m p INSERT ltree_paths (BT' X M r)
Proof
    rw [BT_expand_def]
 >> qabbrev_tac ‘r' = r + LENGTH p’
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘p’, ‘r’] BT_ltree_el_cases) >> rw []
 >> simp []
 >> qabbrev_tac ‘n = LENGTH vs’
 >> Q_TAC (RNEWS_TAC (“vs' :string list”, “r' :num”, “SUC n”)) ‘X’
 >> qabbrev_tac ‘v = LAST vs'’
 >> qmatch_abbrev_tac
   ‘ltree_paths (ltree_insert f (BT' X M r) p (BT_VAR v)) = _’
 >> qabbrev_tac ‘t0 = BT_VAR v’
 >> qabbrev_tac ‘t = BT' X M r’
 >> qabbrev_tac ‘a = SOME (vs,y)’
 (* applying ltree_insert_paths *)
 >> MP_TAC (Q.SPECL [‘f’, ‘p’, ‘t’, ‘m’, ‘t0’]
                    (INST_TYPE [alpha |-> “:BT_node”] ltree_insert_paths))
 >> simp []
 >> DISCH_THEN K_TAC
 >> simp [Abbr ‘t0’]
 >> SET_TAC []
QED

Theorem ltree_paths_BT_expand' :
    !X M p r m.
       FINITE X /\ FV M SUBSET X UNION RANK r /\ has_bnf M /\
       p IN ltree_paths (BT' X M r) /\
       ltree_branching (BT' X M r) p = SOME m ==>
       ltree_paths (BT_expand X (BT' X M r) p r) =
       SNOC m p INSERT ltree_paths (BT' X M r)
Proof
    rw [has_bnf_thm]
 >> ‘M == N’ by PROVE_TAC [betastar_lameq]
 >> Know ‘FV N SUBSET X UNION RANK r’
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M’ >> art [] \\
     MATCH_MP_TAC betastar_FV_SUBSET >> art [])
 >> DISCH_TAC
 >> Know ‘BT' X M r = BT' X N r’
 >- (MATCH_MP_TAC lameq_BT_cong >> art [])
 >> DISCH_THEN (fs o wrap)
 >> MP_TAC (Q.SPECL [‘X’, ‘N’, ‘p’, ‘r’, ‘m’] ltree_paths_BT_expand)
 >> simp []
QED

(* cf. takahashiS3Theory.eta_expand_def (for potential name conflicts only) *)
Overload eta_expand1 = “\X M p r. BT_to_term (BT_expand X (BT' X M r) p r)”

Definition eta_expand_upto_def :
    eta_expand_upto X M r paths =
    let s = paths DIFF ltree_paths (BT' X M r);
        n = CARD s;
        l = GENLIST (path_index s) n;
        f = \e p. eta_expand1 X e (FRONT p) r
    in
        FOLDL f M l
End

Theorem eta_expand_upto_thm :
    !X M M0 r paths.
       FINITE X /\ FV M SUBSET X UNION RANK r /\ has_bnf M /\
       ltree_paths (BT' X M r) SUBSET paths /\ FINITE paths /\
       parent_inclusive paths /\ sibling_inclusive paths /\
       M0 = eta_expand_upto X M r paths ==>
       FV M0 SUBSET X UNION RANK r /\ has_bnf M0 /\
       ltree_paths (BT' X M0 r) = paths /\ lameta M M0
Proof
    rpt GEN_TAC
 >> Q_TAC (UNBETA_TAC [eta_expand_upto_def]) ‘eta_expand_upto X M r paths’
 >> STRIP_TAC
 >> POP_ASSUM K_TAC (* M0 = ... *)
 >> qunabbrev_tac ‘l’
 >> qabbrev_tac ‘g = GENLIST (path_index s)’
 >> qabbrev_tac ‘L = \i. FOLDL f M (g i)’ >> simp []
 >> qabbrev_tac ‘s0 = ltree_paths (BT' X M r)’
 >> Know ‘FINITE s’
 >- (MATCH_MP_TAC SUBSET_FINITE_I \\
     Q.EXISTS_TAC ‘paths’ >> art [] \\
     qunabbrev_tac ‘s’ >> SET_TAC [])
 >> DISCH_TAC
 (* The induction plan:

    ltree_paths (BT' X (L 0) r) = s0
    ltree_paths (BT' X (L 1) r) = s0 + path_index 0
    ltree_paths (BT' X (L 2) r) = s0 + path_index s 0 + path_index s 1
    ...
    ltree_paths (BT' X (L n) r) =
  = s0 UNION (IMAGE (path_index s) (count n))  (by path_index_def)
  = s0 UION s = paths
  *)
 >> ‘s0 UNION s = paths’ by ASM_SET_TAC []
 >> Suff ‘!i. i <= n ==>
              FV (L i) SUBSET X UNION RANK r /\ has_bnf (L i) /\ lameta M (L i) /\
              ltree_paths (BT' X (L i) r) =
              s0 UNION (IMAGE (path_index s) (count i))’
 >- (DISCH_THEN (MP_TAC o Q.SPEC ‘n’) >> simp [] \\
     Suff ‘IMAGE (path_index s) (count n) = s’ >- simp [] \\
     METIS_TAC [path_index_def])
 >> Induct_on ‘i’
 >- simp [Abbr ‘L’, Abbr ‘g’, Abbr ‘f’, lameta_REFL]
 >> DISCH_TAC
 >> ‘i <= n’ by rw [] >> fs []
 >> simp [Abbr ‘L’, Abbr ‘g’, GENLIST, FOLDL_SNOC]
 >> qabbrev_tac ‘g = GENLIST (path_index s)’
 >> qabbrev_tac ‘L = \i. FOLDL f M (g i)’
 >> simp []
 >> qabbrev_tac ‘p = path_index s i’
 >> simp [Abbr ‘f’]
 >> qabbrev_tac ‘N = L i’
 (* applying BT_expand_lemma2 *)
 >> qabbrev_tac ‘p' = FRONT p’
 >> qabbrev_tac ‘B = BT_expand X (BT' X N r) p' r’
 >> Know ‘p IN s’
 >- (qunabbrev_tac ‘p’ \\
     MATCH_MP_TAC path_index_in_paths >> simp [Abbr ‘n’])
 >> DISCH_TAC
  (* p <> [] because “[] IN s0” and “p NOTIN s0” *)
 >> Know ‘p <> []’
 >- (Know ‘[] IN s0’ >- simp [Abbr ‘s0’] \\
     Q.PAT_X_ASSUM ‘p IN s’ MP_TAC \\
     simp [Abbr ‘s’] >> METIS_TAC [])
 >> DISCH_TAC
 (* applying parent_inclusive_def, to be needed by BT_expand_lemma2 *)
 >> Know ‘p' IN s0 UNION IMAGE (path_index s) (count i)’
 >- (‘p IN paths’ by fs [Abbr ‘s’] \\
     Know ‘p' IN paths’
     >- (fs [parent_inclusive_def] \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         Q.EXISTS_TAC ‘p’ >> art [] \\
         qunabbrev_tac ‘p'’ \\
         MATCH_MP_TAC IS_PREFIX_BUTLAST' >> art []) >> DISCH_TAC \\
     Cases_on ‘p' IN s0’ >> simp [IN_UNION] \\
    ‘p' IN s’ by ASM_SET_TAC [] \\
     MP_TAC (Q.SPEC ‘s’ path_index_def) >> rw [] \\
     CCONTR_TAC >> gs [NOT_LESS] \\
  (* find out the index of p' *)
     Q.PAT_X_ASSUM ‘p' IN s’ MP_TAC \\
     Q.PAT_X_ASSUM ‘s = IMAGE _ (count n)’ (fn th => REWRITE_TAC [Once th]) \\
     simp [NOT_LESS] \\
     Q.X_GEN_TAC ‘j’ >> STRONG_DISJ_TAC \\
     Q.PAT_X_ASSUM ‘!x. p' <> path_index s x \/ i <= x’
                   (MP_TAC o Q.SPEC ‘j’) >> rw [] \\
  (* j is the index of p', i is the index of p, j < i *)
     CCONTR_TAC >> fs [NOT_LESS_EQUAL] \\
    ‘i < n’ by rw [] \\
    ‘i = j \/ i < j’ by rw []
     >- (gs [] \\
         Q.PAT_X_ASSUM ‘FRONT p = p’ (MP_TAC o AP_TERM “LENGTH :num list -> num”) \\
         simp [LENGTH_FRONT] \\
         fs [GSYM LENGTH_NON_NIL]) \\
     Q.PAT_X_ASSUM ‘!j k. P’ (MP_TAC o Q.SPECL [‘i’, ‘j’]) >> rw [Abbr ‘p’] \\
     MATCH_MP_TAC LENGTH_LT_SHORTLEX \\
     qabbrev_tac ‘p = path_index s i’ \\
     Q.PAT_X_ASSUM ‘FRONT p = _’ (REWRITE_TAC o wrap o SYM) \\
     simp [LENGTH_FRONT] \\
     fs [GSYM LENGTH_NON_NIL])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘N’, ‘p'’, ‘r’, ‘B’, ‘BT_to_term B’] BT_expand_lemma2)
 >> simp [Abbr ‘B’]
 >> STRIP_TAC
 >> CONJ_TAC
 >- (MATCH_MP_TAC lameta_TRANS \\
     Q.EXISTS_TAC ‘N’ >> art [])
 (* applying ltree_paths_BT_expand' *)
 >> Know ‘s0 UNION IMAGE (path_index s) (count (SUC i)) =
          p INSERT ltree_paths (BT' X N r)’
 >- (simp [Abbr ‘p’] \\
     Suff ‘IMAGE (path_index s) (count (SUC i)) =
           path_index s i INSERT IMAGE (path_index s) (count i)’ >- SET_TAC [] \\
     simp [COUNT_SUC])
 >> Rewr'
 >> Q.PAT_X_ASSUM ‘ltree_paths (BT' X N r) = _’ (ASSUME_TAC o SYM)
 (* applying BT_ltree_el_cases *)
 >> MP_TAC (Q.SPECL [‘X’, ‘N’, ‘p'’, ‘r’] BT_ltree_el_cases') >> simp []
 >> impl_tac >- POP_ASSUM (simp o wrap o SYM)
 >> STRIP_TAC
 >> Suff ‘p = SNOC m p'’
 >- (Rewr' >> MATCH_MP_TAC ltree_paths_BT_expand' \\
     simp [ltree_branching_def] \\
     Q.PAT_X_ASSUM ‘_ = ltree_paths (BT' X N r)’ (simp o wrap o SYM))
 (* final goal: p = SNOC m p' *)
 >> ‘p = SNOC (LAST p) (FRONT p)’
      by ASM_SIMP_TAC std_ss [SNOC_LAST_FRONT] >> POP_ORW
 >> REWRITE_TAC [SNOC_11]
 >> qabbrev_tac ‘m' = LAST p’
 >> simp []
 >> qabbrev_tac ‘f  = path_index s’
 >> qabbrev_tac ‘B  = BT' X M r’
 >> qabbrev_tac ‘B' = BT' X N r’
 >> qabbrev_tac ‘N' = BT_to_term (BT_expand X B' p' r)’
 (* at the end, applying sibling_inclusive_def *)
 >> fs [sibling_inclusive_def]
 >> ‘p IN paths /\ p NOTIN s0’ by fs [Abbr ‘s’]
 >> Q.PAT_X_ASSUM ‘!p q. P’ (MP_TAC o Q.SPEC ‘p’) >> simp []
 >> STRIP_TAC
 >> fs [Abbr ‘L’]
 >> Q.PAT_X_ASSUM ‘i <= n’ K_TAC
 (* stage work *)
 >> MP_TAC (Q.SPECL [‘s’, ‘n’] path_index_thm)
 >> simp [HAS_SIZE] >> STRIP_TAC
 >> ‘ltree_branching B' p' = SOME m’ by rw [ltree_branching_def]
 (* strategy: proof by contradiction (reductum ad absurd) *)
 >> CCONTR_TAC
 >> ‘m' < m \/ m < m'’ by rw [] (* first case is easier *)
 (* Case 1 (m' < m):

       ((vs,y),m) at p'
        / |  \
      /   |   \
    /   p |    \
   0     m'   (m-1)

   If m' < m, then p IN BT_paths B' = s0 UNION IMAGE f (count i).
   But p NOTIN s0, thus p IN IMAGE f (count i). This is impossible because
   p = f i and “INJ f (count n) s”.
  *)
 >- (Know ‘p IN ltree_paths B'’
     >- (‘p = SNOC (LAST p) (FRONT p)’
            by ASM_SIMP_TAC std_ss [SNOC_LAST_FRONT] >> POP_ORW \\
         irule (iffLR ltree_branching_ltree_paths) >> simp []) \\
     Q.PAT_X_ASSUM ‘_ = ltree_paths B'’ (simp o wrap o SYM) \\
     simp [IN_UNION] \\
     Q.X_GEN_TAC ‘j’ \\
     simp [Abbr ‘p’] >> STRONG_DISJ_TAC \\
     CCONTR_TAC >> fs [] \\
    ‘i < n /\ j < n’ by rw [] \\
     fs [BIJ_DEF, INJ_DEF] \\
    ‘j = i’ by METIS_TAC [] >> fs [LT_LE])
 (* Case 2:

       ((vs,y),m) at p'
        / |  \  \__
      /   |   \    \_ p
    /     |    \     \
   0     m-1   (m)     m'

   If m < m' (LAST p), since p IN paths, we have

   (i) SNOC m p' IN paths (by [sibling_inclusive_def])
   (ii) SNOC m p' NOTIN BT_paths B' (by ltree_branching_ltree_paths)
   (iii) SNOC m p' NOTIN s0 /\ SNOC m p' NOTIN IMAGE f (count i)
   (iv) SNOC m p' IN s
   (v) SNOC m p' = f j, by (iv)
   (vi) i <= j (< n), by (iii)

   On the other hand, by [path_index_thm] we have
   (a) ltree_path_lt (SNOC m p') (SNOC m' p'), or
   (b) ltree_path_lt (SNOC m p') p
   (c) ltree_path_lt (f j) (f i)
   (d) j < i, conflicting with (iv) !!!
  *)
 >> Know ‘SNOC m p' IN paths’
 >- (FIRST_X_ASSUM MATCH_MP_TAC \\
     REWRITE_TAC [FRONT_SNOC, LAST_SNOC] >> simp [])
 >> DISCH_TAC
 >> Know ‘SNOC m p' NOTIN ltree_paths B'’
 >- (Know ‘SNOC m p' IN ltree_paths B' <=> m < m’
     >- (irule (GSYM ltree_branching_ltree_paths) >> simp []) >> Rewr \\
     simp [])
 >> Q.PAT_X_ASSUM ‘_ = ltree_paths B'’ (REWRITE_TAC o wrap o SYM)
 >> REWRITE_TAC [IN_UNION]
 >> CCONTR_TAC
 >> FULL_SIMP_TAC std_ss []
 >> ‘SNOC m p' IN s’ by rw [Abbr ‘s’]
 >> Know ‘?j. SNOC m p' = f j /\ j < n’
 >- (Q.PAT_X_ASSUM ‘BIJ f (count n) s’ MP_TAC \\
     SIMP_TAC std_ss [BIJ_DEF, IN_FUNSET, SURJ_DEF, IN_COUNT] \\
     METIS_TAC [])
 >> STRIP_TAC
 >> Know ‘i <= j’
 >- (SPOSE_NOT_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [GSYM NOT_LESS]) \\
     Q.PAT_X_ASSUM ‘SNOC m p' NOTIN IMAGE f (count i)’ MP_TAC \\
     SIMP_TAC std_ss [IN_IMAGE, IN_COUNT] \\
     Q.EXISTS_TAC ‘j’ >> art [])
 >> DISCH_TAC
 >> Know ‘ltree_path_lt (SNOC m p') (SNOC m' p')’
 >- (MATCH_MP_TAC ltree_path_lt_sibling \\
     REWRITE_TAC [FRONT_SNOC, LAST_SNOC] >> simp [])
 >> Q.PAT_X_ASSUM ‘SNOC m p' = f j’ (REWRITE_TAC o wrap)
 >> ASM_SIMP_TAC std_ss [Abbr ‘m'’, Abbr ‘p'’, SNOC_LAST_FRONT, Abbr ‘p’]
 >> ‘i < n’ by rw []
 >> simp []
QED

(* Corollary 10.4.3 (ii) [1, p.256]

   Also known as "Hilbert-Post completeness of lambda(beta)+eta".
 *)
Theorem lameta_complete :
    !X M N r. FINITE X /\ has_bnf M /\ has_bnf N /\ 0 < r /\
              FV M SUBSET X UNION RANK r /\
              FV N SUBSET X UNION RANK r ==>
              lameta M N \/
              inconsistent (conversion (RINSERT (beta RUNION eta) M N))
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘paths = ltree_paths (BT' X M r) UNION ltree_paths (BT' X N r)’
 >> Know ‘FINITE paths’
 >- (simp [Abbr ‘paths’, GSYM ltree_finite_alt_ltree_paths] \\
     simp [ltree_finite_BT_has_bnf])
 >> DISCH_TAC
 >> ‘ltree_paths (BT' X M r) SUBSET paths /\
     ltree_paths (BT' X N r) SUBSET paths’
      by (qunabbrev_tac ‘paths’ >> SET_TAC [])
 >> Know ‘parent_inclusive paths’
 >- (qunabbrev_tac ‘paths’ \\
     MATCH_MP_TAC parent_inclusive_union \\
     rw [parent_inclusive_ltree_paths])
 >> DISCH_TAC
 >> Know ‘sibling_inclusive paths’
 >- (qunabbrev_tac ‘paths’ \\
     MATCH_MP_TAC sibling_inclusive_union \\
     rw [sibling_inclusive_ltree_paths])
 >> DISCH_TAC
 >> qabbrev_tac ‘M0 = eta_expand_upto X M r paths’
 >> qabbrev_tac ‘N0 = eta_expand_upto X N r paths’
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘M0’, ‘r’, ‘paths’] eta_expand_upto_thm)
 >> simp [] >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘N’, ‘N0’, ‘r’, ‘paths’] eta_expand_upto_thm)
 >> simp [] >> STRIP_TAC
 >> Cases_on ‘M0 == N0’
 >- (DISJ1_TAC \\
     Q_TAC (TRANS_TAC lameta_TRANS) ‘M0’ >> art [] \\
     Q_TAC (TRANS_TAC lameta_TRANS) ‘N0’ \\
     reverse CONJ_TAC >- rw [lameta_SYM] \\
     MATCH_MP_TAC lameq_imp_lameta >> art [])
 >> DISJ2_TAC
 >> Know ‘incompatible M0 N0’
 >- (MATCH_MP_TAC distinct_bnf_imp_incompatible >> art [] \\
     qexistsl_tac [‘X’, ‘r’] >> simp [])
 >> rw [incompatible_def]
 >> MATCH_MP_TAC inconsistent_mono
 >> Q.EXISTS_TAC ‘asmlam {(M0,N0)}’ >> art []
 >> qabbrev_tac ‘R = RINSERT (beta RUNION eta) M N’
 >> simp [RSUBSET]
 >> HO_MATCH_MP_TAC asmlam_ind >> rw [] (* 7 subgoals, only 1st is hard *)
 >| [ (* goal 1 (of 7 *)
      MATCH_MP_TAC conversion_TRANS >> Q.EXISTS_TAC ‘M’ \\
      CONJ_TAC
      >- (irule (REWRITE_RULE [RSUBSET] conversion_monotone) \\
          Q.EXISTS_TAC ‘beta RUNION eta’ \\
          CONJ_TAC >- rw [Abbr ‘R’, RINSERT] \\
          rw [beta_eta_lameta, Once lameta_SYM]) \\
      MATCH_MP_TAC conversion_TRANS >> Q.EXISTS_TAC ‘N’ \\
      reverse CONJ_TAC
      >- (irule (REWRITE_RULE [RSUBSET] conversion_monotone) \\
          Q.EXISTS_TAC ‘beta RUNION eta’ \\
          CONJ_TAC >- rw [Abbr ‘R’, RINSERT] \\
          rw [beta_eta_lameta]) \\
      Suff ‘R M N’ >- rw [conversion_rules] \\
      rw [Abbr ‘R’, RINSERT],
      (* goal 2 (of 7) *)
      Suff ‘R (LAM x M' @@ N') ([N'/x] M')’ >- rw [conversion_rules] \\
      rw [Abbr ‘R’] >> MATCH_MP_TAC (REWRITE_RULE [RSUBSET] RSUBSET_RINSERT) \\
      rw [RUNION] >> DISJ1_TAC \\
      rw [beta_def] >> qexistsl_tac [‘x’, ‘M'’] >> rw [],
      (* goal 3 (of 7) *)
      rw [conversion_rules],
      (* goal 4 (of 7) *)
      METIS_TAC [conversion_rules],
      (* goal 5 (of 7) *)
      PROVE_TAC [conversion_compatible, compatible_def, rightctxt, rightctxt_thm],
      (* goal 6 (of 7) *)
      PROVE_TAC [conversion_compatible, compatible_def, leftctxt],
      (* goal 7 (of 7) *)
      PROVE_TAC [conversion_compatible, compatible_def, absctxt] ]
QED

(* NOTE: “has_benf M /\ has_benf N” is used instead of “has_bnf M /\ has_bnf N” *)
Theorem lameta_complete_final :
    !M N. has_benf M /\ has_benf N ==>
          lameta M N \/ inconsistent (conversion (RINSERT (beta RUNION eta) M N))
Proof
    rw [has_benf_has_bnf]
 >> MP_TAC (Q.SPECL [‘FV M UNION FV N’, ‘M’, ‘N’, ‘1’] lameta_complete)
 >> simp []
 >> DISCH_THEN MATCH_MP_TAC
 >> SET_TAC []
QED

Theorem HP_complete_lameta :
    HP_complete (UNCURRY eta) has_benf
Proof
    RW_TAC std_ss [HP_complete_def, GSYM eta_extend_alt_conversion,
                   GSYM lameta_asmlam]
 >> MATCH_MP_TAC lameta_complete_final >> art []
QED

val _ = export_theory ();
val _ = html_theory "lameta_complete";

(* References:

 [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
     College Publications, London (1984).
 [2] https://en.wikipedia.org/wiki/Corrado_Böhm (UOK)
 [3] Böhm, C.: Alcune proprietà delle forme β-η-normali nel λ-K-calcolo. (UOK)
     Pubblicazioni dell'IAC 696, 1-19 (1968)
     English translation: "Some properties of beta-eta-normal forms in the
     lambda-K-calculus" (https://arxiv.org/abs/2502.05774)
 *)
