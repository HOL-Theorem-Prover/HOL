(* ========================================================================== *)
(* FILE    : lameta_completeScript.sml (chap10_4Script.sml)                   *)
(* TITLE   : Completeness of (Untyped) Lambda-Calculus [1, Chapter 10.4]      *)
(*                                                                            *)
(* AUTHORS : 2024-2025 The Australian National University (Chun Tian)         *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open hurdUtils arithmeticTheory pred_setTheory listTheory rich_listTheory
     ltreeTheory llistTheory relationTheory tautLib topologyTheory;

open termTheory basic_swapTheory appFOLDLTheory chap2Theory chap3Theory NEWLib
     horeductionTheory solvableTheory head_reductionTheory head_reductionLib
     nomsetTheory standardisationTheory boehmTheory takahashiS3Theory;

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
    equivalent (M :term) (N :term) =
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
 >> ‘solvable M /\ solvable N’ by PROVE_TAC [hnf_has_hnf, solvable_iff_has_hnf]
 >> RW_TAC std_ss [equivalent_def, principle_hnf_reduce]
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
       by rw [solvable_iff_has_hnf, hnf_has_hnf]
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

(* NOTE: ‘0 < r’ is not necessary but makes this proof much easier. *)
Theorem subtree_equiv_alt_equivalent :
    !X M N r. FINITE X /\ 0 < r /\
              FV M SUBSET X UNION RANK r /\
              FV N SUBSET X UNION RANK r ==>
             (subtree_equiv X M N [] r <=> equivalent M N)
Proof
    rpt STRIP_TAC
 (* special cases (unsolvable) *)
 >> reverse (Cases_on ‘solvable M’)
 >- (rw [subtree_equiv_def, equivalent_def, BT_of_unsolvables, ltree_el_def] \\
     reverse EQ_TAC
     >- rw [BT_of_unsolvables, ltree_el_def] \\
     DISCH_TAC \\
     Know ‘ltree_el (BT' X N r) [] = SOME bot’
     >- (MATCH_MP_TAC ltree_equiv_some_bot_imp >> art []) \\
     simp [Once MONO_NOT_EQ] >> DISCH_TAC \\
     rw [BT_def, Once ltree_unfold, BT_generator_def, ltree_el_def])
 >> reverse (Cases_on ‘solvable N’)
 >- (rw [subtree_equiv_def, equivalent_def, BT_of_unsolvables, ltree_el_def] \\
     CCONTR_TAC >> fs [] \\
     Know ‘ltree_el (BT' X M r) [] = SOME bot’
     >- (MATCH_MP_TAC ltree_equiv_some_bot_imp' >> art []) \\
     rw [BT_def, Once ltree_unfold, BT_generator_def, ltree_el_def])
 (* stage work, now both M and N are solvable *)
 >> RW_TAC std_ss [subtree_equiv_def, equivalent_def]
 >> qabbrev_tac ‘Y = FV M UNION FV N’
 >> Q_TAC (UNBETA_TAC [BT_def, Once ltree_unfold, BT_generator_def]) ‘BT' X M r’
 >> Q_TAC (UNBETA_TAC [BT_def, Once ltree_unfold, BT_generator_def]) ‘BT' X N r’
 >> simp [GSYM BT_def, LMAP_fromList]
 >> rw [ltree_el_def, Abbr ‘l’, Abbr ‘l'’, head_equivalent_def]
 (* renaming some abbreviations *)
 >> rename1 ‘y3 = y4 /\ LENGTH vs1 + LENGTH Ms2 = LENGTH vs2 + LENGTH Ms1 <=>
             y1 = y2 /\ m2 + n1 = m1 + n2’
 >> qunabbrev_tac ‘M0'’
 >> qabbrev_tac ‘N0 = principle_hnf N’
 >> qunabbrev_tac ‘n'''’
 >> qunabbrev_tac ‘M1''’
 >> qabbrev_tac ‘N1' = principle_hnf (N0 @* MAP VAR vs2)’
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
 >> qunabbrev_tac ‘y3’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs0 :string list”,
                    “y3 :string”, “args3 :term list”)) ‘M1'’ >> rfs []
 >> qunabbrev_tac ‘y4’
 >> Q_TAC (HNF_TAC (“N0 :term”, “vs0 :string list”,
                    “y4 :string”, “args4 :term list”)) ‘N1'’ >> rfs []
 >> simp [Abbr ‘Ms1’, Abbr ‘Ms2’]
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

(*---------------------------------------------------------------------------*
 *  Boehm trees of beta/eta equivalent terms
 *---------------------------------------------------------------------------*)

(* Proposition 10.1.6 [1, p.219]

   M -h->* M0
  /          \b*
 ==          +---[lameq_CR] y1 = y2, n1 = n2, m1 = m2
  \         /b*
   N -h->* Ns
 *)
Theorem lameq_BT_cong :
    !X M N r. FINITE X /\ FV M UNION FV N SUBSET X /\ M == N ==>
              BT' X M r = BT' X N r
Proof
    RW_TAC std_ss []
 >> reverse (Cases_on ‘solvable M’)
 >- (‘unsolvable N’ by METIS_TAC [lameq_solvable_cong] \\
     rw [BT_of_unsolvables])
 >> ‘solvable N’ by METIS_TAC [lameq_solvable_cong]
 (* applying ltree_bisimulation *)
 >> rw [ltree_bisimulation]
 (* NOTE: ‘solvable P /\ solvable Q’ cannot be added here *)
 >> Q.EXISTS_TAC
     ‘\x y. ?P Q r. FV P UNION FV Q SUBSET X UNION RANK r /\
                    P == Q /\ x = BT' X P r /\ y = BT' X Q r’
 >> BETA_TAC
 >> CONJ_TAC
 >- (qexistsl_tac [‘M’, ‘N’, ‘r’] >> simp [] \\
     Q.PAT_X_ASSUM ‘FV M UNION FV N SUBSET X’ MP_TAC \\
     Q.PAT_X_ASSUM ‘FINITE X’ MP_TAC \\
     SET_TAC [])
 (* stage work *)
 >> qx_genl_tac [‘a1’, ‘ts1’, ‘a2’, ‘ts2’] >> STRIP_TAC
 >> qabbrev_tac ‘P0 = principle_hnf P’
 >> qabbrev_tac ‘Q0 = principle_hnf Q’
 >> qabbrev_tac ‘n  = LAMl_size P0’
 >> qabbrev_tac ‘n' = LAMl_size Q0’
 >> qabbrev_tac ‘vs = RNEWS r n  X’
 >> qabbrev_tac ‘vs'= RNEWS r n' X’
 >> qabbrev_tac ‘P1 = principle_hnf (P0 @* MAP VAR vs)’
 >> qabbrev_tac ‘Q1 = principle_hnf (Q0 @* MAP VAR vs')’
 >> qabbrev_tac ‘Ps = hnf_children P1’
 >> qabbrev_tac ‘Qs = hnf_children Q1’
 >> qabbrev_tac ‘y  = hnf_head P1’
 >> qabbrev_tac ‘y' = hnf_head Q1’
 (* applying ltree_unfold *)
 >> Q.PAT_X_ASSUM ‘_ = BT' X Q r’ MP_TAC
 >> simp [BT_def, Once ltree_unfold, BT_generator_def]
 >> Q.PAT_X_ASSUM ‘_ = BT' X P r’ MP_TAC
 >> simp [BT_def, Once ltree_unfold, BT_generator_def]
 >> NTAC 2 STRIP_TAC
 (* easy case: unsolvable P (and Q) *)
 >> reverse (Cases_on ‘solvable P’)
 >- (‘unsolvable Q’ by PROVE_TAC [lameq_solvable_cong] >> fs [] \\
     rw [llist_rel_def, LLENGTH_MAP])
 (* now both P and Q are solvable *)
 >> ‘solvable Q’ by PROVE_TAC [lameq_solvable_cong]
 >> fs []
 (* applying lameq_principle_hnf_size_eq' *)
 >> Know ‘n = n' /\ vs = vs'’
 >- (reverse CONJ_ASM1_TAC >- rw [Abbr ‘vs’, Abbr ‘vs'’] \\
     qunabbrevl_tac [‘n’, ‘n'’, ‘P0’, ‘Q0’] \\
     MATCH_MP_TAC lameq_principle_hnf_size_eq' >> art [])
 (* clean up now duplicated abbreviations: n' and vs' *)
 >> qunabbrevl_tac [‘n'’, ‘vs'’]
 >> DISCH_THEN (rfs o wrap o GSYM)
 (* proving y = y' *)
 >> STRONG_CONJ_TAC
 >- (MP_TAC (Q.SPECL [‘r’, ‘X’, ‘P’, ‘Q’, ‘P0’, ‘Q0’, ‘n’, ‘vs’, ‘P1’, ‘Q1’]
                     lameq_principle_hnf_head_eq) \\
     simp [GSYM solvable_iff_has_hnf])
 >> DISCH_THEN (rfs o wrap o GSYM)
 >> qunabbrevl_tac [‘y’, ‘y'’]
 (* applying lameq_principle_hnf_thm' *)
 >> MP_TAC (Q.SPECL [‘r’, ‘X’, ‘P’, ‘Q’, ‘P0’, ‘Q0’, ‘n’, ‘vs’, ‘P1’, ‘Q1’]
                     lameq_principle_hnf_thm)
 >> simp [GSYM solvable_iff_has_hnf]
 >> rw [llist_rel_def, LLENGTH_MAP, EL_MAP]
 >> Cases_on ‘i < LENGTH Ps’ >> fs [LNTH_fromList, EL_MAP]
 >> Q.PAT_X_ASSUM ‘(EL i Ps,SUC r) = z’  (ONCE_REWRITE_TAC o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘(EL i Qs,SUC r) = z'’ (ONCE_REWRITE_TAC o wrap o SYM)
 >> qexistsl_tac [‘EL i Ps’, ‘EL i Qs’, ‘SUC r’] >> simp []
 >> qabbrev_tac ‘n = LAMl_size Q0’
 >> qabbrev_tac ‘m = LENGTH Qs’
 >> CONJ_TAC (* 2 symmetric subgoals *)
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC subterm_induction_lemma' \\
      qexistsl_tac [‘P’,‘P0’, ‘n’, ‘m’, ‘vs’, ‘P1’] >> simp [] \\
      qunabbrev_tac ‘vs’ \\
      Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’ \\
     ‘DISJOINT (set vs) (FV P0)’ by METIS_TAC [subterm_disjoint_lemma'] \\
      Q_TAC (HNF_TAC (“P0 :term”, “vs :string list”,
                      “y  :string”, “args :term list”)) ‘P1’ \\
     ‘TAKE (LAMl_size P0) vs = vs’ by rw [] \\
      POP_ASSUM (rfs o wrap) \\
      Q.PAT_X_ASSUM ‘LENGTH Ps = m’ (REWRITE_TAC o wrap o SYM) \\
      AP_TERM_TAC >> simp [Abbr ‘Ps’],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC subterm_induction_lemma' \\
      qexistsl_tac [‘Q’,‘Q0’, ‘n’, ‘m’, ‘vs’, ‘Q1’] >> simp [] \\
      qunabbrev_tac ‘vs’ \\
      Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’ \\
     ‘DISJOINT (set vs) (FV Q0)’ by METIS_TAC [subterm_disjoint_lemma'] \\
      Q_TAC (HNF_TAC (“Q0 :term”, “vs :string list”,
                      “y  :string”, “args :term list”)) ‘Q1’ \\
     ‘TAKE (LAMl_size Q0) vs = vs’ by rw [] \\
      POP_ASSUM (rfs o wrap) \\
      qunabbrev_tac ‘m’ \\
      AP_TERM_TAC >> simp [Abbr ‘Qs’] ]
QED

(*---------------------------------------------------------------------------*
 *  BT_paths and BT_valid_paths
 *---------------------------------------------------------------------------*)

Definition BT_paths_def :
    BT_paths M = ltree_paths (BT' (FV M) M 0)
End

Theorem BT_paths_nil[simp] :
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

Theorem BT_paths_eq_subterm_not_none :
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

Theorem BT_valid_paths_SUBSET_paths :
    !M. BT_valid_paths M SUBSET BT_paths M
Proof
    rw [SUBSET_DEF, BT_valid_paths_def]
QED

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
    !q M N. q <<= p /\ MEM M Ms /\ MEM N Ms ==> subtree_equiv X M N q r
End

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

(* Lemma 10.3.11 [1. p.251] *)
Theorem agree_upto_lemma :
    !X Ms p r.
       FINITE X /\ Ms <> [] /\ p <> [] /\ 0 < r /\
      (!M. MEM M Ms ==> FV M SUBSET X UNION RANK r) /\
      (!M. MEM M Ms ==> p IN ltree_paths (BT' X M r)) ==>
       ?pi. Boehm_transform pi /\
           (!M. MEM M Ms ==> is_ready' (apply pi M)) /\
           (!M. MEM M Ms ==> FV (apply pi M) SUBSET X UNION RANK r) /\
           (!M. MEM M Ms ==> p IN ltree_paths (BT' X (apply pi M) r)) /\
           (!q M. MEM M Ms /\ q <<= p ==>
                 (solvable (subterm' X M q r) <=>
                  solvable (subterm' X (apply pi M) q r))) /\
           (agree_upto X Ms p r ==>
            agree_upto X (apply pi Ms) p r) /\
           !M N. MEM M Ms /\ MEM N Ms /\
                 subtree_equiv X (apply pi M) (apply pi N) p r ==>
                 subtree_equiv X M N p r
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘Ms’, ‘p’, ‘r’] subtree_equiv_lemma)
 >> simp [BIGUNION_IMAGE_SUBSET, EVERY_MEM, MEM_MAP]
 >> STRIP_TAC
 >> Q.EXISTS_TAC ‘pi’ >> rw []
 >| [ (* goal 1 (of 4) *)
      FIRST_X_ASSUM MATCH_MP_TAC \\
      Q.EXISTS_TAC ‘M’ >> art [],
      (* goal 2 (of 4) *)
      FIRST_X_ASSUM MATCH_MP_TAC \\
      Q.EXISTS_TAC ‘M’ >> art [],
      (* goal 3 (of 4) *)
      FIRST_X_ASSUM MATCH_MP_TAC \\
      Q.EXISTS_TAC ‘M’ >> art [],
      (* goal 4 (of 4) *)
      MATCH_MP_TAC subtree_equiv_imp_agree_upto >> rw [] \\
      METIS_TAC [] ]
QED

(* Definition 10.3.10 (ii) [1, p.251]

   NOTE: This definition now assumes ’p IN ltree_paths (BT' X M r)’.
 *)
Definition is_faithful_def :
    is_faithful p X Ms pi r <=>
        (!M. MEM M Ms ==> (p IN BT_valid_paths M <=> solvable (apply pi M))) /\
         !M N. MEM M Ms /\ MEM N Ms ==>
              (subtree_equiv X M N p r <=>
               equivalent (apply pi M) (apply pi N))
End

Overload is_faithful' = “is_faithful []”

Theorem is_faithful' :
    !X Ms pi r. FINITE X /\ 0 < r /\
               (!M. MEM M Ms ==> FV M SUBSET X UNION RANK r) ==>
      (is_faithful' X Ms pi r <=>
        (!M. MEM M Ms ==> (solvable M <=> solvable (apply pi M))) /\
         !M N. MEM M Ms /\ MEM N Ms ==>
              (equivalent M N <=>
               equivalent (apply pi M) (apply pi N)))
Proof
    rw [is_faithful_def]
 >> Suff ‘!M N. MEM M Ms /\ MEM N Ms ==>
               (subtree_equiv X M N [] r <=> equivalent M N)’
 >- METIS_TAC []
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC subtree_equiv_alt_equivalent >> rw []
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
               ?pi. Boehm_transform pi /\ is_faithful p X Ms pi r
Proof
    Q.X_GEN_TAC ‘X’
 >> Induct_on ‘p’
 >- (rpt STRIP_TAC >> Q.EXISTS_TAC ‘[]’ >> rw [is_faithful'])
 (* stage work *)
 >> rw [is_faithful_def]
 (* trivial case: all unsolvable *)
 >> Cases_on ‘!M. MEM M Ms ==> unsolvable M’
 >- (Q.EXISTS_TAC ‘[]’ \\
     reverse (rw [])
     >- (fs [agree_upto_def] \\
         Know ‘equivalent M N <=> subtree_equiv X M N [] r’
         >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
             MATCH_MP_TAC subtree_equiv_alt_equivalent >> art [] \\
             fs [BIGUNION_IMAGE_SUBSET]) >> Rewr' \\
         FIRST_X_ASSUM irule >> rw []) \\
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
     Q.PAT_X_ASSUM ‘!q M N. q <<= h::p /\ MEM M (apply p0 Ms) /\ _ ==> _’
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
           ltree_paths_alt, ltree_el_def] \\
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
     Q.PAT_X_ASSUM ‘!q M N. q <<= h::p /\ MEM M (apply p0 Ms) /\ _ ==> _’
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
     simp [LMAP_fromList, ltree_paths_alt, ltree_el_def, GSYM BT_def] \\
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
               ?pi. Boehm_transform pi /\ is_faithful p X Ms' pi r'’
      (MP_TAC o Q.SPECL [‘apply pi' Ms’, ‘SUC r’])
 >> simp [is_faithful_def]
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
     Q.PAT_X_ASSUM ‘!M N. _ ==> (subtree_equiv X M N p (SUC r) <=>
                                 equivalent (apply p2 M) (apply p2 N))’
                   (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ] o
                    Q.SPECL [‘t1’, ‘t2’]) \\
     simp [Abbr ‘t1’, Abbr ‘t2’] >> DISCH_THEN K_TAC \\
  (* now “equivalent” is elimianted *)
     Know ‘subtree_equiv X (M a) (M b) (h::p) r’
     >- (Q.PAT_X_ASSUM ‘agree_upto X Ms (h::p) r’ MP_TAC \\
         rw [agree_upto_def] \\
         POP_ASSUM MATCH_MP_TAC >> simp [EL_MEM, Abbr ‘M’]) >> Rewr \\
     qabbrev_tac ‘t1 = apply p0 (M a)’ \\
     qabbrev_tac ‘t2 = apply p0 (M b)’ \\
     Q.PAT_X_ASSUM ‘agree_upto X (apply p0 Ms) (h::p) r’ MP_TAC \\
     rw [agree_upto_def] \\
     POP_ASSUM (MP_TAC o Q.SPECL [‘h::p’, ‘t1’, ‘t2’]) \\
     simp [Abbr ‘t1’, Abbr ‘t2’] \\
     impl_tac
     >- (rw [MEM_MAP] >| (* 2 subgoals *)
         [ Q.EXISTS_TAC ‘M a’ >> simp [EL_MEM, Abbr ‘M’],
           Q.EXISTS_TAC ‘M b’ >> simp [EL_MEM, Abbr ‘M’] ]) \\
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
 >> Q.PAT_X_ASSUM ‘!M N. _ ==> (subtree_equiv X M N p (SUC r) <=> _)’ K_TAC
 >> Q.PAT_X_ASSUM ‘!M N. _ ==> subtree_equiv X M N (h::p) r’          K_TAC
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
 >> Q.PAT_X_ASSUM ‘!q M. MEM M Ms /\ q <<= h::p ==> _’
      (MP_TAC o Q.SPECL [‘h::p’, ‘M (i :num)’])
 >> impl_tac >- simp [EL_MEM, Abbr ‘M’]
 >> Rewr'
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

Theorem is_faithful_swap :
    !p X M N pi r. is_faithful p X [M; N] pi r <=> is_faithful p X [N; M] pi r
Proof
    rw [is_faithful_def]
 >> METIS_TAC []
QED

(*---------------------------------------------------------------------------*
 *  Separability of lambda terms
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

val _ = export_theory ();
val _ = html_theory "lameta_complete";

(* References:

 [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
     College Publications, London (1984).
 [2] https://en.wikipedia.org/wiki/Corrado_Böhm (UOK)
 [3] Böhm, C.: Alcune proprietà delle forme β-η-normali nel λ-K-calcolo. (UOK)
     Pubblicazioni dell'IAC 696, 1-19 (1968)
     English translation: "Some properties of beta-eta-normal forms in the
     lambda-K-calculus".
 *)
