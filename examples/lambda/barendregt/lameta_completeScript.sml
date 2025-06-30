(* ========================================================================== *)
(* FILE    : lameta_completeScript.sml (chap10_4Script.sml)                   *)
(* TITLE   : Completeness of (Untyped) Lambda-Calculus [1, Chapter 10.4]      *)
(*                                                                            *)
(* AUTHORS : 2024 - 2025 The Australian National University (Chun Tian)       *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open hurdUtils combinTheory tautLib arithmeticTheory pred_setTheory listTheory
     rich_listTheory llistTheory ltreeTheory relationTheory topologyTheory
     iterateTheory optionTheory numLib listLib;

open nomsetTheory basic_swapTheory NEWLib termTheory appFOLDLTheory chap2Theory
     chap3Theory horeductionTheory reductionEval solvableTheory takahashiS3Theory
     head_reductionTheory head_reductionLib standardisationTheory boehmTheory
     chap4Theory;

(* enable basic monad support *)
open monadsyntax;
val _ = enable_monadsyntax ();
val _ = enable_monad "option";

local open set_relationTheory in
   val rel_to_reln_IS_UNCURRY = rel_to_reln_IS_UNCURRY;
end

val _ = new_theory "lameta_complete";

(* These theorems usually give unexpected results, should be applied manually *)
val _ = temp_delsimps [
   "lift_disj_eq", "lift_imp_disj",
   "IN_UNION",     (* |- !s t x. x IN s UNION t <=> x IN s \/ x IN t *)
   "APPEND_ASSOC"  (* |- !l1 l2 l3. l1 ++ (l2 ++ l3) = l1 ++ l2 ++ l3 *)
];

val _ = hide "B";
val _ = hide "C";
val _ = hide "W";
val _ = hide "Y";

(* some proofs here are large with too many assumptions *)
val _ = set_trace "Goalstack.print_goal_at_top" 0;

fun PRINT_TAC pfx g = (print (pfx ^ "\n"); ALL_TAC g);

(* Disable some conflicting overloads from labelledTermsTheory *)
Overload FV  = “supp term_pmact”
Overload VAR = “term$VAR”

(*---------------------------------------------------------------------------*
 *  head equivalence
 *---------------------------------------------------------------------------*)

(* Definition 10.2.21 (i) [1, p.238]

   NOTE: For ‘y1 = y2’ to be meaningful, here we assumed that vs1 and vs2
   share the same prefix, i.e. either vs1 <<= vs2 or vs2 <<= vs1. In reality,
   we have ‘vs1 = RNEWS r n1 X /\ vs2 = RNEWS r n2 X’ for some X and r.
 *)
Definition head_equivalent_def :
    head_equivalent ((a1,m1) :BT_node # num option)
                    ((a2,m2) :BT_node # num option) =
    case (a1,a2) of
      (SOME (vs1,y1),SOME (vs2,y2)) =>
       y1 = y2 /\ LENGTH vs1 + THE m2 = LENGTH vs2 + THE m1
    | (SOME _,NONE) => F
    | (NONE,SOME _) => F
    | (NONE,NONE)   => T
End

Theorem head_equivalent_refl[simp] :
    head_equivalent A A
Proof
    Cases_on ‘A’ >> rw [head_equivalent_def]
 >> Cases_on ‘q’ >> rw []
 >> Cases_on ‘x’ >> rw []
QED

Theorem head_equivalent_sym :
    !A B. head_equivalent A B ==> head_equivalent B A
Proof
    qx_genl_tac [‘A’, ‘B’]
 >> Cases_on ‘A’ >> Cases_on ‘B’  >> simp [head_equivalent_def]
 >> Cases_on ‘q’ >> Cases_on ‘q'’ >> simp []
 >> Cases_on ‘x’ >> Cases_on ‘x'’ >> simp []
QED

Theorem head_equivalent_comm :
    !A B. head_equivalent A B <=> head_equivalent B A
Proof
    rpt GEN_TAC
 >> EQ_TAC >> rw [head_equivalent_sym]
QED

(* Definition 10.2.21 (ii) [1, p.238] *)
Overload ltree_equiv = “OPTREL head_equivalent”

Theorem ltree_equiv_refl[simp] :
    ltree_equiv A A
Proof
    MATCH_MP_TAC OPTREL_refl >> rw []
QED

Theorem ltree_equiv_sym :
    !A B. ltree_equiv A B ==> ltree_equiv B A
Proof
    rpt GEN_TAC
 >> Cases_on ‘A’ >> Cases_on ‘B’ >> rw [OPTREL_THM]
 >> rw [Once head_equivalent_comm]
QED

Theorem ltree_equiv_comm :
    !A B. ltree_equiv A B <=> ltree_equiv B A
Proof
    rpt STRIP_TAC
 >> EQ_TAC >> rw [ltree_equiv_sym]
QED

Theorem ltree_equiv_some_bot_imp :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              ltree_equiv (SOME bot) (ltree_el (BT' X M r) p) ==>
              ltree_el (BT' X M r) p = SOME bot
Proof
    rw [OPTREL_def]
 >> Cases_on ‘y0’ >> fs [head_equivalent_def]
 >> Cases_on ‘q’ >> fs []
 >> METIS_TAC [BT_ltree_el_eq_some_none]
QED

(* |- !X M p r.
        FINITE X /\ FV M SUBSET X UNION RANK r /\
        ltree_equiv (ltree_el (BT' X M r) p) (SOME bot) ==>
        ltree_el (BT' X M r) p = SOME bot
 *)
Theorem ltree_equiv_some_bot_imp' =
    ONCE_REWRITE_RULE [ltree_equiv_comm] ltree_equiv_some_bot_imp

(* Definition 10.2.32 (v) [1, p.245] *)
Definition subtree_equiv_def :
    subtree_equiv X M N p r =
    ltree_equiv (ltree_el (BT' X M r) p) (ltree_el (BT' X N r) p)
End

Theorem subtree_equiv_refl[simp] :
    subtree_equiv X M M p r
Proof
    rw [subtree_equiv_def]
QED

Theorem subtree_equiv_comm :
    !X M N p r. subtree_equiv X M N p r <=> subtree_equiv X N M p r
Proof
    rw [subtree_equiv_def, Once ltree_equiv_comm]
QED

Theorem hreduce_subtree_equiv_cong :
    !X M M' N N' p r. M -h->* M' /\ N -h->* N' ==>
                     (subtree_equiv X M N p r <=> subtree_equiv X M' N' p r)
Proof
    rw [subtree_equiv_def]
 >> Suff ‘BT' X M r = BT' X M' r /\ BT' X N r = BT' X N' r’
 >- DISCH_THEN (fs o wrap)
 >> rw [hreduce_BT_cong]
QED

(* This HUGE theorem is an improved version of Lemma 10.3.11 [1. p.251], to be
   proved later in ‘lameta_completeTheory’ as [agree_upto_lemma].

   NOTE: ‘p <> []’ must be added, otherwise each N in Ns cannot be "is_ready".

   NOTE: ‘!X M. MEM M Ns ==> subterm X M p <> NONE’ will be later assumed for
   non-trivial cases. If any M in Ns doesn't satisfy this requirements, then
  ‘subterm X M p = NONE’ (the unsolvable case) and doesn't have contributions
   in ‘pi’.

   On the other hand, if any M in Ns is unsolvable (and p <> []), then p cannot
   be in ‘ltree_paths (BT X M)’. Thus all terms in Ns are solvable. Let's first
   put ‘EVERY solvable Ns’ in assumption to focus on the non-trivial part of
   this proof.

   NOTE: ‘0 < r’ is to ensure a non-empty ‘RANK r’ for allocating fresh names
   on the construction of Boehm transform ‘pi’.

   NOTE: This is the LAST theorem of the current theory, because this proof is
   so long. Further results (plus users of this lemma) are to be found in the
   next lameta_completeTheory.

   NOTE: Added the following conclusion for the need of [agree_upto_thm]:

    !q M. MEM M Ms /\ q <<= p ==>
         (solvable (subterm' X M q r) <=>
          solvable (subterm' X (apply pi M) q r))
 *)
Theorem subtree_equiv_lemma_explicit :
    !X Ms p r.
       FINITE X /\ p <> [] /\ 0 < r /\ Ms <> [] /\
       BIGUNION (IMAGE FV (set Ms)) SUBSET X UNION RANK r /\
       EVERY (\M. subterm X M p r <> NONE) Ms ==>
       let pi = Boehm_construction X Ms p in
           Boehm_transform pi /\
           EVERY is_ready' (apply pi Ms) /\
           EVERY (\M. p IN ltree_paths (BT' X M r)) (apply pi Ms) /\
          (!q M. MEM M Ms /\ q <<= p ==>
                (solvable (subterm' X M q r) <=>
                 solvable (subterm' X (apply pi M) q r))) /\
           !q M N. MEM M Ms /\ MEM N Ms /\ q <<= p ==>
                  (subtree_equiv X M N q r <=>
                   subtree_equiv X (apply pi M) (apply pi N) q r)
Proof
    rpt GEN_TAC >> simp [LET_DEF]
 >> STRIP_TAC
 >> qabbrev_tac ‘Y = BIGUNION (IMAGE FV (set Ms))’
 >> ‘FINITE Y’ by (rw [Abbr ‘Y’] >> rw [])
 >> qabbrev_tac ‘pi' = Boehm_construction X Ms p’
 >> CONJ_ASM1_TAC
 >- rw [Abbr ‘pi'’, Boehm_construction_transform]
 (* original steps *)
 >> Q.PAT_X_ASSUM ‘EVERY _ Ms’ MP_TAC
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [EVERY_EL]))
 >> qabbrev_tac ‘k = LENGTH Ms’
 >> qabbrev_tac ‘M = \i. EL i Ms’ >> fs []
 >> Know ‘!i. i < k ==> FV (M i) SUBSET X UNION RANK r’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘Y SUBSET X UNION RANK r’ MP_TAC \\
     rw [Abbr ‘Y’, SUBSET_DEF, IN_BIGUNION_IMAGE] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘M i’ >> art [] \\
     rw [Abbr ‘M’, EL_MEM])
 >> DISCH_TAC
 (* now derive some non-trivial assumptions *)
 >> ‘!i. i < k ==> (!q. q <<= p ==> subterm X (M i) q r <> NONE) /\
                    !q. q <<= FRONT p ==> solvable (subterm' X (M i) q r)’
       by METIS_TAC [subterm_solvable_lemma]
 (* convert previous assumption into easier forms for MATCH_MP_TAC *)
 >> ‘(!i q. i < k /\ q <<= p ==> subterm X (M i) q r <> NONE) /\
     (!i q. i < k /\ q <<= FRONT p ==> solvable (subterm' X (M i) q r))’
       by PROVE_TAC []
 >> Q.PAT_X_ASSUM ‘!i. i < k ==> P /\ Q’ K_TAC
 (* In the original antecedents of this theorem, some M may be unsolvable,
    and that's the easy case.
  *)
 >> Know ‘!i. i < k ==> solvable (M i)’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!i q. i < k /\ q <<= FRONT p ==> solvable _’
       (MP_TAC o Q.SPECL [‘i’, ‘[]’]) >> simp [])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==> p IN ltree_paths (BT' X (M i) r)’
 >- (rpt STRIP_TAC \\
     irule (iffRL BT_ltree_paths_thm) >> rw [])
 >> DISCH_TAC
 (* define M0 *)
 >> qabbrev_tac ‘M0 = \i. principal_hnf (M i)’
 >> Know ‘!i. i < k ==> hnf (M0 i)’
 >- (rw [Abbr ‘M0’] \\
     MATCH_MP_TAC hnf_principal_hnf \\
     rw [GSYM solvable_iff_has_hnf] >> fs [EVERY_EL])
 >> DISCH_TAC
 >> qabbrev_tac ‘n = \i. LAMl_size (M0 i)’
 (* NOTE: This n_max was redefined from previous ‘MAX_SET (IMAGE n (count k))’ *)
 >> qabbrev_tac ‘n_max = MAX_LIST (MAP (\e. subterm_length e p) Ms)’
 >> Know ‘!i. i < k ==> subterm_length (M i) p <= n_max’
 >- (rw [Abbr ‘n_max’] \\
     MATCH_MP_TAC MAX_LIST_PROPERTY >> rw [MEM_MAP] \\
     Q.EXISTS_TAC ‘M i’ >> rw [EL_MEM, Abbr ‘M’])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==> n i <= n_max’
 >- (RW_TAC std_ss [] \\
     Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_length (M i) p’ \\
     MP_TAC (Q.SPECL [‘X’, ‘(M :num -> term) i’, ‘p’, ‘r’] subterm_length_first) \\
     simp [Abbr ‘n’])
 >> DISCH_TAC
 >> qabbrev_tac ‘d = MAX_LIST (MAP (\e. subterm_width e p) Ms)’
 >> Know ‘!i. i < k ==> subterm_width (M i) p <= d’
 >- (rw [Abbr ‘d’] \\
     MATCH_MP_TAC MAX_LIST_PROPERTY >> rw [MEM_MAP] \\
     Q.EXISTS_TAC ‘M i’ >> rw [EL_MEM, Abbr ‘M’])
 >> DISCH_TAC
 >> qabbrev_tac ‘d_max = d + n_max’
 (* ‘vs0’ excludes all free variables in Ms but is in ROW 0, then is divideded
    to vs and xs for constructing p1 and p3, resp.

    NOTE: The basic requirement of ‘vs’ is that it must be disjoint with ‘Y’
    and is at row 0. But if we exclude ‘X UNION Y’, then it also holds that
   ‘set vs SUBSET X UNION RANK r’ just like another part of ‘M’.
  *)
 >> Q_TAC (NEWS_TAC (“vs0 :string list”, “n_max + SUC d_max + k”)) ‘X UNION Y’
 >> Know ‘set vs0 SUBSET X UNION RANK (SUC r)’
 >- (Suff ‘set vs0 SUBSET RANK (SUC r)’ >- SET_TAC [] \\
     qunabbrev_tac ‘vs0’ \\
     MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp [])
 >> DISCH_TAC
 >> qabbrev_tac ‘vs = TAKE n_max vs0’
 >> qabbrev_tac ‘xs = DROP n_max vs0’
 >> ‘vs ++ xs = vs0’ by METIS_TAC [TAKE_DROP]
 >> Know ‘set vs SUBSET set vs0 /\ set xs SUBSET set vs0’
 >- (POP_ASSUM (REWRITE_TAC o wrap o SYM) \\
     simp [LIST_TO_SET_APPEND])
 >> STRIP_TAC
 >> Know ‘set vs SUBSET X UNION RANK (SUC r)’
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs0’ >> art [])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set vs) X /\ DISJOINT (set vs) Y /\
          DISJOINT (set xs) X /\ DISJOINT (set xs) Y’
 >- (rpt CONJ_TAC \\
     MATCH_MP_TAC DISJOINT_SUBSET' \\
     Q.EXISTS_TAC ‘set vs0’ >> art [])
 >> STRIP_TAC
 >> ‘LENGTH vs = n_max’         by rw [Abbr ‘vs’]
 >> ‘LENGTH xs = SUC d_max + k’ by rw [Abbr ‘xs’]
 >> Know ‘ALL_DISTINCT vs /\ ALL_DISTINCT xs /\ DISJOINT (set xs) (set vs)’
 >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs0’ MP_TAC \\
     Q.PAT_X_ASSUM ‘vs ++ xs = vs0’ (REWRITE_TAC o wrap o SYM) \\
     simp [ALL_DISTINCT_APPEND', Once DISJOINT_SYM])
 >> STRIP_TAC
 >> ‘NEWS n_max (X UNION Y) = vs’ by simp [Abbr ‘vs’, Abbr ‘vs0’, TAKE_RNEWS]
 >> Know ‘set vs SUBSET ROW 0’
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs0’ >> art [] \\
     rw [Abbr ‘vs0’, RNEWS_SUBSET_ROW])
 >> DISCH_TAC
 >> Know ‘set vs SUBSET RANK r’
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ >> art [] \\
     rw [ROW_SUBSET_RANK])
 >> DISCH_TAC
 (* construct p1 *)
 >> qabbrev_tac ‘p1 = MAP rightctxt (REVERSE (MAP VAR vs))’
 >> ‘Boehm_transform p1’ by rw [Abbr ‘p1’, MAP_MAP_o, GSYM MAP_REVERSE]
 (* decompose M0 by hnf_cases_shared *)
 >> Know ‘!i. i < k ==> ?y args. M0 i = LAMl (TAKE (n i) vs) (VAR y @* args)’
 >- (Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     fs [Abbr ‘n’] \\
     irule (iffLR hnf_cases_shared) >> simp [] \\
     MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘FV (EL i Ms)’ \\
     reverse CONJ_TAC
     >- (rw [Abbr ‘M0’] >> MATCH_MP_TAC principal_hnf_FV_SUBSET \\
         rw [GSYM solvable_iff_has_hnf]) \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs) Y’ MP_TAC \\
     rw [Abbr ‘Y’] \\
     POP_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘M i’ >> rw [Abbr ‘M’, EL_MEM])
 (* now assert two functions y and args for each term in Ms *)
 >> simp [EXT_SKOLEM_THM'] (* from topologyTheory *)
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘y’
                 (Q.X_CHOOSE_THEN ‘args’ STRIP_ASSUME_TAC))
 >> Q.PAT_X_ASSUM ‘!i. i < k ==> hnf (M0 i)’ K_TAC
 (* define M1 *)
 >> qabbrev_tac ‘M1 = \i. principal_hnf (M0 i @* MAP VAR vs)’
 >> Know ‘!i. i < k ==> M1 i = VAR (y i) @* args i @* DROP (n i) (MAP VAR vs)’
 >- (Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     simp [Abbr ‘M1’] \\
     qabbrev_tac ‘t = VAR (y i) @* args i’ \\
     simp [GSYM MAP_DROP] \\
     qabbrev_tac ‘vs' = TAKE (n i) vs’ \\
     Know ‘MAP VAR vs = MAP VAR vs' ++ MAP VAR (DROP (n i) vs)’
     >- (REWRITE_TAC [GSYM MAP_APPEND] >> AP_TERM_TAC \\
         rw [Abbr ‘vs'’, TAKE_DROP]) >> Rewr' \\
     REWRITE_TAC [appstar_APPEND] \\
     qabbrev_tac ‘l = MAP VAR (DROP (n i) vs)’ \\
     MATCH_MP_TAC principal_hnf_beta_reduce_ext \\
     rw [Abbr ‘t’, hnf_appstar])
 >> DISCH_TAC
 >> ‘!i. i < k ==> hnf_headvar (M1 i) = y i’
       by rw [hnf_head_hnf, GSYM appstar_APPEND]
 (* calculating ‘apply p1 (M0 i)’ *)
 >> Know ‘!i. i < k ==> apply p1 (M0 i) == M1 i’
 >- (rw [Abbr ‘p1’, Boehm_apply_MAP_rightctxt'] \\
     GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites
       [ISPECL [“(n :num -> num) i”, “MAP VAR vs”] (GSYM TAKE_DROP)] \\
     REWRITE_TAC [appstar_APPEND] \\
     MATCH_MP_TAC lameq_appstar_cong \\
     rw [GSYM MAP_TAKE])
 >> DISCH_TAC
 >> qabbrev_tac ‘m = \i. LENGTH (args i)’
 >> Know ‘!i. i < k ==> m i <= d’
 >- (RW_TAC std_ss [] \\
     Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width (M i) p’ \\
     MP_TAC (Q.SPECL [‘X’, ‘(M :num -> term) i’, ‘p’, ‘r’] subterm_width_first) \\
     simp [Abbr ‘m’])
 >> DISCH_TAC
 (* NOTE: Thus P(d) is not enough to cover M1, whose ‘hnf_children_size’ is
    bounded by ‘d + n_max’. *)
 >> qabbrev_tac ‘P = \i. permutator (d_max + i)’
 (* construct p2 *)
 >> qabbrev_tac ‘p2 = REVERSE (GENLIST (\i. [P i/y i]) k)’
 >> ‘Boehm_transform p2’ by rw [Boehm_transform_def, Abbr ‘p2’, EVERY_GENLIST]
 (* p2 can be rewritten to an ISUB

    NOTE: It's important to make ‘sub’ in increasing ‘P i’ for future uses.
  *)
 >> qabbrev_tac ‘sub = \k. GENLIST (\i. (P i,y i)) k’
 >> Know ‘!t. apply p2 t = t ISUB sub k’
 >- (simp [Abbr ‘p2’, Abbr ‘sub’] \\
     Q.SPEC_TAC (‘k’, ‘j’) \\
     Induct_on ‘j’ >- rw [] \\
     rw [GENLIST, REVERSE_SNOC, ISUB_SNOC])
 >> DISCH_TAC
 (* properties of ‘sub’ (iterated substitution) *)
 >> Know ‘!j. DOM (sub j) = IMAGE y (count j) /\ FVS (sub j) = {}’
 >- (simp [Abbr ‘sub’] \\
     Induct_on ‘j’ >- rw [DOM_DEF, FVS_DEF] \\
     rw [GENLIST, REVERSE_SNOC, DOM_DEF, FVS_DEF, COUNT_SUC, DOM_SNOC, FVS_SNOC]
     >- SET_TAC [] \\
     rw [Abbr ‘P’, FV_permutator])
 >> DISCH_TAC
 (* NOTE: There may be duplicated names among all ‘y i’. The function f maps
    i to the least j such that y j = y i, and P j is the ISUB result.
  *)
 >> Know ‘!i t. i <= k /\ t IN DOM (sub i) ==>
                VAR t ISUB (sub i) = P (LEAST j. y j = t)’
 >- (Induct_on ‘i’ >- rw [Abbr ‘sub’] \\
     rw [] \\
     Know ‘!i j. P i ISUB sub j = P i’
     >- (rw [Abbr ‘sub’] \\
         MATCH_MP_TAC ISUB_unchanged >> simp [Abbr ‘P’]) >> DISCH_TAC \\
    ‘sub (SUC i) = GENLIST (\i. (P i,y i)) (SUC i)’ by rw [] >> POP_ORW \\
     REWRITE_TAC [GENLIST] \\
     simp [DOM_SNOC, ISUB_SNOC, IN_UNION] \\
     Cases_on ‘y x IN DOM (sub i)’
     >- (Q.PAT_X_ASSUM ‘!t. i <= k /\ t IN DOM (sub i) ==> _’
            (MP_TAC o Q.SPEC ‘y (x :num)’) >> rw [] \\
         MATCH_MP_TAC lemma14b >> simp [Abbr ‘P’, FV_permutator]) \\
     Know ‘VAR (y x) ISUB sub i = VAR (y x)’
     >- (MATCH_MP_TAC ISUB_unchanged \\
         Q.PAT_X_ASSUM ‘!j. DOM (sub j) = _ /\ _’ K_TAC \\
         simp [DISJOINT_ALT]) >> Rewr' \\
     POP_ASSUM MP_TAC \\
     simp [] >> DISCH_TAC \\
     Know ‘x = i’
     >- (POP_ASSUM (MP_TAC o Q.SPEC ‘x’) >> rw []) \\
     DISCH_THEN (fs o wrap) >> T_TAC \\
     LEAST_ELIM_TAC \\
     CONJ_TAC >- (Q.EXISTS_TAC ‘i’ >> rw []) \\
     Q.X_GEN_TAC ‘j’ >> rw [Abbr ‘P’] \\
     CCONTR_TAC \\
    ‘i < j \/ j < i’ by rw [] \\ (* 2 subgoals, same tactics *)
     METIS_TAC [])
 >> DISCH_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o SIMP_RULE arith_ss [] o Q.SPEC ‘k’)
 >> Q.PAT_X_ASSUM ‘!j. DOM (sub j) = IMAGE y (count j) /\ _’
      (STRIP_ASSUME_TAC o Q.SPEC ‘k’)
 >> qabbrev_tac ‘ss = sub k’
 (* NOTE: f is the important injection from index to index *)
 >> qabbrev_tac ‘f = \i. LEAST j. y j = y i’
 >> Know ‘!i. i < k ==> f i < k /\ VAR (y i) ISUB ss = P (f i)’
 >- (rw [Abbr ‘f’] \\
     LEAST_ELIM_TAC \\
     CONJ_TAC >- (Q.EXISTS_TAC ‘i’ >> rw []) \\
     Q.X_GEN_TAC ‘j’ >> rw [] \\
     SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [NOT_LESS]) \\
    ‘i < j’ by rw [] >> METIS_TAC [])
 >> DISCH_TAC
 >> Know ‘!j1 j2. y j1 <> y j2 ==> f j1 <> f j2’
 >- (rpt GEN_TAC >> DISCH_TAC \\
     simp [Abbr ‘f’] \\
     LEAST_ELIM_TAC \\
     CONJ_TAC >- (Q.EXISTS_TAC ‘j1’ >> rw []) \\
     Q.X_GEN_TAC ‘j3’ >> STRIP_TAC \\
     LEAST_ELIM_TAC \\
     CONJ_TAC >- (Q.EXISTS_TAC ‘j2’ >> rw []) \\
     Q.X_GEN_TAC ‘j4’ >> STRIP_TAC \\
     CCONTR_TAC >> METIS_TAC [])
 >> DISCH_TAC
 (* more properties of ISUB ‘ss’ *)
 >> ‘!N. MEM N (MAP FST ss) ==> ?j. j < k /\ N = P j’
       by (rw [Abbr ‘ss’, Abbr ‘sub’, MAP_REVERSE, MAP_GENLIST, MEM_GENLIST])
 (* Now we have a list of M1's whose hnf_children_size is bounded by ‘d_max’.
    In the worst case, ‘P @* M1 i’ will leave ‘SUC d_max’ variable bindings
    at most (in this case, ‘args i = 0 /\ n i = n_max’), and to finally get a
   "is_ready" term, we should apply a fresh list of d_max+1 variables (l).

    After redefining P by (\i. permutator (d_max + i), in the new worst
    case ‘P (f i) @* M1 i’ will leave at most ‘SUC d_max + k’ ending variables.

    NOTE: This list ‘xs’ is now part of vs0, defined as ‘DROP n_max vs0’.

    p3 is the maximal possible fresh list to be applied after the permutator
 *)
 >> qabbrev_tac ‘p3 = MAP rightctxt (REVERSE (MAP VAR xs))’
 >> ‘Boehm_transform p3’ by rw [Abbr ‘p3’, MAP_MAP_o, GSYM MAP_REVERSE]
 (* additional steps for explicit construction *)
 >> Q.PAT_X_ASSUM ‘Boehm_transform pi'’ MP_TAC
 >> Know ‘pi' = p3 ++ p2 ++ p1’
 >- (rw [Abbr ‘pi'’, Boehm_construction_def] \\
     simp [Abbr ‘p2’, LIST_EQ_REWRITE])
 >> Rewr'
 (* “Boehm_construction” is now eliminated, back to old steps *)
 >> qunabbrev_tac ‘pi'’
 >> qabbrev_tac ‘pi = p3 ++ p2 ++ p1’
 >> DISCH_TAC (* Boehm_transform pi *)
 (* NOTE: requirements for ‘Z’

    1. y i IN Z /\ BIGUNION (IMAGE FV (set (args i))) SUBSET Z
    2. DISJOINT (set xs) Z
    3. Z SUBSET X UNION RANK (SUC r)
  *)
 >> qabbrev_tac ‘Z = Y UNION set vs’
 >> ‘FINITE Z’ by rw [Abbr ‘Z’]
 >> ‘DISJOINT (set xs) Z’ by rw [Abbr ‘Z’, DISJOINT_UNION']
 (* FV properties of the head variable y (and children args) *)
 >> Know ‘!i. i < k ==> y i IN Z /\
                        BIGUNION (IMAGE FV (set (args i))) SUBSET Z’
 >- (NTAC 2 STRIP_TAC \\
     qabbrev_tac ‘Z' = FV (M i) UNION set vs’ \\
     Suff ‘y i IN Z' /\ BIGUNION (IMAGE FV (set (args i))) SUBSET Z'’
     >- (Suff ‘Z' SUBSET Z’ >- PROVE_TAC [SUBSET_DEF] \\
         Q.PAT_X_ASSUM ‘Y SUBSET X UNION RANK r’ MP_TAC \\
         simp [Abbr ‘Z'’, Abbr ‘Z’, Abbr ‘Y’] \\
         rw [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNION] \\
         DISJ1_TAC \\
         Q.EXISTS_TAC ‘M i’ >> art [] \\
         rw [Abbr ‘M’, EL_MEM]) \\
  (* applying principal_hnf_FV_SUBSET' *)
     Know ‘FV (M0 i) SUBSET FV (M i)’
     >- (SIMP_TAC std_ss [Abbr ‘M0’, o_DEF] \\
         MATCH_MP_TAC principal_hnf_FV_SUBSET' >> rw []) \\
     qunabbrev_tac ‘Z'’ \\
     Suff ‘y i IN FV (M0 i) UNION set vs /\
           BIGUNION (IMAGE FV (set (args i))) SUBSET
           FV (M0 i) UNION set vs’
     >- SET_TAC [] \\
     Know ‘FV (M1 i) SUBSET FV (M0 i @* MAP VAR vs)’
     >- (‘M1 i = principal_hnf (M0 i @* MAP VAR vs)’ by rw [] >> POP_ORW \\
         MATCH_MP_TAC principal_hnf_FV_SUBSET' \\
        ‘M0 i @* MAP VAR vs = apply p1 (M0 i)’
            by rw [Abbr ‘p1’, Boehm_apply_MAP_rightctxt'] >> POP_ORW \\
         Suff ‘solvable (M1 i)’ >- METIS_TAC [lameq_solvable_cong] \\
         MATCH_MP_TAC hnf_solvable \\
         rw [GSYM appstar_APPEND, hnf_appstar]) \\
     REWRITE_TAC [FV_appstar_MAP_VAR] \\
     Know ‘y i IN FV (M1 i) /\
           BIGUNION (IMAGE FV (set (args i))) SUBSET FV (M1 i)’
     >- (rw [FV_appstar] >> SET_TAC []) \\
     rpt STRIP_TAC >- METIS_TAC [SUBSET_DEF] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘FV (M1 i)’ >> art [])
 >> DISCH_TAC
 >> Know ‘Z SUBSET X UNION RANK r’
 >- (simp [Abbr ‘Z’, UNION_SUBSET] \\
     Suff ‘set vs SUBSET RANK r’ >- SET_TAC [] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ \\
     rw [ROW_SUBSET_RANK])
 >> DISCH_TAC
 (* A better upper bound on ‘y i’ using subterm_headvar_lemma_alt *)
 >> Know ‘!i. i < k ==> y i IN Y UNION set (TAKE (n i) vs)’
 >- (rpt STRIP_TAC \\
     Know ‘FV (M i) SUBSET Y’
     >- (rw [SUBSET_DEF, Abbr ‘Y’] \\
         Q.EXISTS_TAC ‘FV (M i)’ >> art [] \\
         Q.EXISTS_TAC ‘M i’ >> simp [Abbr ‘M’, EL_MEM]) >> DISCH_TAC \\
     Suff ‘y i IN FV (M i) UNION set (TAKE (n i) vs)’
     >- (POP_ASSUM MP_TAC >> SET_TAC []) \\
    ‘y i = hnf_headvar (M1 i)’ by simp [GSYM appstar_APPEND] \\
     POP_ORW \\
     MATCH_MP_TAC subterm_headvar_lemma_alt \\
     qexistsl_tac [‘X UNION Y’, ‘0’, ‘M0 (i :num)’, ‘n_max’] >> simp [] \\
     POP_ASSUM MP_TAC >> SET_TAC [])
 >> DISCH_TAC
 >> Know ‘!i h. i < k /\ h < m i ==> FV (EL h (args i)) SUBSET X UNION RANK r’
 >- (rpt STRIP_TAC \\
     qabbrev_tac ‘N = EL h (args i)’ \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> y i IN Z /\ _’ drule \\
     simp [BIGUNION_SUBSET] >> STRIP_TAC \\
     Know ‘FV N SUBSET Z’
     >- (POP_ASSUM MATCH_MP_TAC \\
         Q.EXISTS_TAC ‘N’ >> simp [Abbr ‘N’, EL_MEM]) \\
     qunabbrev_tac ‘Z’ >> DISCH_TAC \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘Y UNION set vs’ \\
     POP_ASSUM (REWRITE_TAC o wrap) \\
     simp [UNION_SUBSET])
 >> DISCH_TAC
 (* a better upper bound of BIGUNION (IMAGE FV (set (args i))) *)
 >> Know ‘!i. i < k ==> BIGUNION (IMAGE FV (set (args i))) SUBSET
                        FV (M i) UNION set (TAKE (n i) vs)’
 >- (rpt STRIP_TAC \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV (M0 i) UNION set (TAKE (n i) vs)’ \\
     reverse CONJ_TAC
     >- (Suff ‘FV (M0 i) SUBSET FV (M i)’ >- SET_TAC [] \\
         SIMP_TAC std_ss [Abbr ‘M0’] \\
         MATCH_MP_TAC principal_hnf_FV_SUBSET' >> simp []) \\
     qabbrev_tac ‘vs' = TAKE (n i) vs’ \\
    ‘M0 i @* MAP VAR vs' == VAR (y i) @* args i’
       by simp [lameq_LAMl_appstar_VAR] \\
  (* applying principal_hnf_beta_reduce *)
     Know ‘principal_hnf (M0 i @* MAP VAR vs') = VAR (y i) @* args i’
     >- (simp [] \\
         MATCH_MP_TAC principal_hnf_beta_reduce \\
         simp [hnf_appstar]) >> DISCH_TAC \\
     MP_TAC (Q.SPEC ‘M0 (i :num) @* MAP VAR vs'’ principal_hnf_FV_SUBSET') \\
     impl_tac >- (Suff ‘solvable (VAR (y i) @* args i)’
                  >- METIS_TAC [lameq_solvable_cong] \\
                  MATCH_MP_TAC hnf_solvable >> simp [hnf_appstar]) \\
     POP_ORW \\
     REWRITE_TAC [FV_appstar_MAP_VAR, FV_appstar, FV_thm] \\
     SET_TAC [])
 >> DISCH_TAC
 (* NOTE: now, before proving ‘EVERY is_ready' ...’, (for future subgoals) we
    need to calculute the principal_hnf of ‘apply pi (EL i Ms)’ for any i < k.

   ‘args'’ is the possibly substituted version of ‘args’.
  *)
 >> qabbrev_tac ‘args' = \i. MAP (\t. t ISUB ss) (args i)’
 >> ‘!i. LENGTH (args' i) = m i’ by rw [Abbr ‘args'’, Abbr ‘m’]
 (* NOTE: In vs, some elements are replaced by P, thus ‘set vs SUBSET set vs’ *)
 >> qabbrev_tac ‘args1 = MAP (\t. t ISUB ss) (MAP VAR vs)’
 >> ‘LENGTH args1 = n_max’ by rw [Abbr ‘args1’]
 >> Know ‘BIGUNION (IMAGE FV (set args1)) SUBSET set vs’
 >- (simp [Abbr ‘args1’, LIST_TO_SET_MAP, IMAGE_IMAGE] \\
     rw [SUBSET_DEF, IN_BIGUNION_IMAGE] \\
     POP_ASSUM MP_TAC \\
     rename1 ‘MEM v vs’ \\
     Cases_on ‘v IN DOM ss’ >- simp [Abbr ‘P’, FV_permutator] \\
     Know ‘VAR v ISUB ss = VAR v’
     >- (MATCH_MP_TAC ISUB_VAR_FRESH' >> art []) >> Rewr' \\
     simp [])
 >> DISCH_TAC
 (* abbreviate the tail term list after applying p2 *)
 >> qabbrev_tac ‘args2 = \i. DROP (n i) args1’
 >> Know ‘!i. BIGUNION (IMAGE FV (set (args2 i))) SUBSET set vs’
 >- (Q.X_GEN_TAC ‘i’ \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘BIGUNION (IMAGE FV (set args1))’ >> art [] \\
     Suff ‘set (args2 i) SUBSET set args1’ >- SET_TAC [] \\
     rw [Abbr ‘args2’, LIST_TO_SET_DROP])
 >> DISCH_TAC
 (* calculating ‘apply p2 (M1 i)’ *)
 >> ‘!i. i < k ==> apply p2 (M1 i) = P (f i) @* args' i @* args2 i’
       by rw [Abbr ‘args'’, Abbr ‘args1’, Abbr ‘args2’,
              GSYM appstar_APPEND, MAP_APPEND, appstar_ISUB, MAP_DROP]
 (* calculating ‘apply p2 ...’ until reaching a hnf *)
 >> Know ‘!i. i < k ==> apply p3 (P (f i) @* args' i @* args2 i) =
                        P (f i) @* args' i @* args2 i @* MAP VAR xs’
 >- rw [Abbr ‘p3’, Boehm_apply_MAP_rightctxt']
 (* preparing for permutator_hreduce_more (no DISCH_TAC for above Know) *)
 >> qabbrev_tac ‘l = \i. args' i ++ args2 i ++ MAP VAR xs’
 >> ASM_SIMP_TAC bool_ss [GSYM appstar_APPEND, APPEND_ASSOC]
 (* now l appears in the goal *)
 >> REWRITE_TAC [appstar_APPEND]
 (* stage work *)
 >> ‘!i. LENGTH (l i) = m i + (n_max - n i) + SUC d_max + k’
       by rw [Abbr ‘l’, Abbr ‘m’, Abbr ‘args2’, Abbr ‘d_max’, MAP_DROP]
 >> ‘!i. d_max + k < LENGTH (l i)’ by rw []
 >> DISCH_TAC
 (* applying TAKE_DROP_SUC to break l into 3 pieces

    NOTE: New the segmentation of ‘l’ also depends on ‘i’.
  *)
 >> qabbrev_tac ‘d_max' = \i. d_max + f i’
 >> Know ‘!i. i < k ==> d_max' i < d_max + k’
 >- (rw [Abbr ‘d_max'’] \\
     Q_TAC (TRANS_TAC LESS_TRANS) ‘d_max + k’ >> simp [])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==> d_max' i <= LENGTH (l i)’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!i. LENGTH (l i) = _’ K_TAC \\
     simp [Abbr ‘d_max'’] \\
     MATCH_MP_TAC LT_IMP_LE \\
     Q_TAC (TRANS_TAC LESS_TRANS) ‘d_max + k’ >> simp [])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==>
              apply p3 (P (f i) @* args' i @* args2 i) =
              P (f i) @* (TAKE (d_max' i) (l i) ++ [EL (d_max' i) (l i)] ++
                          DROP (SUC (d_max' i)) (l i))’
 >- (RW_TAC std_ss [] \\
     Suff ‘TAKE (d_max' i) (l i) ++ [EL (d_max' i) (l i)] ++
           DROP (SUC (d_max' i)) (l i) = l i’ >- Rewr \\
     MATCH_MP_TAC TAKE_DROP_SUC \\
     Q.PAT_X_ASSUM ‘!i. LENGTH (l i) = _ + k’ K_TAC \\
     Q_TAC (TRANS_TAC LESS_TRANS) ‘d_max + k’ >> simp [])
 >> Q.PAT_X_ASSUM ‘!i. i < k ==> _ = P (f i) @* l i’ K_TAC
 >> REWRITE_TAC [appstar_APPEND, appstar_SING]
 (* NOTE: The segmentation of list l(i) - apply (p3 ++ p2 ++ p1) (M i)

  |<-- m(i)<= d -->|<-- n_max-n(i) -->|<-------------- SUC d_max + k--------->|
  |----- args' ----+----- args2 ------+-------------- MAP VAR xs -------------|
  |------------------------------------ l ------------------------------------|
  |                                   |<-j->|
  |<--- d_max + f = d + n_max + f(i) ---->|b|
  |------------------- Ns(i) -------------+-+<-------------- tl(i) ---------->|
  |<-------------- d_max + k + 1 ---------->|
  *)
 >> qabbrev_tac ‘Ns = \i. TAKE (d_max' i) (l i)’
 >> qabbrev_tac ‘B  = \i. EL (d_max' i) (l i)’
 >> qabbrev_tac ‘tl = \i. DROP (SUC (d_max' i)) (l i)’
 >> simp [] (* this put Ns, B and tl in use *)
 (* What is j here? The purpose of j is to show that (B i) is a fresh name in
    xs. This j is the offset (d_max' i) of l, translated to offset of xs. *)
 >> qabbrev_tac ‘j = \i. d_max' i - LENGTH (args' i ++ args2 i)’
 (* show that (j i) is valid index of xs *)
 >> Know ‘!i. i < k ==> LENGTH (args' i ++ args2 i) <= d_max' i’
 >- (rpt STRIP_TAC \\
     simp [Abbr ‘j’, Abbr ‘args'’, Abbr ‘args2’, Abbr ‘d_max'’, Abbr ‘d_max’] \\
     MATCH_MP_TAC LESS_EQ_LESS_EQ_MONO >> simp [])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==> j i < LENGTH xs’
 >- (rw [Abbr ‘j’, Abbr ‘args'’, Abbr ‘args2’, Abbr ‘d_max'’, Abbr ‘d_max’] \\
    ‘f i < k’ by rw [] \\
     simp [ADD1])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==> ?b. EL (j i) xs = b /\ B i = VAR b’
 >- (rw [Abbr ‘B’, Abbr ‘l’] \\
     Suff ‘EL (d_max' i) (args' i ++ args2 i ++ MAP VAR xs) = EL (j i) (MAP VAR xs)’
     >- rw [EL_MAP] \\
     SIMP_TAC bool_ss [Abbr ‘j’] \\
     MATCH_MP_TAC EL_APPEND2 \\
    ‘f i < k’ by rw [] \\
     rw [Abbr ‘args'’, Abbr ‘args2’, Abbr ‘d_max'’, Abbr ‘d_max’, MAP_DROP] \\
     MATCH_MP_TAC LESS_EQ_LESS_EQ_MONO >> rw [])
 >> simp [EXT_SKOLEM_THM']
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘b’ STRIP_ASSUME_TAC) (* this asserts ‘b’ *)
 >> simp []
 >> DISCH_TAC (* store ‘!i. i < k ==> apply p3 ...’ *)
 (* applying permutator_hreduce_more, it clearly reduces to a hnf *)
 >> Know ‘!i. i < k ==>
              P (f i) @* Ns i @@ VAR (b i) @* tl i -h->* VAR (b i) @* Ns i @* tl i’
 >- (RW_TAC std_ss [Abbr ‘P’] \\
     MATCH_MP_TAC permutator_hreduce_more >> rw [Abbr ‘Ns’, Abbr ‘d_max'’] \\
    ‘f i < k’ by rw [] \\
    ‘d_max + f i <= LENGTH (l i)’ by rw [] \\
     simp [LENGTH_TAKE])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==> apply pi (M i) == VAR (b i) @* Ns i @* tl i’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘apply pi (M0 i)’ \\
     CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> art [] \\
                  SIMP_TAC std_ss [Abbr ‘M0’] \\
                  MATCH_MP_TAC lameq_SYM \\
                  MATCH_MP_TAC lameq_principal_hnf' >> rw []) \\
     Q.PAT_X_ASSUM ‘Boehm_transform pi’ K_TAC \\
     qunabbrev_tac ‘pi’ \\
     ONCE_REWRITE_TAC [Boehm_apply_APPEND] \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘apply (p3 ++ p2) (M1 i)’ \\
     CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> rw [] \\
                  MATCH_MP_TAC Boehm_transform_APPEND >> art []) \\
     ASM_SIMP_TAC std_ss [Boehm_apply_APPEND] \\
     MATCH_MP_TAC hreduces_lameq >> rw [])
 >> DISCH_TAC
 (* calculating ‘principal_hnf (apply pi (M i))’ (hard) *)
 >> Know ‘!i. i < k ==>
              principal_hnf (apply pi (M i)) = VAR (b i) @* Ns i @* tl i’
 >- (rpt STRIP_TAC \\
     Know ‘MAP (\t. t ISUB ss) (MAP VAR xs) = MAP VAR xs’
     >- (rw [LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC ISUB_VAR_FRESH' >> rw [GSYM DOM_ALT_MAP_SND] \\
         simp [IN_IMAGE, IN_COUNT, Once DISJ_SYM] \\
         STRONG_DISJ_TAC (* push ‘a < k’ *) \\
         rename1 ‘EL x xs <> y a’ \\
         CCONTR_TAC \\
        ‘y a IN Z’ by rw [] \\
         Q.PAT_X_ASSUM ‘DISJOINT (set xs) Z’ MP_TAC \\
         rw [DISJOINT_ALT] \\
         Q.EXISTS_TAC ‘EL x xs’ >> rw [EL_MEM]) >> DISCH_TAC \\
  (* NOTE: This MP_TAC is for applying principal_hnf_denude_thm later. From
     now on, both ‘apply pi M == ...’ and ‘principal_hnf (apply pi M) = ...’
     are simplified in parallel.
   *)
     Q.PAT_X_ASSUM ‘!i. i < k ==> apply pi (M i) == _’ drule \\
     Q.PAT_X_ASSUM ‘Boehm_transform pi’ K_TAC \\
     Q.PAT_X_ASSUM ‘Boehm_transform p3’ K_TAC \\
  (* NOTE: No need to unabbrev ‘p2’ here since ‘apply p2 t = t ISUB sub k’ *)
     ASM_SIMP_TAC std_ss [Abbr ‘pi’, Boehm_apply_APPEND, Abbr ‘p1’, Abbr ‘p3’] \\
     FULL_SIMP_TAC bool_ss [Boehm_apply_MAP_rightctxt'] \\
  (* stage work *)
    ‘(M i @* MAP VAR vs ISUB ss) @* MAP VAR xs =
     (M i @* MAP VAR vs @* MAP VAR xs) ISUB ss’ by rw [appstar_ISUB] >> POP_ORW \\
     DISCH_TAC (* store ‘M i @* MAP VAR vs @* MAP VAR xs ISUB sub k == ...’ *) \\
  (* rewriting RHS to principal_hnf of ISUB *)
     Know ‘VAR (b i) @* Ns i @* tl i =
           principal_hnf (P (f i) @* args' i @* args2 i @* MAP VAR xs)’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
        ‘hnf (VAR (b i) @* Ns i @* tl i)’
            by rw [GSYM appstar_APPEND, hnf_appstar] \\
         Suff ‘solvable (P (f i) @* args' i @* args2 i @* MAP VAR xs)’
         >- (METIS_TAC [principal_hnf_thm']) \\
         Suff ‘solvable (VAR (b i) @* Ns i @* tl i) /\
               P (f i) @* Ns i @@ VAR (b i) @* tl i == VAR (b i) @* Ns i @* tl i’
         >- (METIS_TAC [lameq_solvable_cong]) \\
         reverse CONJ_TAC >- (MATCH_MP_TAC hreduces_lameq >> rw []) \\
         MATCH_MP_TAC hnf_solvable >> art []) >> Rewr' \\
     Know ‘P (f i) @* args' i @* args2 i @* MAP VAR xs = M1 i @* MAP VAR xs ISUB ss’
     >- (REWRITE_TAC [appstar_ISUB, Once EQ_SYM_EQ] \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> apply p2 (M1 i) = _’
           (drule o GSYM) >> Rewr' \\
         Q.PAT_X_ASSUM ‘!t. apply p2 t = t ISUB ss’ (ONCE_REWRITE_TAC o wrap) \\
         AP_TERM_TAC >> art []) >> Rewr' \\
  (* applying principal_hnf_ISUB_cong *)
     MATCH_MP_TAC principal_hnf_ISUB_cong \\
     CONJ_TAC (* has_hnf #1 *)
     >- (simp [GSYM solvable_iff_has_hnf, GSYM appstar_APPEND] \\
         Know ‘M0 i == M i’
         >- (SIMP_TAC std_ss [Abbr ‘M0’] \\
             MATCH_MP_TAC lameq_principal_hnf' >> rw []) >> DISCH_TAC \\
        ‘M0 i @* (MAP VAR vs ++ MAP VAR xs) ==
          M i @* (MAP VAR vs ++ MAP VAR xs)’ by rw [lameq_appstar_cong] \\
         Suff ‘solvable (M0 i @* (MAP VAR vs ++ MAP VAR xs))’
         >- PROVE_TAC [lameq_solvable_cong] \\
         NTAC 2 (POP_ASSUM K_TAC) \\
         REWRITE_TAC [appstar_APPEND] \\
         qabbrev_tac ‘M0' = M0 i @* MAP VAR vs’ \\
        ‘M0' == M1 i’ by rw [Abbr ‘M0'’] \\
        ‘M0' @* MAP VAR xs == M1 i @* MAP VAR xs’ by rw [lameq_appstar_cong] \\
         Suff ‘solvable (M1 i @* MAP VAR xs)’ >- PROVE_TAC [lameq_solvable_cong] \\
         MATCH_MP_TAC hnf_solvable >> rw [hnf_appstar]) \\
     CONJ_TAC (* has_hnf #2 *)
     >- (REWRITE_TAC [GSYM solvable_iff_has_hnf] \\
         Suff ‘solvable (VAR (b i) @* Ns i @* tl i)’
         >- PROVE_TAC [lameq_solvable_cong] \\
         MATCH_MP_TAC hnf_solvable >> rw [hnf_appstar]) \\
     CONJ_TAC (* has_hnf # 3 *)
     >- (simp [appstar_ISUB, MAP_DROP] \\
         ASM_SIMP_TAC bool_ss [has_hnf_thm] \\
         Q.EXISTS_TAC ‘VAR (b i) @* Ns i @* tl i’ >> rw [] \\
         rw [hnf_appstar, GSYM appstar_APPEND]) \\
     ASM_SIMP_TAC std_ss [] (* rewrite M1 i *) \\
    ‘MAP VAR vs = TAKE (n i) (MAP VAR vs) ++ DROP (n i) (MAP VAR vs)’
       by rw [TAKE_DROP] \\
     POP_ASSUM
       (GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites o wrap) \\
     REWRITE_TAC [appstar_APPEND] \\
     qabbrev_tac ‘A = M i @* TAKE (n i) (MAP VAR vs)’ \\
     qabbrev_tac ‘A' = VAR (y i) @* args i’ \\
     REWRITE_TAC [GSYM appstar_APPEND] \\
     qabbrev_tac ‘C = DROP (n i) (MAP VAR vs) ++ MAP VAR xs’ \\
     qunabbrevl_tac [‘A’, ‘A'’] \\
     REWRITE_TAC [GSYM MAP_TAKE] \\
  (* applying principal_hnf_denude_thm, finally *)
     MATCH_MP_TAC principal_hnf_denude_thm >> simp [] \\
     CONJ_TAC (* ALL_DISTINCT *)
     >- (MATCH_MP_TAC ALL_DISTINCT_TAKE >> art []) \\
     MATCH_MP_TAC DISJOINT_SUBSET' \\
     Q.EXISTS_TAC ‘set vs’ \\
     reverse CONJ_TAC
     >- (rw [SUBSET_DEF] \\
         MATCH_MP_TAC MEM_TAKE >> Q.EXISTS_TAC ‘n i’ >> art []) \\
     MATCH_MP_TAC DISJOINT_SUBSET >> Q.EXISTS_TAC ‘Y’ >> art [] \\
     rw [SUBSET_DEF, Abbr ‘Y’] \\
     Q.EXISTS_TAC ‘FV (M i)’ >> art [] \\
     Q.EXISTS_TAC ‘M i’ >> art [] \\
     rw [Abbr ‘M’, EL_MEM])
 >> DISCH_TAC
 (* stage work *)
 >> Know ‘!i. i < k ==> solvable (apply pi (M i))’
 >- (rpt STRIP_TAC \\
     Suff ‘solvable (VAR (b i) @* Ns i @* tl i)’
     >- METIS_TAC [lameq_solvable_cong] \\
     MATCH_MP_TAC hnf_solvable >> rw [hnf_appstar, GSYM appstar_APPEND])
 >> DISCH_TAC
 >> PRINT_TAC "stage work on subtree_equiv_lemma"
 >> CONJ_TAC (* EVERY is_ready ... *)
 >- (rpt (Q.PAT_X_ASSUM ‘Boehm_transform _’ K_TAC) \\
     simp [EVERY_EL, EL_MAP] \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
  (* now expanding ‘is_ready’ using [is_ready_alt] *)
     ASM_SIMP_TAC std_ss [is_ready_alt'] \\
     qexistsl_tac [‘b i’, ‘Ns i ++ tl i’] \\
  (* subgoal: apply pi (M i) -h->* VAR (b i) @* (Ns i ++ tl i) *)
     CONJ_TAC
     >- (REWRITE_TAC [appstar_APPEND] \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> principal_hnf (apply pi (M i)) = _’ drule \\
         rw [principal_hnf_thm']) \\
  (* final goal (is_ready): EVERY (\e. b # e) ... *)
     Q.PAT_X_ASSUM ‘!i. i < k ==> principal_hnf (apply pi (M i)) = _’ K_TAC \\
     ASM_SIMP_TAC list_ss [EVERY_EL] \\
  (* easier goal first *)
     reverse CONJ_TAC (* b i # EL n (tl i) *)
     >- (Q.X_GEN_TAC ‘a’ >> DISCH_TAC \\
         qabbrev_tac ‘l1 = args' i ++ args2 i’ \\
         Know ‘LENGTH l1 <= d_max' i’
         >- (rw [Abbr ‘l1’, Abbr ‘args2’, Abbr ‘d_max’, Abbr ‘d_max'’, MAP_DROP] \\
             MATCH_MP_TAC LESS_EQ_LESS_EQ_MONO >> rw [] \\
             Q.PAT_X_ASSUM ‘!i. i < k ==> m i <= d’ MP_TAC \\
             simp [Abbr ‘m’]) >> DISCH_TAC \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> apply pi (M i) == _’ K_TAC \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> apply p3 _ = _’      K_TAC \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> apply p2 _ = _’      K_TAC \\
         Q.PAT_X_ASSUM ‘a < LENGTH (tl i)’ MP_TAC \\
      (* applying DROP_APPEND2 *)
         Know ‘tl i = DROP (SUC (j i)) (MAP VAR xs)’
         >- (rw [Abbr ‘tl’, Abbr ‘l’] \\
            ‘LENGTH l1 <= SUC (d_max' i)’ by rw [] \\
             ASM_SIMP_TAC std_ss [DROP_APPEND2] \\
             Suff ‘SUC (d_max' i) - LENGTH l1 = SUC (j i)’ >- rw [] \\
             ASM_SIMP_TAC arith_ss [Abbr ‘j’]) >> Rewr' \\
         simp [] >> DISCH_TAC (* a < d_max + ... *) \\
         Know ‘EL a (DROP (SUC (j i)) (MAP VAR xs :term list)) =
               EL (a + SUC (j i)) (MAP VAR xs)’
         >- (MATCH_MP_TAC EL_DROP >> rw []) >> Rewr' \\
         simp [EL_MAP] \\
        ‘b i = EL (j i) xs’ by rw [] >> POP_ORW \\
         SPOSE_NOT_THEN (STRIP_ASSUME_TAC o REWRITE_RULE []) \\
         Suff ‘EL (j i) xs = EL (a + SUC (j i)) xs <=> j i = a + SUC (j i)’
         >- rw [] \\
         MATCH_MP_TAC ALL_DISTINCT_EL_IMP >> rw []) \\
  (* final goal, only slightly harder *)
     Q.X_GEN_TAC ‘a’ >> DISCH_TAC \\
  (* cleanup useless assumptions and abbreviations *)
     Q.PAT_X_ASSUM ‘!i. i < k ==> apply pi (M i) == _’ K_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> apply p3 _ = _’      K_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> apply p2 _ = _’      K_TAC \\
     Q.PAT_X_ASSUM ‘!t. apply p2 t = t ISUB ss’        K_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> apply p1 _ == _’     K_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> solvable (apply pi (M i))’ K_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> P (f i) @* Ns i @@ _ @* tl i -h->* _’ K_TAC \\
     qunabbrevl_tac [‘pi’, ‘p1’, ‘p2’, ‘p3’] \\
  (* The segmentation of list l(i) - apply (p3 ++ p2 ++ p1) (M i)

   |<-- m(i)<= d -->|<-- n_max-n(i) -->|<------------- SUC d_max + k --------->|
   |----- args' ----+----- args2 ------+-------------- MAP VAR xs -------------|
   |------------------------------------ l ------------------------------------|
   |                                   |<-j->|
   |<--- d_max + f = d + n_max + f(i) ---->|b|
   |------------------- Ns(i) -------------+-+<-------------- tl(i) ---------->|
   |<-------------- d_max + k + 1 ---------->|

     Three cases for proving ‘b i # EL a (Ns i)’, given a < LENGTH (Ns i):
     1) a < m i (= LENGTH (args' i))
     2) m i <= a < m i + LENGTH (args2 i)
     3) m i + LENGTH (args2 i) <= a
   *)
     Cases_on ‘a < m i’
     >- (Q.PAT_X_ASSUM ‘a < LENGTH (Ns i)’ MP_TAC \\
         simp [Abbr ‘Ns’, LENGTH_TAKE] \\
         DISCH_TAC (* a < d_max' i *) \\
         simp [EL_TAKE] \\
         Know ‘EL a (l i) = EL a (args' i)’
         >- (SIMP_TAC std_ss [Abbr ‘l’, GSYM APPEND_ASSOC] \\
             MATCH_MP_TAC EL_APPEND1 >> art []) >> Rewr' \\
         Suff ‘b i # EL a (args i)’
         >- (Suff ‘FV (EL a (args' i)) SUBSET FV (EL a (args i))’ >- SET_TAC [] \\
             Q.PAT_X_ASSUM ‘a < m i’ MP_TAC \\
             simp [Abbr ‘args'’, EL_MAP] >> DISCH_TAC \\
             MATCH_MP_TAC FV_ISUB_SUBSET >> art []) \\
         Know ‘b i NOTIN Z’
         >- (Q.PAT_X_ASSUM ‘DISJOINT (set xs) Z’ MP_TAC \\
             rw [DISJOINT_ALT] \\
             POP_ASSUM MATCH_MP_TAC \\
            ‘b i = EL (j i) xs’ by rw [] >> POP_ORW \\
             rw [EL_MEM]) \\
         Suff ‘FV (EL a (args i)) SUBSET Z’ >- SET_TAC [] \\
         Know ‘BIGUNION (IMAGE FV (set (args i))) SUBSET Z’ >- rw [] \\
         REWRITE_TAC [BIGUNION_SUBSET, IN_IMAGE] \\
         DISCH_THEN MATCH_MP_TAC \\
         Q.EXISTS_TAC ‘EL a (args i)’ >> rw [MEM_EL] \\
         Q.EXISTS_TAC ‘a’ \\
         Q.PAT_X_ASSUM ‘a < m i’ MP_TAC \\
         rw [Abbr ‘args'’]) \\
  (* 2nd case *)
     Cases_on ‘a < m i + LENGTH (args2 i)’
     >- (Q.PAT_X_ASSUM ‘a < LENGTH (Ns i)’ MP_TAC \\
         simp [Abbr ‘Ns’, LENGTH_TAKE] \\
         DISCH_TAC (* a < d_max *) \\
         simp [EL_TAKE] \\
         Know ‘EL a (l i) = EL (a - m i) (args2 i)’
         >- (SIMP_TAC std_ss [Abbr ‘l’, GSYM APPEND_ASSOC] \\
             qabbrev_tac ‘l2 = args2 i ++ MAP VAR xs’ \\
             Know ‘EL a (args' i ++ l2) = EL (a - LENGTH (args' i)) l2’
             >- (MATCH_MP_TAC EL_APPEND2 >> rw []) >> Rewr' \\
             simp [Abbr ‘l2’] \\
             MATCH_MP_TAC EL_APPEND1 >> rw []) >> Rewr' \\
         Know ‘b i NOTIN Z’
         >- (Q.PAT_X_ASSUM ‘DISJOINT (set xs) Z’ MP_TAC \\
             rw [DISJOINT_ALT] \\
             POP_ASSUM MATCH_MP_TAC \\
            ‘b i = EL (j i) xs’ by rw [] >> POP_ORW \\
             rw [EL_MEM]) \\
         qabbrev_tac ‘a' = a - m i’ \\
         Suff ‘FV (EL a' (args2 i)) SUBSET Z’ >- SET_TAC [] \\
         Suff ‘FV (EL a' (args2 i)) SUBSET set vs’
         >- (qunabbrev_tac ‘Z’ >> SET_TAC []) \\
        ‘a' < LENGTH (args2 i)’ by rw [Abbr ‘a'’] \\
         Q.PAT_X_ASSUM ‘a < m i + LENGTH (args2 i)’ MP_TAC \\
         Q.PAT_X_ASSUM ‘a' < LENGTH (args2 i)’ MP_TAC \\
         simp [Abbr ‘args1’, Abbr ‘args2’, EL_MAP, LENGTH_DROP] \\
         ONCE_REWRITE_TAC [GSYM MAP_DROP] \\
         simp [EL_MAP] \\
         NTAC 2 DISCH_TAC \\
         qabbrev_tac ‘a'' = EL a' (DROP (n i) (MAP VAR vs))’ \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV a''’ \\
         CONJ_TAC >- (MATCH_MP_TAC FV_ISUB_SUBSET >> art []) \\
         qunabbrev_tac ‘a''’ \\
         qabbrev_tac ‘ls = MAP VAR vs’ \\
        ‘a' + n i < LENGTH ls’ by simp [Abbr ‘ls’] \\
         Know ‘EL a' (DROP (n i) ls) = EL (a' + n i) ls’
         >- (MATCH_MP_TAC EL_DROP >> art []) >> Rewr' \\
         simp [Abbr ‘ls’, SUBSET_DEF, EL_MAP, EL_MEM]) \\
  (* 3rd case *)
     Q.PAT_X_ASSUM ‘a < LENGTH (Ns i)’ MP_TAC \\
     simp [Abbr ‘Ns’, LENGTH_TAKE] \\
     DISCH_TAC (* a < d_max *) \\
     simp [EL_TAKE] \\
     qabbrev_tac ‘ls = MAP VAR xs’ \\
     Know ‘EL a (l i) = EL (a - LENGTH (args' i ++ args2 i)) ls’
     >- (SIMP_TAC std_ss [Abbr ‘l’] \\
         qabbrev_tac ‘l1 = args' i ++ args2 i’ \\
         MATCH_MP_TAC EL_APPEND2 >> rw [Abbr ‘l1’]) >> Rewr' \\
     simp [] \\
     qabbrev_tac ‘a' = a - (m i + LENGTH (args2 i))’ \\
    ‘a' < j i’ by simp [Abbr ‘a'’, Abbr ‘j’] \\
     Know ‘a' < LENGTH xs’
     >- (MATCH_MP_TAC LESS_TRANS \\
         Q.EXISTS_TAC ‘j i’ >> rw []) >> DISCH_TAC \\
     rw [Abbr ‘ls’, EL_MAP] \\
    ‘b i = EL (j i) xs’ by rw [] >> POP_ORW \\
     SPOSE_NOT_THEN (STRIP_ASSUME_TAC o REWRITE_RULE []) \\
     Suff ‘EL (j i) xs = EL a' xs <=> j i = a'’ >- rw [] \\
     MATCH_MP_TAC ALL_DISTINCT_EL_IMP >> rw [])
 (* cleanup *)
 >> PRINT_TAC "stage work on subtree_equiv_lemma"
 >> Q.PAT_X_ASSUM ‘Boehm_transform p1’            K_TAC
 >> Q.PAT_X_ASSUM ‘Boehm_transform p2’            K_TAC
 >> Q.PAT_X_ASSUM ‘Boehm_transform p3’            K_TAC
 >> Q.PAT_X_ASSUM ‘!i. i < k ==> apply p1 _ == _’ K_TAC
 >> Q.PAT_X_ASSUM ‘!t. apply p2 t = t ISUB ss’    K_TAC
 >> Q.PAT_X_ASSUM ‘!t. i < k ==> apply p2 _ = _’  K_TAC
 >> Q.PAT_X_ASSUM ‘!i. i < k ==> apply p3 _ = _’  K_TAC
 >> Q.PAT_X_ASSUM ‘!i. i < k ==> _ -h->* _’       K_TAC
 (* This subgoal was due to modifications of agree_upto_def. It's still kept
    in case this extra subgoal may be later needed.
  *)
 >> Know ‘!i. i < k ==> p IN ltree_paths (BT' X (apply pi (M i)) r)’
 >- (rpt STRIP_TAC \\
     simp [BT_def, BT_generator_def, Once ltree_unfold,
           GSYM appstar_APPEND, LAMl_size_appstar, ltree_paths_def,
           LMAP_fromList, MAP_MAP_o] \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> p IN ltree_paths (BT' X (M i) r)’ drule \\
     simp [BT_def, BT_generator_def, Once ltree_unfold, ltree_paths_def,
           LMAP_fromList, MAP_MAP_o] \\
     simp [GSYM BT_def] \\
     qabbrev_tac ‘vs' = TAKE (n i) vs’ \\
    ‘ALL_DISTINCT vs'’
       by (qunabbrev_tac ‘vs'’ >> MATCH_MP_TAC ALL_DISTINCT_TAKE >> art []) \\
    ‘LENGTH vs' = n i’
       by (qunabbrev_tac ‘vs'’ \\
           MATCH_MP_TAC LENGTH_TAKE >> art [] \\
           FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     Q_TAC (RNEWS_TAC (“ys' :string list”, “r :num”, “(n :num -> num) i”)) ‘X’ \\
     Know ‘DISJOINT (set vs) (set ys')’
     >- (qunabbrev_tac ‘ys'’ \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘RANK r’ \\
         simp [DISJOINT_RANK_RNEWS'] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ >> art [] \\
         rw [ROW_SUBSET_RANK]) >> DISCH_TAC \\
     Know ‘DISJOINT (set vs') (set ys')’
     >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs’ >> art [] \\
         rw [Abbr ‘vs'’, LIST_TO_SET_TAKE]) >> DISCH_TAC \\
     qabbrev_tac ‘t = VAR (y i) @* args i’ \\
  (* applying for principal_hnf_tpm_reduce *)
     Know ‘principal_hnf (LAMl vs' t @* MAP VAR ys') = tpm (ZIP (vs',ys')) t’
     >- (‘hnf t’ by rw [Abbr ‘t’, hnf_appstar] \\
         MATCH_MP_TAC principal_hnf_tpm_reduce' >> art [] \\
         MATCH_MP_TAC subterm_disjoint_lemma \\
         qexistsl_tac [‘X’, ‘r’, ‘n i’] >> simp [] \\
         MATCH_MP_TAC SUBSET_TRANS \\
         Q.EXISTS_TAC ‘Z’ >> art [] \\
         rw [Abbr ‘t’, FV_appstar]) >> Rewr' \\
     simp [Abbr ‘t’, tpm_appstar] \\
     Cases_on ‘p’ >> fs [] \\
     simp [ltree_lookup, LMAP_fromList, MAP_MAP_o, LNTH_fromList, EL_MAP] \\
     Cases_on ‘h < m i’ >> simp [] \\
     qabbrev_tac ‘pm = ZIP (vs',ys')’ \\
     Know ‘d_max' i <= LENGTH (l i)’
     >- (Q.PAT_X_ASSUM ‘!i. LENGTH (l i) = _’ K_TAC \\
         simp [Abbr ‘d_max'’] \\
         MATCH_MP_TAC LT_IMP_LE \\
         Q_TAC (TRANS_TAC LESS_TRANS) ‘d_max + k’ >> simp []) >> DISCH_TAC \\
     Know ‘h < LENGTH (Ns i)’
     >- (simp [Abbr ‘Ns’] \\
         Suff ‘m i <= d_max’ >- rw [Abbr ‘d_max'’] \\
         simp [Abbr ‘d_max’] \\
         MATCH_MP_TAC LESS_EQ_TRANS \\
         Q.EXISTS_TAC ‘d’ >> simp []) >> DISCH_TAC \\
     Know ‘EL h (MAP (BT X o (\e. (e,SUC r))) (Ns i) ++
                 MAP (BT X o (\e. (e,SUC r))) (tl i)) =
           EL h (MAP (BT X o (\e. (e,SUC r))) (Ns i))’
     >- (MATCH_MP_TAC EL_APPEND1 >> simp [LENGTH_MAP]) >> Rewr' \\
     simp [EL_MAP] \\
     Know ‘EL h (Ns i) = EL h (args' i)’
     >- (gs [Abbr ‘Ns’, LENGTH_TAKE] \\
         ASM_SIMP_TAC std_ss [EL_TAKE, Abbr ‘l’, GSYM APPEND_ASSOC] \\
         MATCH_MP_TAC EL_APPEND1 >> rw [Abbr ‘args'’]) >> Rewr' \\
     qabbrev_tac ‘N = tpm pm (EL h (args i))’ \\
     qabbrev_tac ‘pm' = REVERSE pm’ \\
    ‘EL h (args' i) = (EL h (args i)) ISUB ss’
       by simp [Abbr ‘args'’, EL_MAP] >> POP_ORW \\
    ‘EL h (args i) = tpm pm' N’ by simp [Abbr ‘pm'’, Abbr ‘N’] >> POP_ORW \\
     Know ‘FV N SUBSET X UNION RANK (SUC r)’
     >- (simp [Abbr ‘N’, Abbr ‘pm'’, FV_tpm, SUBSET_DEF, IN_UNION] \\
         rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> y i IN Z /\ _’ (MP_TAC o Q.SPEC ‘i’) \\
         simp [SUBSET_DEF, IN_BIGUNION_IMAGE] >> STRIP_TAC \\
         POP_ASSUM (MP_TAC o Q.SPEC ‘lswapstr (REVERSE pm) x’) \\
         impl_tac >- (Q.EXISTS_TAC ‘EL h (args i)’ >> rw [EL_MEM]) \\
         Q.PAT_X_ASSUM ‘lswapstr (REVERSE pm) x IN FV (EL h (args i))’ K_TAC \\
         Know ‘set vs SUBSET RANK (SUC r)’
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ >> art [] \\
             rw [ROW_SUBSET_RANK]) >> DISCH_TAC \\
         Know ‘set vs' SUBSET RANK (SUC r)’
         >- (qunabbrev_tac ‘vs'’ \\
             Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs’ \\
             rw [LIST_TO_SET_TAKE]) >> DISCH_TAC \\
         Know ‘set ys' SUBSET RANK (SUC r)’
         >- (qunabbrev_tac ‘ys'’ \\
             MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw []) >> DISCH_TAC \\
         simp [Abbr ‘Z’, IN_UNION] \\
         reverse STRIP_TAC
      (* when “lswapstr (REVERSE pm) x IN set vs” is assumed *)
         >- (DISJ2_TAC >> POP_ASSUM MP_TAC >> simp [MEM_EL] \\
             DISCH_THEN (Q.X_CHOOSE_THEN ‘a’ STRIP_ASSUME_TAC) \\
             Know ‘x = lswapstr pm (EL a vs)’
             >- (POP_ASSUM (REWRITE_TAC o wrap o SYM) >> simp []) >> Rewr' \\
             qunabbrev_tac ‘pm’ \\
             MATCH_MP_TAC lswapstr_IN_RANK >> art [] \\
             CONJ_TAC >- (Q.PAT_X_ASSUM ‘set vs SUBSET RANK (SUC r)’ MP_TAC \\
                          rw [SUBSET_DEF, MEM_EL] \\
                          POP_ASSUM MATCH_MP_TAC \\
                          Q.EXISTS_TAC ‘a’ >> art []) \\
             Know ‘set ys' SUBSET ROW r’
             >- (qunabbrev_tac ‘ys'’ \\
                 MATCH_MP_TAC RNEWS_SUBSET_ROW >> art []) >> DISCH_TAC \\
             Know ‘DISJOINT (ROW 0) (ROW r)’ >- rw [ROW_DISJOINT] \\
             simp [DISJOINT_ALT] >> STRIP_TAC \\
             Suff ‘EL a vs NOTIN ROW r’ >- METIS_TAC [SUBSET_DEF] \\
             FIRST_X_ASSUM MATCH_MP_TAC \\
             Suff ‘EL a vs IN set vs’ >- METIS_TAC [SUBSET_DEF] \\
             MATCH_MP_TAC EL_MEM >> art []) \\
      (* lswapstr (REVERSE pm) x IN Y (SUBSET X UNION RANK r) *)
         Know ‘lswapstr (REVERSE pm) x IN X UNION RANK r’ >- ASM_SET_TAC [] \\
         Q.PAT_X_ASSUM ‘lswapstr (REVERSE pm) x IN Y’ K_TAC \\
         simp [IN_UNION] \\
         STRIP_TAC
         >- (FULL_SIMP_TAC std_ss [GSYM ssetpm_IN] \\
             DISJ1_TAC \\
             Suff ‘ssetpm pm X = X’ >- DISCH_THEN (FULL_SIMP_TAC std_ss o wrap) \\
             MATCH_MP_TAC ssetpm_unchanged \\
             simp [Abbr ‘pm’, MAP_ZIP] \\
             MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set vs’ >> art [] \\
             simp [Abbr ‘vs'’, LIST_TO_SET_TAKE]) \\
         DISJ2_TAC \\
         FULL_SIMP_TAC std_ss [GSYM ssetpm_IN] \\
         qabbrev_tac ‘x' = lswapstr (REVERSE pm) x’ \\
        ‘x = lswapstr pm x'’ by simp [Abbr ‘x'’] >> POP_ORW \\
      (* NOTE: if x' IN set vs' (vs, ROW 0), then ‘lswapstr pm x' IN ys'’,
         otherwise lswapstr pm x' = x'.
       *)
         Cases_on ‘x' IN set vs'’
         >- (qunabbrev_tac ‘pm’ >> MATCH_MP_TAC lswapstr_IN_RANK >> art [] \\
             CONJ_TAC >- METIS_TAC [SUBSET_DEF] \\
             METIS_TAC [DISJOINT_ALT]) \\
         Suff ‘lswapstr pm x' = x'’
         >- (Rewr \\
             Q.PAT_X_ASSUM ‘x IN ssetpm pm (RANK r)’ MP_TAC \\
             simp [Abbr ‘x'’] \\
             Suff ‘RANK r SUBSET RANK (SUC r)’ >- rw [SUBSET_DEF] \\
             rw [RANK_MONO]) \\
         MATCH_MP_TAC lswapstr_unchanged' \\
         POP_ASSUM MP_TAC \\
         Q.PAT_X_ASSUM ‘x IN ssetpm pm (RANK r)’ MP_TAC \\
         simp [Abbr ‘x'’, Abbr ‘pm’, MEM_ZIP, MAP_ZIP] \\
         qabbrev_tac ‘z = lswapstr (REVERSE (ZIP (vs',ys'))) x’ \\
         Know ‘DISJOINT (RANK r) (set ys')’
         >- rw [Abbr ‘ys'’, DISJOINT_RANK_RNEWS] \\
         rw [DISJOINT_ALT]) >> DISCH_TAC \\
  (* applying BT_ltree_paths_tpm *)
     DISCH_TAC \\
     Know ‘ltree_lookup (BT' X (tpm pm' N) (SUC r)) t <> NONE’
     >- (POP_ASSUM MP_TAC \\
         Suff ‘ltree_paths (BT' X N (SUC r)) =
               ltree_paths (BT' X (tpm pm' N) (SUC r))’
         >- simp [ltree_paths_def, Once EXTENSION] \\
         MATCH_MP_TAC BT_ltree_paths_tpm >> art [] \\
         simp [Abbr ‘pm'’, Abbr ‘pm’, MAP_REVERSE, MAP_ZIP] \\
         reverse CONJ_TAC
         >- (qunabbrev_tac ‘ys'’ \\
             MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw []) \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs’ \\
         CONJ_TAC >- rw [Abbr ‘vs'’, LIST_TO_SET_TAKE] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ >> art [] \\
         rw [ROW_SUBSET_RANK]) \\
     NTAC 2 (POP_ASSUM K_TAC) \\
     fs [Abbr ‘pm'’, Abbr ‘N’] >> T_TAC \\
     qabbrev_tac ‘N = EL h (args i)’ \\
  (* applying subterm_width_isub_permutator_cong *)
    ‘!M. ltree_lookup (BT' X M (SUC r)) t <> NONE <=>
         t IN ltree_paths (BT' X M (SUC r))’ by rw [ltree_paths_def] \\
     POP_ORW >> DISCH_TAC \\
     MATCH_MP_TAC (cj 1 subterm_width_isub_permutator_cong_alt) \\
     qexistsl_tac [‘d_max’, ‘y’, ‘k’] >> simp [] \\
     CONJ_TAC
     >- (Suff ‘FV N SUBSET X UNION RANK r’
         >- (Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
             rw [RANK_MONO]) \\
         qunabbrev_tac ‘N’ >> FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     CONJ_TAC
     >- (Q.X_GEN_TAC ‘J’ >> DISCH_TAC \\
         Know ‘y J IN Z’ >- rw [] \\
         Suff ‘Z SUBSET X UNION RANK (SUC r)’ >- rw [SUBSET_DEF] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘X UNION RANK r’ >> art [] \\
         Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [RANK_MONO]) \\
     Know ‘subterm_width (M i) (h::t) <= d’ >- rw [] \\
     qabbrev_tac ‘Ms' = args i ++ DROP (n i) (MAP VAR vs)’ \\
  (* applying subterm_width_induction_lemma (the general one) *)
     Suff ‘subterm_width (M i) (h::t) <= d <=>
           m i <= d /\ subterm_width (EL h Ms') t <= d’
     >- (Rewr' \\
         Know ‘EL h Ms' = N’
         >- (simp [Abbr ‘Ms'’, Abbr ‘N’] \\
             MATCH_MP_TAC EL_APPEND1 >> simp []) >> Rewr' \\
         STRIP_TAC \\
         Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘d’ >> art [] \\
         simp [Abbr ‘d_max’]) \\
  (* stage work *)
     MATCH_MP_TAC subterm_width_induction_lemma_alt \\
     qexistsl_tac [‘X’, ‘Y’, ‘r’, ‘M0 i’, ‘n i’, ‘n_max’, ‘vs’, ‘M1 i’] \\
     simp [GSYM appstar_APPEND] \\
     rw [SUBSET_DEF, Abbr ‘Y’] \\
     Q.EXISTS_TAC ‘FV (M i)’ >> art [] \\
     Q.EXISTS_TAC ‘M i’ >> rw [Abbr ‘M’, EL_MEM])
 >> DISCH_TAC
 (* stage work *)
 >> CONJ_TAC >- (rw [EVERY_EL] >> simp [EL_MAP])
 (* upper bound of all FVs from l (args' ++ args2 ++ xs) *)
 >> Know ‘!i. i < k ==> BIGUNION (IMAGE FV (set (l i))) SUBSET X UNION RANK r’
 >- (simp [Abbr ‘l’] >> rpt STRIP_TAC >| (* 3 subgoals *)
     [ (* goal 1 (of 3): args' *)
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘Z’ >> art [] \\
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘BIGUNION (IMAGE FV (set (args i)))’ \\
       simp [] \\
       rw [SUBSET_DEF, IN_BIGUNION_IMAGE] \\
       rename1 ‘x IN FV t’ \\
       Q.PAT_X_ASSUM ‘MEM t (args' i)’ MP_TAC \\
       rw [MEM_EL] >> rename1 ‘h < m i’ \\
       Q.EXISTS_TAC ‘EL h (args i)’ \\
       CONJ_TAC >- (Q.EXISTS_TAC ‘h’ >> art []) \\
       Q.PAT_X_ASSUM ‘x IN FV (EL h (args' i))’ MP_TAC \\
       Suff ‘FV (EL h (args' i)) SUBSET FV (EL h (args i))’ >- rw [SUBSET_DEF] \\
       simp [Abbr ‘args'’, EL_MAP] \\
       qabbrev_tac ‘N = EL h (args i)’ \\
       MP_TAC (Q.SPECL [‘ss’, ‘N’] FV_ISUB_upperbound) >> rw [],
       (* goal 2 (of 3): args2 *)
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘BIGUNION (IMAGE FV (set args1))’ \\
       CONJ_TAC
       >- (MATCH_MP_TAC SUBSET_BIGUNION \\
           MATCH_MP_TAC IMAGE_SUBSET \\
           rw [Abbr ‘args2’, LIST_TO_SET_DROP]) \\
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs’ >> art [] \\
       Suff ‘set vs SUBSET RANK r’ >- SET_TAC [] \\
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ \\
       CONJ_TAC >- rw [Abbr ‘vs’, RNEWS_SUBSET_ROW] \\
       MATCH_MP_TAC ROW_SUBSET_RANK >> art [],
       (* goal 3 (of 3): xs *)
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘RANK r’ \\
       reverse CONJ_TAC >- SET_TAC [] \\
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ \\
       simp [ROW_SUBSET_RANK] \\
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs0’ >> art [] \\
       simp [Abbr ‘vs0’, RNEWS_SUBSET_ROW] ])
 >> DISCH_TAC
 (* ‘H i’ is the head reduction of apply pi (M i) *)
 >> qabbrev_tac ‘H = \i. VAR (b i) @* Ns i @* tl i’
 >> Know ‘!i. solvable (H i)’
 >- (rw [Abbr ‘H’] \\
     MATCH_MP_TAC hnf_solvable >> rw [hnf_appstar])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==> FV (H i) SUBSET X UNION RANK r’
 >- (simp [Abbr ‘H’, GSYM appstar_APPEND, FV_appstar] \\
     rpt STRIP_TAC >| (* 3 subgoals *)
     [ (* goal 1 (of 3): easier *)
       REWRITE_TAC [IN_UNION] >> DISJ2_TAC \\
       Suff ‘b i IN ROW 0’
       >- (Suff ‘ROW 0 SUBSET RANK r’ >- METIS_TAC [SUBSET_DEF] \\
           rw [ROW_SUBSET_RANK]) \\
       Q.PAT_X_ASSUM ‘!i. i < k ==> EL (j i) xs = b i /\ _’ drule \\
       STRIP_TAC \\
       Q.PAT_X_ASSUM ‘EL (j i) xs = b i’ (REWRITE_TAC o wrap o SYM) \\
       Suff ‘set xs SUBSET ROW 0’
       >- (rw [SUBSET_DEF] \\
           POP_ASSUM MATCH_MP_TAC >> simp [EL_MEM]) \\
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs0’ >> art [] \\
       simp [Abbr ‘vs0’, RNEWS_SUBSET_ROW],
       (* goal 2 (of 3): hard but now easy *)
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘BIGUNION (IMAGE FV (set (l i)))’ \\
       simp [Abbr ‘Ns’] \\
       MATCH_MP_TAC SUBSET_BIGUNION \\
       MATCH_MP_TAC IMAGE_SUBSET >> rw [LIST_TO_SET_TAKE],
       (* goal 3 (of 3): not that hard *)
       Q_TAC (TRANS_TAC SUBSET_TRANS) ‘BIGUNION (IMAGE FV (set (l i)))’ \\
       simp [Abbr ‘tl’] \\
       MATCH_MP_TAC SUBSET_BIGUNION \\
       MATCH_MP_TAC IMAGE_SUBSET >> rw [LIST_TO_SET_DROP] ])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==> d_max <= LENGTH (hnf_children (H i))’
 >- (rw [Abbr ‘H’, GSYM appstar_APPEND] \\
     simp [Abbr ‘Ns’] \\
     simp [Abbr ‘d_max'’])
 >> DISCH_TAC
 (* stage work, now connect ‘subterm X (M i) q’ with ‘subterm X (H i) q’ *)
 >> Q_TAC (RNEWS_TAC (“ys :string list”, “r :num”, “n_max :num”)) ‘X’
 >> qabbrev_tac ‘pm = ZIP (vs,ys)’
 >> Know ‘DISJOINT (set vs) (set ys)’
 >- (Q.PAT_X_ASSUM ‘_ = vs’ (REWRITE_TAC o wrap o SYM) \\
     qunabbrev_tac ‘ys’ \\
     MATCH_MP_TAC DISJOINT_RNEWS >> simp [])
 >> DISCH_TAC
 >> PRINT_TAC "stage work on subtree_equiv_lemma"
 (* Now ‘subterm X (M i) q r <> NONE’ is added into antecedents of the subgoal *)
 >> Know ‘!q. q <<= p /\ q <> [] ==>
              !i. i < k ==> subterm X (H i) q r <> NONE /\
                            subterm' X (H i) q r =
                           (tpm (REVERSE pm) (subterm' X (M i) q r)) ISUB ss’
 >- (Q.X_GEN_TAC ‘q’ >> STRIP_TAC \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘!i q. i < k /\ q <<= p ==> subterm X (M i) q r <> NONE’
        (MP_TAC o Q.SPECL [‘i’, ‘q’]) >> simp [] \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> subterm_width (M i) p <= d’ drule \\
     Cases_on ‘p’ >> fs [] \\
     Cases_on ‘q’ >> fs [] \\
     Q.PAT_X_ASSUM ‘h' = h’ (fs o wrap) >> T_TAC \\
     simp [subterm_of_solvables] \\
     Know ‘principal_hnf (H i) = H i’
     >- (MATCH_MP_TAC principal_hnf_reduce \\
         simp [Abbr ‘H’, GSYM appstar_APPEND, hnf_appstar]) >> DISCH_TAC \\
    ‘LAMl_size (H i) = 0’
       by rw [Abbr ‘H’, LAMl_size_appstar, GSYM appstar_APPEND] \\
     simp [] \\
     NTAC 2 (POP_ASSUM K_TAC) (* principal_hnf (H i), LAMl_size (H i) *) \\
     DISCH_TAC (* subterm_width (M i) (h::t) <= d *) \\
     Q_TAC (RNEWS_TAC (“ys' :string list”, “r :num”, “(n :num -> num) i”)) ‘X’ \\
     qabbrev_tac ‘vs' = TAKE (n i) vs’ \\
    ‘ALL_DISTINCT vs' /\ LENGTH vs' = n i’
       by rw [ALL_DISTINCT_TAKE, Abbr ‘vs'’] \\
     qabbrev_tac ‘t0 = VAR (y i) @* args i’ \\
  (* prove that ‘ys' = TAKE (n i) ys’ *)
     MP_TAC (Q.SPECL [‘r’, ‘n (i :num)’, ‘n_max’, ‘X’] RNEWS_prefix) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘ni’
                   (STRIP_ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ])) \\
     Know ‘ni = n i’
     >- (Know ‘LENGTH ys' = LENGTH (TAKE ni ys)’ >- rw [] \\
         simp [LENGTH_TAKE]) \\
     DISCH_THEN (rfs o wrap) >> T_TAC \\
     Know ‘DISJOINT (set vs) (set ys)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘ROW 0’ >> art [] \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘ROW r’ \\
         simp [Abbr ‘ys’, RNEWS_SUBSET_ROW] \\
         rw [Once DISJOINT_SYM, ROW_DISJOINT]) >> DISCH_TAC \\
     Know ‘DISJOINT (set vs') (set ys')’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set ys’ \\
         reverse CONJ_TAC >- rw [LIST_TO_SET_TAKE] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs’ \\
         simp [Abbr ‘vs'’, LIST_TO_SET_TAKE]) >> DISCH_TAC \\
  (* applying for principal_hnf_tpm_reduce *)
     Know ‘principal_hnf (LAMl vs' t0 @* MAP VAR ys') = tpm (ZIP (vs',ys')) t0’
     >- (‘hnf t0’ by rw [Abbr ‘t0’, hnf_appstar] \\
         MATCH_MP_TAC principal_hnf_tpm_reduce' >> art [] \\
         MATCH_MP_TAC subterm_disjoint_lemma \\
         qexistsl_tac [‘X’, ‘r’, ‘n i’] >> simp [] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘Z’ >> art [] \\
         rw [Abbr ‘t0’, FV_appstar]) >> Rewr' \\
     simp [Abbr ‘t0’, tpm_appstar, hnf_children_appstar] \\
     Cases_on ‘h < m i’ >> simp [] \\
     Know ‘h < d_max’
     >- (Q_TAC (TRANS_TAC LESS_LESS_EQ_TRANS) ‘m i’ >> art [] \\
         Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘d’ >> simp [] \\
         simp [Abbr ‘d_max’]) >> DISCH_TAC \\
    ‘h < d_max' i’ by rw [Abbr ‘d_max'’] \\
     Know ‘h < LENGTH (hnf_children (H i))’
     >- (Q_TAC (TRANS_TAC LESS_LESS_EQ_TRANS) ‘d_max’ \\
         simp []) >> Rewr \\
     Know ‘EL h (hnf_children (H i)) = EL h (Ns i)’
     >- (simp [Abbr ‘H’, GSYM appstar_APPEND] \\
         MATCH_MP_TAC EL_APPEND1 >> simp [Abbr ‘Ns’]) >> Rewr' \\
     Know ‘EL h (Ns i) = EL h (args' i)’
     >- (simp [Abbr ‘Ns’] \\
         Know ‘EL h (TAKE (d_max' i) (l i)) = EL h (l i)’
         >- (MATCH_MP_TAC EL_TAKE >> art []) >> Rewr' \\
         simp [Abbr ‘l’] \\
         REWRITE_TAC [GSYM APPEND_ASSOC] \\
         MATCH_MP_TAC EL_APPEND1 \\
         simp [Abbr ‘args'’]) >> Rewr' \\
     qabbrev_tac ‘N = EL h (args i)’ \\
     fs [Abbr ‘args'’, EL_MAP] >> T_TAC \\
     qabbrev_tac ‘pm' = ZIP (vs',ys')’ \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs') (set ys')’ K_TAC \\
  (* applying tpm_unchanged *)
     Know ‘tpm pm' N = tpm pm N’ (* (n i) vs. n_max *)
     >- (simp [Abbr ‘pm'’, Abbr ‘vs'’] \\
         Q.PAT_X_ASSUM ‘TAKE (n i) ys = ys'’ (REWRITE_TAC o wrap o SYM) \\
         simp [ZIP_TAKE] \\
        ‘tpm pm N = tpm (TAKE (n i) pm ++ DROP (n i) pm) N’
           by rw [TAKE_DROP] >> POP_ORW \\
         REWRITE_TAC [pmact_append] \\
         Suff ‘tpm (DROP (n i) pm) N = N’ >- rw [] \\
         MATCH_MP_TAC tpm_unchanged \\
         simp [Abbr ‘pm’, GSYM ZIP_DROP, MAP_ZIP] \\
         Q.PAT_X_ASSUM ‘ALL_DISTINCT (TAKE (n i) vs)’ K_TAC \\
         Q.PAT_X_ASSUM ‘LENGTH (TAKE (n i) vs) = n i’ K_TAC \\
         Know ‘FV N SUBSET FV (M i) UNION set (TAKE (n i) vs)’
         >- (Q.PAT_X_ASSUM
               ‘!i. i < k ==> BIGUNION (IMAGE FV (set (args i))) SUBSET _’ drule \\
             rw [SUBSET_DEF] \\
             FIRST_X_ASSUM MATCH_MP_TAC \\
             Q.EXISTS_TAC ‘FV N’ >> art [] \\
             Q.EXISTS_TAC ‘N’ >> simp [Abbr ‘N’, EL_MEM]) \\
         DISCH_TAC \\
      (* NOTE: FV (M i) SUBSET Y SUBSET X UNION RANK r *)
         reverse CONJ_TAC (* ys is easier *)
         >- (Know ‘DISJOINT (set ys) (FV (M i))’
             >- (MATCH_MP_TAC subterm_disjoint_lemma \\
                 qexistsl_tac [‘X’, ‘r’, ‘n_max’] >> simp []) \\
             DISCH_TAC \\
             MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set ys’ \\
             simp [LIST_TO_SET_DROP] \\
             simp [DISJOINT_ALT'] >> rpt STRIP_TAC \\
             Know ‘x IN FV (M i) UNION set (TAKE (n i) vs)’
             >- METIS_TAC [SUBSET_DEF] \\
             simp [IN_UNION] \\
             CONJ_TAC
             >- (Q.PAT_X_ASSUM ‘DISJOINT (set ys) (FV (M i))’ MP_TAC \\
                 rw [DISJOINT_ALT]) \\
             Suff ‘DISJOINT (set (TAKE (n i) vs)) (set ys)’
             >- rw [DISJOINT_ALT'] \\
             MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set vs’ >> rw [LIST_TO_SET_TAKE]) \\
      (* vs is slightly harder *)
         simp [DISJOINT_ALT'] >> rpt STRIP_TAC \\
         Know ‘x IN FV (M i) UNION set (TAKE (n i) vs)’
         >- METIS_TAC [SUBSET_DEF] \\
         simp [IN_UNION] \\
         reverse CONJ_TAC
         >- (Know ‘ALL_DISTINCT (TAKE (n i) vs ++ DROP (n i) vs)’
             >- rw [TAKE_DROP] \\
             simp [ALL_DISTINCT_APPEND', DISJOINT_ALT']) \\
         Suff ‘DISJOINT (set (DROP (n i) vs)) (FV (M i))’ >- rw [DISJOINT_ALT] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs’ \\
         simp [LIST_TO_SET_DROP] \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘Y’ >> art [] \\
         simp [Abbr ‘Y’, SUBSET_DEF] \\
         Q.X_GEN_TAC ‘v’ >> DISCH_TAC \\
         Q.EXISTS_TAC ‘FV (M i)’ >> art [] \\
         Q.EXISTS_TAC ‘M i’ >> simp [Abbr ‘M’, EL_MEM]) >> Rewr' \\
     qunabbrev_tac ‘pm'’ \\
  (* some shared subgoals to be used later *)
     Know ‘set ys SUBSET X UNION RANK (SUC r)’
     >- (Suff ‘set ys SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         qunabbrev_tac ‘ys’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp []) >> DISCH_TAC \\
     Know ‘FV N SUBSET X UNION RANK (SUC r)’
     >- (Suff ‘FV N SUBSET X UNION RANK r’
         >- (Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
             rw [RANK_MONO]) \\
         qunabbrev_tac ‘N’ \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC \\
     Know ‘DISJOINT (set ys) (FV (M i))’
     >- (MATCH_MP_TAC subterm_disjoint_lemma \\
         qexistsl_tac [‘X’, ‘r’, ‘n_max’] >> simp []) >> DISCH_TAC \\
     Know ‘DISJOINT (set ys) (FV N)’
     >- (Q.PAT_X_ASSUM ‘!i. i < k ==> _ SUBSET FV (M i) UNION _’ drule \\
         simp [BIGUNION_SUBSET] >> STRIP_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV (M i) UNION set vs'’ \\
         reverse CONJ_TAC
         >- (POP_ASSUM MATCH_MP_TAC \\
             Q.EXISTS_TAC ‘N’ >> simp [Abbr ‘N’, EL_MEM]) \\
         simp [DISJOINT_UNION'] \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs’ \\
         simp [Once DISJOINT_SYM, Abbr ‘vs'’, LIST_TO_SET_TAKE]) \\
     DISCH_TAC \\
  (* applying subterm_fresh_tpm_cong *)
     DISCH_TAC (* subterm X (tpm pm N) t (SUC r) <> NONE *) \\
     MP_TAC (Q.SPECL [‘pm’, ‘X’, ‘N’, ‘t'’, ‘SUC r’] subterm_fresh_tpm_cong) \\
     impl_tac >- simp [Abbr ‘pm’, MAP_ZIP] \\
     simp [] \\
     STRIP_TAC >> POP_ASSUM K_TAC (* already used *) \\
  (* applying subterm_isub_permutator_cong' *)
     MATCH_MP_TAC subterm_isub_permutator_cong_alt' \\
     qexistsl_tac [‘d_max’, ‘y’, ‘k’] >> simp [] \\
     CONJ_TAC (* easier *)
     >- (rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> y i IN Z /\ _’ drule \\
         qunabbrev_tac ‘Z’ >> STRIP_TAC \\
         rename1 ‘i' < k’ \\
         Q.PAT_X_ASSUM ‘y i' IN Y UNION set vs’ MP_TAC \\
         Suff ‘Y UNION set vs SUBSET X UNION RANK (SUC r)’ >- SET_TAC [] \\
         rw [UNION_SUBSET] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘X UNION RANK r’ >> art [] \\
         Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [RANK_MONO]) \\
  (* subterm_width N t <= d_max *)
     Know ‘subterm_width (M i) (h::t') <= d’
     >- (MATCH_MP_TAC subterm_width_inclusive \\
         Q.EXISTS_TAC ‘h::t’ >> simp []) \\
     qabbrev_tac ‘Ms' = args i ++ DROP (n i) (MAP VAR vs)’ \\
  (* applying subterm_width_induction_lemma (the general one) *)
     Suff ‘subterm_width (M i) (h::t') <= d <=>
           m i <= d /\ subterm_width (EL h Ms') t' <= d’
     >- (Rewr' \\
         Know ‘EL h Ms' = N’
         >- (simp [Abbr ‘Ms'’, Abbr ‘N’] \\
             MATCH_MP_TAC EL_APPEND1 >> simp []) >> Rewr' \\
         STRIP_TAC \\
         Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘d’ >> art [] \\
         simp [Abbr ‘d_max’]) \\
  (* stage work *)
     MATCH_MP_TAC subterm_width_induction_lemma_alt \\
     qexistsl_tac [‘X’, ‘Y’, ‘r’, ‘M0 i’, ‘n i’, ‘n_max’, ‘vs’, ‘M1 i’] \\
     simp [GSYM appstar_APPEND] \\
     rw [SUBSET_DEF, Abbr ‘Y’]
     >- (Q.EXISTS_TAC ‘FV (M i)’ >> art [] \\
         Q.EXISTS_TAC ‘M i’ >> art [] \\
         rw [Abbr ‘M’, EL_MEM]) \\
     MATCH_MP_TAC ltree_paths_inclusive \\
     Q.EXISTS_TAC ‘h::t’ >> simp [])
 >> DISCH_TAC
 >> PRINT_TAC "stage work on subtree_equiv_lemma"
 >> Suff ‘(!M N q.
            MEM M Ms /\ MEM N Ms /\ q <<= p /\
            subtree_equiv X M N q r ==>
            subtree_equiv X (apply pi M) (apply pi N) q r /\
           (solvable (subterm' X M q r) ==>
            solvable (subterm' X (apply pi M) q r))) /\
          (!M N q.
            MEM M Ms /\ MEM N Ms /\ q <<= p /\
            subtree_equiv X (apply pi M) (apply pi N) q r ==>
            subtree_equiv X M N q r /\
           (solvable (subterm' X (apply pi M) q r) ==>
            solvable (subterm' X M q r)))’
 >- (STRIP_TAC \\
     CONJ_TAC (* extra goal *)
     >- (qx_genl_tac [‘q’, ‘t’] >> STRIP_TAC \\
         EQ_TAC >> STRIP_TAC >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           Q.PAT_X_ASSUM ‘!M N q. MEM M Ms /\ MEM N Ms /\ q <<= p /\
                                  subtree_equiv X M N q r ==> _’
             (MP_TAC o Q.SPECL [‘t’, ‘t’, ‘q’]) >> simp [],
           (* goal 2 (of 2) *)
           Q.PAT_X_ASSUM
             ‘!M N q. MEM M Ms /\ MEM N Ms /\ q <<= p /\
                      subtree_equiv X (apply pi M) (apply pi N) q r ==> _’
             (MP_TAC o Q.SPECL [‘t’, ‘t’, ‘q’]) >> simp [] ]) \\
     METIS_TAC [])
 (* stage work, next goal:

    !M N q. MEM M Ms /\ MEM N Ms /\ q <<= p /\ subtree_equiv X M N q r ==>
            subtree_equiv X (apply pi M) (apply pi N) q r)
  *)
 >> CONJ_ASM1_TAC
 >- (qx_genl_tac [‘M2’, ‘N2’, ‘q’] >> simp [MEM_EL] \\
     ONCE_REWRITE_TAC
       [TAUT ‘p /\ q /\ r /\ s ==> t <=> p ==> q ==> r ==> s ==> t’] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘j1’ STRIP_ASSUME_TAC) \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘j2’ STRIP_ASSUME_TAC) \\
     DISCH_TAC (* q <<= p *) \\
     Q.PAT_X_ASSUM ‘_ = M j1’ (REWRITE_TAC o wrap) \\
     Q.PAT_X_ASSUM ‘_ = M j2’ (REWRITE_TAC o wrap) \\
     qabbrev_tac ‘M' = \i. apply pi (M i)’ >> simp [] \\
     simp [subtree_equiv_def] \\
  (* applying BT_of_principal_hnf *)
     Know ‘BT' X (M' j1) r = BT' X (principal_hnf (M' j1)) r’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC BT_of_principal_hnf \\
         simp [Abbr ‘M'’] \\
         METIS_TAC [lameq_solvable_cong]) >> Rewr' \\
     Know ‘BT' X (M' j2) r = BT' X (principal_hnf (M' j2)) r’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC BT_of_principal_hnf \\
         simp [Abbr ‘M'’] \\
         METIS_TAC [lameq_solvable_cong]) >> Rewr' \\
     simp [Abbr ‘M'’] \\
  (* NOTE: now we are still missing some important connections:
   - ltree_el (BT X M2) q            ~1~  subterm' X M2 q
   - ltree_el (BT X N2) q            ~1~  subterm' X N2 q
   - ltree_el (BT X (apply pi M2) q  ~1~  subterm' X (apply pi M2) q
   - ltree_el (BT X (apply pi N2) q  ~1~  subterm' X (apply pi N2) q
   - subterm' X (apply pi M2) q      ~2~  subterm' X M2 q
   - subterm' X (apply pi N2) q      ~2~  subterm' X N2 q

     where the relation ~1~ is to be established by BT_subterm_thm, and ~2~
     follows a similar idea of [Boehm_transform_exists_lemma].
   *)
     Cases_on ‘q = []’
     >- (POP_ORW >> simp [BT_ltree_el_NIL] \\
         Know ‘!i. principal_hnf (H i) = H i’
         >- (rw [Abbr ‘H’] >> MATCH_MP_TAC principal_hnf_reduce \\
             rw [hnf_appstar]) >> Rewr' \\
         Q.PAT_X_ASSUM ‘!q. q <<= p /\ q <> [] ==> _’ K_TAC \\
         simp [Abbr ‘H’, GSYM appstar_APPEND, hnf_head_appstar] \\
         simp [head_equivalent_def] \\
         qabbrev_tac ‘vs1 = TAKE (n j1) vs’ \\
         qabbrev_tac ‘vs2 = TAKE (n j2) vs’ \\
        ‘ALL_DISTINCT vs1 /\ ALL_DISTINCT vs2’
           by simp [Abbr ‘vs1’, Abbr ‘vs2’, ALL_DISTINCT_TAKE] \\
        ‘LENGTH vs1 = n j1’
           by (qunabbrev_tac ‘vs1’ \\
               MATCH_MP_TAC LENGTH_TAKE >> art [] \\
               FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
        ‘LENGTH vs2 = n j2’
           by (qunabbrev_tac ‘vs2’ \\
               MATCH_MP_TAC LENGTH_TAKE >> art [] \\
               FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
         Q_TAC (RNEWS_TAC (“ys1 :string list”, “r :num”, “(n :num->num) j1”)) ‘X’ \\
         Q_TAC (RNEWS_TAC (“ys2 :string list”, “r :num”, “(n :num->num) j2”)) ‘X’ \\
         Know ‘DISJOINT (set vs1) (set ys1)’
         >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set vs’ \\
             reverse CONJ_TAC >- rw [Abbr ‘vs1’, LIST_TO_SET_TAKE] \\
             qunabbrev_tac ‘ys1’ \\
             MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘RANK r’ >> simp [DISJOINT_RANK_RNEWS']) >> DISCH_TAC \\
         Know ‘DISJOINT (set vs2) (set ys2)’
         >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set vs’ \\
             reverse CONJ_TAC >- rw [Abbr ‘vs2’, LIST_TO_SET_TAKE] \\
             qunabbrev_tac ‘ys2’ \\
             MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘RANK r’ >> simp [DISJOINT_RANK_RNEWS']) >> DISCH_TAC \\
         qabbrev_tac ‘t1 = VAR (y j1) @* args j1’ \\
         qabbrev_tac ‘t2 = VAR (y j2) @* args j2’ \\
      (* applying for principal_hnf_tpm_reduce *)
         Know ‘principal_hnf (LAMl vs1 t1 @* MAP VAR ys1) = tpm (ZIP (vs1,ys1)) t1’
         >- (‘hnf t1’ by rw [Abbr ‘t1’, hnf_appstar] \\
             MATCH_MP_TAC principal_hnf_tpm_reduce' >> art [] \\
             MATCH_MP_TAC subterm_disjoint_lemma \\
             qexistsl_tac [‘X’, ‘r’, ‘n j1’] >> simp [] \\
             MATCH_MP_TAC SUBSET_TRANS \\
             Q.EXISTS_TAC ‘Z’ >> art [] \\
             rw [Abbr ‘t1’, FV_appstar]) >> Rewr' \\
         Know ‘principal_hnf (LAMl vs2 t2 @* MAP VAR ys2) = tpm (ZIP (vs2,ys2)) t2’
         >- (‘hnf t2’ by rw [Abbr ‘t2’, hnf_appstar] \\
             MATCH_MP_TAC principal_hnf_tpm_reduce' >> art [] \\
             MATCH_MP_TAC subterm_disjoint_lemma \\
             qexistsl_tac [‘X’, ‘r’, ‘n j2’] >> simp [] \\
             MATCH_MP_TAC SUBSET_TRANS \\
             Q.EXISTS_TAC ‘Z’ >> art [] \\
             rw [Abbr ‘t2’, FV_appstar]) >> Rewr' \\
         simp [Abbr ‘t1’, Abbr ‘t2’, tpm_appstar] >> STRIP_TAC \\
         Know ‘LENGTH (l j1) = LENGTH (l j2)’
         >- (simp [] \\
            ‘n j1 <= n_max /\ n j2 <= n_max’ by rw [] \\
             simp []) >> DISCH_TAC \\
         reverse CONJ_TAC
         >- (simp [Abbr ‘Ns’, Abbr ‘tl’, Abbr ‘d_max'’] \\
            ‘f j1 < k /\ f j2 < k’ by rw [] >> simp []) \\
        ‘b j1 = EL (j j1) xs /\ b j2 = EL (j j2) xs’ by rw [] \\
         NTAC 2 POP_ORW \\
         Suff ‘j j1 = j j2’ >- Rewr \\
         simp [Abbr ‘j’, Abbr ‘args'’, Abbr ‘args2’] \\
        ‘n j1 <= n_max /\ n j2 <= n_max’ by rw [] \\
        ‘f j1 < k /\ f j2 < k’ by rw [] \\
         simp [Abbr ‘d_max'’] \\
         Suff ‘f j1 = f j2’ >- rw [] \\
      (* NOTE: current situation:

        |<--------- vs (n_max) --------->|
        |<--- vs1 ----->|<---- vs1'----->|      y j1  ---+
        |<------ vs2 ------->|<--vs2'--->|      y j2  ---|--+
     ----------------------------------------------------|--|----
        |<--- ys1 ----->|------ys1'----->|      y' <-----+  |
        |<------ ys2 ------->|<--ys2'--->|      y' <--------+

        lswapstr (ZIP (vs, ys))  (y j1) =
        lswapstr (ZIP (vs1,ys1)) (y j1) =
        lswapstr (ZIP (vs2,ys2)) (y j2) =
        lswapstr (ZIP (vs, ys))  (y j2) ==> y j1 = y j2

        P (f j1) = VAR (y j1) ISUB ss = VAR (y j2) ISUB ss = P (f j2)
    ==> permutator (d_max + f j1) = permutator (d_max + f j2)
    ==> d_max + f j1 = d_max + f j2 ==> f j1 = f j2
       *)
         PRINT_TAC "stage work on subtree_equiv_lemma" \\
         Suff ‘y j1 = y j2’
         >- (DISCH_TAC \\
             Know ‘VAR (y j1) ISUB ss = VAR (y j2) ISUB ss’
             >- POP_ASSUM (REWRITE_TAC o wrap) \\
             POP_ASSUM K_TAC \\
             simp [Abbr ‘P’]) (* permutator_11 is used here *) \\
         qabbrev_tac ‘vs1' = DROP (n j1) vs’ \\
         qabbrev_tac ‘vs2' = DROP (n j2) vs’ \\
         Know ‘ys1 <<= ys’
         >- (qunabbrevl_tac [‘ys1’, ‘ys’] \\
             MATCH_MP_TAC RNEWS_prefix >> simp []) \\
         simp [IS_PREFIX_EQ_TAKE] \\
         DISCH_THEN (Q.X_CHOOSE_THEN ‘n1'’ STRIP_ASSUME_TAC) \\
         Know ‘n1' = n j1’
         >- (POP_ASSUM (MP_TAC o AP_TERM “LENGTH :string list -> num”) \\
             simp [LENGTH_TAKE]) >> DISCH_TAC \\
         Q.PAT_X_ASSUM ‘n1' <= n_max’ MP_TAC \\
         Q.PAT_X_ASSUM ‘ys1 = TAKE n1' ys’
           (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
         POP_ORW >> rpt STRIP_TAC \\
         qabbrev_tac ‘ys1' = DROP (n j1) ys’ \\
        ‘vs1 ++ vs1' = vs /\ ys1 ++ ys1' = ys’ by METIS_TAC [TAKE_DROP] \\
         Know ‘ys2 <<= ys’
         >- (qunabbrevl_tac [‘ys2’, ‘ys’] \\
             MATCH_MP_TAC RNEWS_prefix >> simp []) \\
         simp [IS_PREFIX_EQ_TAKE] \\
         DISCH_THEN (Q.X_CHOOSE_THEN ‘n2'’ STRIP_ASSUME_TAC) \\
         Know ‘n2' = n j2’
         >- (POP_ASSUM (MP_TAC o AP_TERM “LENGTH :string list -> num”) \\
             simp [LENGTH_TAKE]) >> DISCH_TAC \\
         Q.PAT_X_ASSUM ‘n2' <= n_max’ MP_TAC \\
         Q.PAT_X_ASSUM ‘ys2 = TAKE n2' ys’
           (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
         POP_ORW >> rpt STRIP_TAC \\
         qabbrev_tac ‘ys2' = DROP (n j2) ys’ \\
        ‘vs2 ++ vs2' = vs /\ ys2 ++ ys2' = ys’ by METIS_TAC [TAKE_DROP] \\
         qabbrev_tac ‘pm1 = ZIP (vs1,ys1)’ \\
         qabbrev_tac ‘pm2 = ZIP (vs2,ys2)’ \\
         Suff ‘lswapstr pm1 (y j1) = lswapstr pm (y j1) /\
               lswapstr pm2 (y j2) = lswapstr pm (y j2)’
         >- (STRIP_TAC \\
             Q.PAT_X_ASSUM ‘lswapstr pm1 (y j1) = lswapstr pm2 (y j2)’ MP_TAC \\
             simp []) \\
         Q.PAT_X_ASSUM ‘lswapstr pm1 (y j1) = lswapstr pm2 (y j2)’ K_TAC \\
         CONJ_TAC >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
          ‘LENGTH vs1' = LENGTH ys1'’ by rw [Abbr ‘vs1'’, Abbr ‘ys1'’] \\
           Know ‘pm = pm1 ++ ZIP (vs1',ys1')’
           >- (simp [Abbr ‘pm’, Abbr ‘pm1’] \\
              ‘LENGTH vs1 = LENGTH ys1’ by rw [Abbr ‘vs1'’] \\
               simp [ZIP_APPEND]) >> Rewr' \\
           simp [lswapstr_append, Once EQ_SYM_EQ] \\
           MATCH_MP_TAC lswapstr_unchanged' >> simp [MAP_ZIP] \\
           reverse CONJ_TAC (* easy goal first *)
           >- (‘y j1 IN X UNION RANK r’ by METIS_TAC [SUBSET_DEF] \\
               Suff ‘DISJOINT (X UNION RANK r) (set ys1')’
               >- (REWRITE_TAC [DISJOINT_ALT] \\
                   DISCH_THEN MATCH_MP_TAC >> art []) \\
               MATCH_MP_TAC DISJOINT_SUBSET \\
               Q.EXISTS_TAC ‘set ys’ \\
               reverse CONJ_TAC >- simp [Abbr ‘ys1'’, LIST_TO_SET_DROP] \\
               simp [DISJOINT_UNION', Once DISJOINT_SYM] \\
               simp [Abbr ‘ys’, Once DISJOINT_SYM, DISJOINT_RNEWS_RANK]) \\
        (* current goal: ~MEM (y j1) vs1'

           M0 i = LAMl (TAKE (n i) vs) (VAR (y i) @* args i)
           Abbrev (M1 = (\i. principal_hnf (M0 i @* MAP VAR vs)))
           M1 i = VAR (y i) @* args i @* DROP (n i) (MAP VAR vs)

           It seems that (y i) at most uses (TAKE (n i) vs).
         *)
          ‘y j1 IN Y UNION set vs1’ by rw [Abbr ‘vs1’] \\
           Suff ‘DISJOINT (Y UNION set vs1) (set vs1')’
           >- (REWRITE_TAC [DISJOINT_ALT] \\
               DISCH_THEN MATCH_MP_TAC >> art []) \\
           REWRITE_TAC [DISJOINT_UNION] \\
           reverse CONJ_TAC (* easy goal first *)
           >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs’ MP_TAC \\
               Q.PAT_X_ASSUM ‘vs1 ++ vs1' = vs’ (REWRITE_TAC o wrap o SYM) \\
               simp [ALL_DISTINCT_APPEND']) \\
           MATCH_MP_TAC DISJOINT_SUBSET \\
           Q.EXISTS_TAC ‘set vs’ >> simp [Once DISJOINT_SYM] \\
           simp [Abbr ‘vs1'’, LIST_TO_SET_DROP],
           (* goal 2 (of 2) *)
          ‘LENGTH vs2' = LENGTH ys2'’ by rw [Abbr ‘vs2'’, Abbr ‘ys2'’] \\
           Know ‘pm = pm2 ++ ZIP (vs2',ys2')’
           >- (simp [Abbr ‘pm’, Abbr ‘pm2’] \\
              ‘LENGTH vs2 = LENGTH ys2’ by rw [Abbr ‘vs2'’] \\
               simp [ZIP_APPEND]) >> Rewr' \\
           simp [lswapstr_append, Once EQ_SYM_EQ] \\
           MATCH_MP_TAC lswapstr_unchanged' >> simp [MAP_ZIP] \\
           reverse CONJ_TAC (* easy goal first *)
           >- (‘y j2 IN X UNION RANK r’ by METIS_TAC [SUBSET_DEF] \\
               Suff ‘DISJOINT (X UNION RANK r) (set ys2')’
               >- (REWRITE_TAC [DISJOINT_ALT] \\
                   DISCH_THEN MATCH_MP_TAC >> art []) \\
               MATCH_MP_TAC DISJOINT_SUBSET \\
               Q.EXISTS_TAC ‘set ys’ \\
               reverse CONJ_TAC >- simp [Abbr ‘ys2'’, LIST_TO_SET_DROP] \\
               simp [DISJOINT_UNION', Once DISJOINT_SYM] \\
               simp [Abbr ‘ys’, Once DISJOINT_SYM, DISJOINT_RNEWS_RANK]) \\
          ‘y j2 IN Y UNION set vs2’ by rw [Abbr ‘vs2’] \\
           Suff ‘DISJOINT (Y UNION set vs2) (set vs2')’
           >- (REWRITE_TAC [DISJOINT_ALT] \\
               DISCH_THEN MATCH_MP_TAC >> art []) \\
           REWRITE_TAC [DISJOINT_UNION] \\
           reverse CONJ_TAC (* easy goal first *)
           >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs’ MP_TAC \\
               Q.PAT_X_ASSUM ‘vs2 ++ vs2' = vs’ (REWRITE_TAC o wrap o SYM) \\
               simp [ALL_DISTINCT_APPEND']) \\
           MATCH_MP_TAC DISJOINT_SUBSET \\
           Q.EXISTS_TAC ‘set vs’ >> simp [Once DISJOINT_SYM] \\
           simp [Abbr ‘vs2'’, LIST_TO_SET_DROP] ]) \\
  (* stage work, instantiating the key substitution assumption with q <> [] *)
     Q.PAT_X_ASSUM ‘!q. q <<= p /\ q <> [] ==> _’ drule >> art [] \\
     DISCH_TAC \\
  (* NOTE: ‘solvable (subterm' X (M i) q r)’ only holds when ‘q <<= FRONT p’.
     The case that ‘unsolvable (subterm' X (M j1/j2) q r)’ (p = q) must be
     treated specially. In this case, ltree_el (BT' X (M i) r q = SOME bot.
   *)
     reverse (Cases_on ‘solvable (subterm' X (M j1) q r)’)
     >- (‘q <<= FRONT p \/ q = p’ by METIS_TAC [IS_PREFIX_FRONT_CASES]
         >- (‘solvable (subterm' X (M j1) q r)’ by METIS_TAC []) \\
         POP_ASSUM (fs o wrap) >> T_TAC \\
         Know ‘unsolvable (subterm' X (M j1) p r) <=>
               ltree_el (BT' X (M j1) r) p = SOME bot’
         >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> rw []) \\
         simp [] >> DISCH_THEN K_TAC \\
         DISCH_TAC \\
      (* applying ltree_equiv_bot_eq *)
         Know ‘ltree_el (BT' X (M j2) r) p = SOME bot’
         >- (MATCH_MP_TAC ltree_equiv_some_bot_imp >> simp []) \\
         Know ‘unsolvable (subterm' X (M j2) p r) <=>
               ltree_el (BT' X (M j2) r) p = SOME bot’
         >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> rw []) \\
         DISCH_THEN (REWRITE_TAC o wrap o SYM) \\
         DISCH_TAC (* unsolvable (subterm' X (M j2) p r) *) \\
         Know ‘unsolvable (subterm' X (H j1) p r) /\
               unsolvable (subterm' X (H j2) p r)’
         >- (ASM_SIMP_TAC std_ss [] \\
             CONJ_TAC (* 2 subgoals, same tactics *) \\
             MATCH_MP_TAC unsolvable_ISUB \\
             simp [solvable_tpm]) >> STRIP_TAC \\
         Know ‘unsolvable (subterm' X (H j1) p r) <=>
               ltree_el (BT' X (H j1) r) p = SOME bot’
         >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> simp []) \\
         simp [] >> DISCH_THEN K_TAC \\
         Know ‘unsolvable (subterm' X (H j2) p r) <=>
               ltree_el (BT' X (H j2) r) p = SOME bot’
         >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> simp []) \\
         simp []) \\
     reverse (Cases_on ‘solvable (subterm' X (M j2) q r)’)
     >- (‘q <<= FRONT p \/ q = p’ by METIS_TAC [IS_PREFIX_FRONT_CASES]
         >- (‘solvable (subterm' X (M j2) q r)’ by METIS_TAC []) \\
         POP_ASSUM (fs o wrap) >> T_TAC \\
         Know ‘unsolvable (subterm' X (M j2) p r) <=>
               ltree_el (BT' X (M j2) r) p = SOME bot’
         >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> rw []) >> simp [] \\
         NTAC 2 DISCH_TAC \\
         Know ‘ltree_el (BT' X (M j1) r) p = SOME bot’
         >- (MATCH_MP_TAC ltree_equiv_some_bot_imp' >> simp []) \\
      (* applying BT_subterm_thm *)
         MP_TAC (Q.SPECL [‘p’, ‘X’, ‘M (j1 :num)’, ‘r’] BT_subterm_thm) \\
         rw [] >> fs [] \\
         rename1 ‘(\(N,r). NONE) z = SOME T’ \\
         Cases_on ‘z’ >> FULL_SIMP_TAC std_ss []) \\
  (* stage work, now applying BT_subterm_thm on ‘M j1’ *)
     MP_TAC (Q.SPECL [‘q’, ‘X’, ‘M (j1 :num)’, ‘r’] BT_subterm_thm) \\
     simp [] >> STRIP_TAC (* this asserts ‘x’ *) \\
     NTAC 3 (Cases_on ‘x’ >> fs []) \\
     qabbrev_tac ‘r1 = r + LENGTH q’ \\
     rename1 ‘subterm X (M j1) q r = SOME (N,r1)’ \\
     qabbrev_tac ‘N0 = principal_hnf N’ \\
     qabbrev_tac ‘m1 = hnf_children_size N0’ \\
     rename1 ‘ltree_el (BT' X (M j1) r) q = SOME (SOME (vs1,y1),SOME m1)’ \\
     Q.PAT_X_ASSUM ‘_ = SOME (vs1,y1)’ K_TAC >> gs [] \\
     Q.PAT_X_ASSUM ‘_ = r1’      K_TAC \\
     Q.PAT_X_ASSUM ‘_ = SOME m1’ K_TAC \\
     qabbrev_tac ‘n1 = LAMl_size N0’ \\
  (* applying BT_subterm_thm again *)
     MP_TAC (Q.SPECL [‘q’, ‘X’, ‘M (j2 :num)’, ‘r’] BT_subterm_thm) \\
     simp [] >> STRIP_TAC (* this asserts ‘x’ *) \\
     NTAC 3 (Cases_on ‘x’ >> fs []) \\
     rename1 ‘subterm X (M j2) q r = SOME (N',r1)’ \\
     qabbrev_tac ‘N0' = principal_hnf N'’ \\
     qabbrev_tac ‘m2 = hnf_children_size N0'’ \\
     rename1 ‘ltree_el (BT' X (M j2) r) q = SOME (SOME (vs2,y2),SOME m2)’ \\
     Q.PAT_X_ASSUM ‘_ = SOME (vs2,y2)’ K_TAC >> gs [] \\
     Q.PAT_X_ASSUM ‘_ = r1’      K_TAC \\
     Q.PAT_X_ASSUM ‘_ = SOME m2’ K_TAC \\
     qabbrev_tac ‘n2 = LAMl_size N0'’ \\
     simp [head_equivalent_def] \\
  (* decompose N *)
     Q.PAT_X_ASSUM ‘RNEWS r1 n1 X = vs1’ (fs o wrap o SYM) \\
     Q_TAC (RNEWS_TAC (“vs1 :string list”, “r1 :num”, “n1 :num”)) ‘X’ \\
     qabbrev_tac ‘N1 = principal_hnf (N0 @* MAP VAR vs1)’ \\
     Q_TAC (HNF_TAC (“N0 :term”, “vs1 :string list”,
                     “y1' :string”, “Ns1 :term list”)) ‘N1’ \\
    ‘TAKE (LAMl_size N0) vs1 = vs1’ by rw [] \\
     POP_ASSUM (rfs o wrap) >> T_TAC \\
    ‘LENGTH Ns1 = m1 /\ hnf_headvar N1 = y1' /\ hnf_children N1 = Ns1’
       by rw [Abbr ‘m1’] \\
     Q.PAT_X_ASSUM ‘N0 = _’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘N1 = _’ (ASSUME_TAC o SYM) \\
  (* decompose N' *)
     Q.PAT_X_ASSUM ‘RNEWS r1 n2 X = vs2’ (fs o wrap o SYM) \\
     Q_TAC (RNEWS_TAC (“vs2 :string list”, “r1 :num”, “n2 :num”)) ‘X’ \\
     qabbrev_tac ‘N1' = principal_hnf (N0' @* MAP VAR vs2)’ \\
     Q_TAC (HNF_TAC (“N0' :term”, “vs2 :string list”,
                     “y2' :string”, “Ns2 :term list”)) ‘N1'’ \\
    ‘TAKE (LAMl_size N0') vs2 = vs2’ by rw [] \\
     POP_ASSUM (rfs o wrap) \\
    ‘LENGTH Ns2 = m2 /\ hnf_headvar N1' = y2' /\ hnf_children N1' = Ns2’
       by rw [Abbr ‘m2’] \\
     Q.PAT_X_ASSUM ‘N0' = _’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘N1' = _’ (ASSUME_TAC o SYM) \\
     DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [Once EQ_SYM_EQ]) >> gs [] \\
     Q.PAT_X_ASSUM ‘y2' = y1’ (fs o wrap) \\
     Q.PAT_X_ASSUM ‘y1' = y1’ (fs o wrap) \\
  (* stage work, preparing for BT_subterm_thm on ‘H j1’ and ‘H j2’*)
     Know ‘subterm X (H j1) q r <> NONE /\
           subterm X (H j2) q r <> NONE’
     >- ASM_SIMP_TAC std_ss [] >> STRIP_TAC \\
     Know ‘IMAGE y (count k) SUBSET X UNION RANK r1’
     >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘X UNION RANK r’ \\
         reverse CONJ_TAC
         >- (Suff ‘RANK r SUBSET RANK r1’ >- SET_TAC [] \\
             rw [RANK_MONO, Abbr ‘r1’]) \\
         rw [SUBSET_DEF] >> rename1 ‘i < k’ \\
         Know ‘y i IN Z’ >- rw [] \\
         Suff ‘Z SUBSET X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
         FIRST_X_ASSUM ACCEPT_TAC) >> DISCH_TAC \\
  (* some properties needed by the next "solvable" subgoal *)
     Know ‘set vs SUBSET X UNION RANK r1’
     >- (Suff ‘set vs SUBSET RANK r1’ >- SET_TAC [] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘RANK r’ >> art [] \\
         simp [Abbr ‘r1’, RANK_MONO]) >> DISCH_TAC \\
     Know ‘set ys SUBSET X UNION RANK r1’
     >- (Suff ‘set ys SUBSET RANK r1’ >- SET_TAC [] \\
         qunabbrev_tac ‘ys’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp [Abbr ‘r1’] \\
         rw [LENGTH_NON_NIL]) >> DISCH_TAC \\
     Know ‘FV (tpm (REVERSE pm) N)  SUBSET X UNION RANK r1 /\
           FV (tpm (REVERSE pm) N') SUBSET X UNION RANK r1’
     >- (CONJ_TAC \\
         MATCH_MP_TAC FV_tpm_lemma \\
         Q.EXISTS_TAC ‘r1’ >> simp [Abbr ‘pm’, MAP_REVERSE, MAP_ZIP]) \\
     STRIP_TAC \\
  (* applying subterm_width_last on N and N' (subterm X (M j) q r) *)
     Know ‘m1 <= d_max’ (* m1 = hnf_children_size N0 *)
     >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘d’ \\
         reverse CONJ_TAC >- rw [Abbr ‘d_max’] \\
         Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width (M j1) p’ \\
         reverse CONJ_TAC >- simp [] \\
         qunabbrevl_tac [‘m1’, ‘N0’] \\
        ‘N = subterm' X (M j1) q r’ by rw [] >> POP_ORW \\
         MATCH_MP_TAC subterm_width_last >> simp []) >> DISCH_TAC \\
     Know ‘m2 <= d_max’ (* m2 = hnf_children_size N0' *)
     >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘d’ \\
         reverse CONJ_TAC >- rw [Abbr ‘d_max’] \\
         Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width (M j2) p’ \\
         reverse CONJ_TAC >- simp [] \\
         qunabbrevl_tac [‘m2’, ‘N0'’] \\
        ‘N' = subterm' X (M j2) q r’ by rw [] >> POP_ORW \\
         MATCH_MP_TAC subterm_width_last >> simp []) >> DISCH_TAC \\
     Know ‘solvable (subterm' X (H j1) q r) /\
           solvable (subterm' X (H j2) q r)’
     >- (ASM_SIMP_TAC std_ss [] \\
         CONJ_TAC >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           MATCH_MP_TAC (cj 1 solvable_isub_permutator_alt) \\
           qexistsl_tac [‘X’, ‘r1’, ‘d_max’, ‘y’, ‘k’] \\
           simp [subterm_width_nil, principal_hnf_tpm'] \\
           rpt STRIP_TAC \\
           Know ‘y i IN X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
           Suff ‘RANK r SUBSET RANK r1’ >- SET_TAC [] \\
           simp [Abbr ‘r1’, RANK_MONO],
           (* goal 2 (of 2) *)
           MATCH_MP_TAC (cj 1 solvable_isub_permutator_alt) \\
           qexistsl_tac [‘X’, ‘r1’, ‘d_max’, ‘y’, ‘k’] \\
           simp [subterm_width_nil, principal_hnf_tpm'] \\
           rpt STRIP_TAC \\
           Know ‘y i IN X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
           Suff ‘RANK r SUBSET RANK r1’ >- SET_TAC [] \\
           simp [Abbr ‘r1’, RANK_MONO] ]) >> STRIP_TAC \\
  (* extra goal *)
     reverse CONJ_TAC
     >- (Suff ‘subterm X (apply pi (M j1)) q r = subterm X (H j1) q r’
         >- (Rewr >> art []) \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> principal_hnf (apply pi (M i)) = H i’
           (MP_TAC o Q.SPEC ‘j1’) >> art [] \\
         DISCH_THEN (ONCE_REWRITE_TAC o wrap o SYM) \\
         ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC subterm_of_principal_hnf >> simp []) \\
  (* stage work *)
     PRINT_TAC "stage work on subtree_equiv_lemma" \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> subterm X (H i) q r <> NONE /\ _’ ASSUME_TAC \\
  (* applying BT_subterm_thm on ‘H j1’ *)
     MP_TAC (Q.SPECL [‘q’, ‘X’, ‘H (j1 :num)’, ‘r’] BT_subterm_thm) \\
     simp [] >> STRIP_TAC (* this asserts ‘x’ *) \\
     NTAC 3 (Cases_on ‘x’ >> fs []) \\
     rename1 ‘subterm X (H j1) q r = SOME (W,r1)’ \\
     qabbrev_tac ‘W0 = principal_hnf W’ \\
     qabbrev_tac ‘m3 = hnf_children_size W0’ \\
     rename1 ‘ltree_el (BT' X (H j1) r) q = SOME (SOME (vs3,y3),SOME m3)’ \\
     Q.PAT_X_ASSUM ‘_ = SOME (vs3,y3)’ K_TAC \\
     Q.PAT_X_ASSUM ‘_ = SOME m3’       K_TAC \\
     qabbrev_tac ‘n3 = LAMl_size W0’ \\
     Q.PAT_X_ASSUM ‘_ = r1’ (fs o wrap) >> T_TAC \\
  (* applying BT_subterm_thm on ‘H j2’ *)
     MP_TAC (Q.SPECL [‘q’, ‘X’, ‘H (j2 :num)’, ‘r’] BT_subterm_thm) \\
     simp [] >> STRIP_TAC (* this asserts ‘x’ *) \\
     NTAC 3 (Cases_on ‘x’ >> fs []) \\
     rename1 ‘subterm X (H j2) q r = SOME (W',r1)’ \\
     qabbrev_tac ‘W0' = principal_hnf W'’ \\
     qabbrev_tac ‘m4 = hnf_children_size W0'’ \\
     rename1 ‘ltree_el (BT' X (H j2) r) q = SOME (SOME (vs4,y4),SOME m4)’ \\
     Q.PAT_X_ASSUM ‘_ = SOME (vs4,y4)’ K_TAC \\
     Q.PAT_X_ASSUM ‘_ = SOME m4’       K_TAC \\
     qabbrev_tac ‘n4 = LAMl_size W0'’ \\
     Q.PAT_X_ASSUM ‘_ = r1’ (fs o wrap) >> T_TAC \\
  (* decompose W *)
     Q.PAT_X_ASSUM ‘RNEWS r1 n3 X = vs3’ (fs o wrap o SYM) \\
     Q_TAC (RNEWS_TAC (“vs3 :string list”, “r1 :num”, “n3 :num”)) ‘X’ \\
     qabbrev_tac ‘W1 = principal_hnf (W0 @* MAP VAR vs3)’ \\
     Q_TAC (HNF_TAC (“W0 :term”, “vs3 :string list”,
                     “y3' :string”, “Ns3 :term list”)) ‘W1’ \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs3) (FV W0)’ K_TAC \\
  (* decompose W' *)
     Q.PAT_X_ASSUM ‘RNEWS r1 n4 X = vs4’ (fs o wrap o SYM) \\
     Q_TAC (RNEWS_TAC (“vs4 :string list”, “r1 :num”, “n4 :num”)) ‘X’ \\
     qabbrev_tac ‘W1' = principal_hnf (W0' @* MAP VAR vs4)’ \\
     Q_TAC (HNF_TAC (“W0' :term”, “vs4 :string list”,
                     “y4' :string”, “Ns4 :term list”)) ‘W1'’ \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs4) (FV W0')’ K_TAC \\
  (* stage work *)
     Know ‘TAKE (LAMl_size W0) vs3 = vs3 /\ TAKE (LAMl_size W0') vs4 = vs4’
     >- simp [] \\
     DISCH_THEN (rfs o CONJUNCTS) \\
     Q.PAT_X_ASSUM ‘hnf_headvar (principal_hnf (W0 @* MAP VAR vs3)) = y3’ MP_TAC \\
     simp [] (* y3' = y3 *) \\
     DISCH_THEN (rfs o wrap) \\
     Q.PAT_X_ASSUM ‘hnf_headvar (principal_hnf (W0' @* MAP VAR vs4)) = y4’ MP_TAC \\
     simp [] (* y4' = y4 *) \\
     DISCH_THEN (rfs o wrap) \\
  (* properties of W0 *)
    ‘LAMl_size W0 = n3 /\ hnf_children_size W0 = m3 /\ hnf_headvar W1 = y3’
       by rw [] \\
     Q.PAT_X_ASSUM ‘W0 = _’  (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘W1 = _’  (ASSUME_TAC o SYM) \\
  (* properties of W0' *)
    ‘LAMl_size W0' = n4 /\ hnf_children_size W0' = m4 /\ hnf_headvar W1' = y4’
       by rw [] \\
     Q.PAT_X_ASSUM ‘W0' = _’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘W1' = _’ (ASSUME_TAC o SYM) \\
  (* stage work *)
     Know ‘W = tpm (REVERSE pm) N ISUB ss’
     >- (Q.PAT_X_ASSUM  ‘!i. i < k ==> subterm X (H i) q r <> NONE /\ _’
           (MP_TAC o Q.SPEC ‘j1’) >> simp []) >> DISCH_TAC \\
     Know ‘W' = tpm (REVERSE pm) N' ISUB ss’
     >- (Q.PAT_X_ASSUM  ‘!i. i < k ==> subterm X (H i) q r <> NONE /\ _’
           (MP_TAC o Q.SPEC ‘j2’) >> simp []) >> DISCH_TAC \\
  (* applying hreduce_ISUB and tpm_hreduces *)
    ‘N -h->* N0 /\ N' -h->* N0'’ by METIS_TAC [principal_hnf_thm'] \\
     Know ‘W  -h->* tpm (REVERSE pm) N0  ISUB ss /\
           W' -h->* tpm (REVERSE pm) N0' ISUB ss’
     >- simp [hreduce_ISUB, tpm_hreduces] \\
     Q.PAT_X_ASSUM ‘LAMl vs1 _ = N0’ (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘LAMl vs2 _ = N0'’ (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = N1’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = N1'’ (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘W  = tpm (REVERSE pm) N  ISUB ss’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘W' = tpm (REVERSE pm) N' ISUB ss’ (ASSUME_TAC o SYM) \\
     simp [tpm_LAMl, tpm_appstar] \\
     qabbrev_tac ‘y1'  = lswapstr (REVERSE pm) y1’ \\
     qabbrev_tac ‘Ns1' = listpm term_pmact (REVERSE pm) Ns1’ \\
     qabbrev_tac ‘Ns2' = listpm term_pmact (REVERSE pm) Ns2’ \\
  (* pm = ZIP (vs,ys), where ys is in ROW r, vs is in ROW 0.
     vs1 is in ROW r1 = r + LENGTH q > r, as q <> [].
   *)
     Know ‘listpm string_pmact (REVERSE pm) vs1 = vs1’
     >- (simp [Once LIST_EQ_REWRITE] \\
         Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
         MATCH_MP_TAC lswapstr_unchanged' \\
         simp [Abbr ‘pm’, MAP_REVERSE, MAP_ZIP] \\
         CONJ_TAC >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           POP_ASSUM MP_TAC \\
           Suff ‘DISJOINT (set vs1) (set vs)’
           >- (rw [DISJOINT_ALT] \\
               FIRST_X_ASSUM MATCH_MP_TAC >> simp [EL_MEM]) \\
           MATCH_MP_TAC DISJOINT_SUBSET \\
           Q.EXISTS_TAC ‘set vs0’ >> art [] \\
           qunabbrevl_tac [‘vs1’, ‘vs0’] \\
           MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’],
           (* goal 2 (of 2) *)
           POP_ASSUM MP_TAC \\
           Suff ‘DISJOINT (set vs1) (set ys)’
           >- (rw [DISJOINT_ALT] \\
               FIRST_X_ASSUM MATCH_MP_TAC >> simp [EL_MEM]) \\
           qunabbrevl_tac [‘vs1’, ‘ys’] \\
           MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’] ]) >> Rewr' \\
     Know ‘listpm string_pmact (REVERSE pm) vs2 = vs2’
     >- (simp [Once LIST_EQ_REWRITE] \\
         Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
         MATCH_MP_TAC lswapstr_unchanged' \\
         simp [Abbr ‘pm’, MAP_REVERSE, MAP_ZIP] \\
         CONJ_TAC >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           POP_ASSUM MP_TAC \\
           Suff ‘DISJOINT (set vs2) (set vs)’
           >- (rw [DISJOINT_ALT] \\
               FIRST_X_ASSUM MATCH_MP_TAC >> simp [EL_MEM]) \\
           MATCH_MP_TAC DISJOINT_SUBSET \\
           Q.EXISTS_TAC ‘set vs0’ >> art [] \\
           qunabbrevl_tac [‘vs2’, ‘vs0’] \\
           MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’],
           (* goal 2 (of 2) *)
           POP_ASSUM MP_TAC \\
           Suff ‘DISJOINT (set vs2) (set ys)’
           >- (rw [DISJOINT_ALT] \\
               FIRST_X_ASSUM MATCH_MP_TAC >> simp [EL_MEM]) \\
           qunabbrevl_tac [‘vs2’, ‘ys’] \\
           MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’] ]) >> Rewr' \\
  (* NOTE: DOM ss = IMAGE y k, SUBSET Z, SUBSET X UNION RANK r *)
     Know ‘DISJOINT (set vs1) (DOM ss)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘X UNION RANK r’ \\
         reverse CONJ_TAC
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘Z’ >> simp [] \\
             rw [SUBSET_DEF] >> simp []) \\
         simp [DISJOINT_UNION', Abbr ‘vs1’] \\
         MATCH_MP_TAC DISJOINT_RNEWS_RANK >> simp [Abbr ‘r1’]) >> DISCH_TAC \\
     Know ‘DISJOINT (set vs2) (DOM ss)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘X UNION RANK r’ \\
         reverse CONJ_TAC
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘Z’ >> simp [] \\
             rw [SUBSET_DEF] >> simp []) \\
         simp [DISJOINT_UNION', Abbr ‘vs2’] \\
         MATCH_MP_TAC DISJOINT_RNEWS_RANK >> simp [Abbr ‘r1’]) >> DISCH_TAC \\
     simp [LAMl_ISUB, appstar_ISUB] \\
     qabbrev_tac ‘Ns1'' = MAP (\t. t ISUB ss) Ns1'’ \\
     qabbrev_tac ‘Ns2'' = MAP (\t. t ISUB ss) Ns2'’ \\
  (* easy case *)
     reverse (Cases_on ‘y1' IN DOM ss’)
     >- (simp [ISUB_VAR_FRESH'] >> STRIP_TAC \\
        ‘hnf (LAMl vs1 (VAR y1' @* Ns1'')) /\
         hnf (LAMl vs2 (VAR y1' @* Ns2''))’ by rw [hnf_appstar] \\
        ‘LAMl vs1 (VAR y1' @* Ns1'') = W0 /\
         LAMl vs2 (VAR y1' @* Ns2'') = W0'’ by METIS_TAC [principal_hnf_thm'] \\
        ‘LAMl_size W0 = n1 /\ LAMl_size W0' = n2’ by rw [LAMl_size_hnf] \\
        ‘n3 = n1 /\ n4 = n2’ by PROVE_TAC [] \\
         simp [head_equivalent_def] \\
         Know ‘y3 = y1' /\ y4 = y1' /\ Ns1'' = Ns3 /\ Ns2'' = Ns4’
         >- (Q.PAT_X_ASSUM ‘LAMl vs3 _ = W0’ MP_TAC \\
             Q.PAT_X_ASSUM ‘_ = W1’ (REWRITE_TAC o wrap o SYM) \\
             Q.PAT_X_ASSUM ‘_ = W0’ (REWRITE_TAC o wrap o SYM) \\
             Q.PAT_X_ASSUM ‘LAMl vs4 _ = W0'’ MP_TAC \\
             Q.PAT_X_ASSUM ‘_ = W1'’ (REWRITE_TAC o wrap o SYM) \\
             Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) \\
             NTAC 2 (POP_ASSUM (fs o wrap))) >> STRIP_TAC \\
         simp [Abbr ‘m3’, Abbr ‘m4’] \\
         NTAC 2 (POP_ASSUM (REWRITE_TAC o wrap o SYM)) \\
         Q.PAT_X_ASSUM ‘_ = W0’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) \\
         simp [Abbr ‘Ns1'’, Abbr ‘Ns2'’, Abbr ‘Ns1''’, Abbr ‘Ns2''’]) \\
  (* hard case *)
     PRINT_TAC "stage work on subtree_equiv_lemma" \\
     POP_ASSUM MP_TAC >> simp [] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘j3’ STRIP_ASSUME_TAC) \\
    ‘(LEAST j. y j = y1') = f j3’ by rw [] >> POP_ORW \\
  (* preparing for hreduce_permutator_shared *)
    ‘LENGTH Ns1'' = m1 /\ LENGTH Ns2'' = m2’
       by simp [Abbr ‘Ns1''’, Abbr ‘Ns2''’, Abbr ‘Ns1'’, Abbr ‘Ns2'’] \\
     qabbrev_tac ‘X' = BIGUNION (IMAGE FV (set Ns1'')) UNION
                       BIGUNION (IMAGE FV (set Ns2''))’ \\
    ‘FINITE X'’ by rw [Abbr ‘X'’] \\
  (* NOTE: Here the length of L must be big enough that ‘n3 <= LENGTH L’ can
     be proved later.

     It will be shown that SUC d_max + n1 - m1 = n3 = n4. Depending on the
     independent n1 and m1, either SUC d_max <= n3 or n3 <= SUC d_max.

     Thus ‘MAX n3 (SUC (d_max' j3))’ is the suitable length to be used here.
   *)
     qabbrev_tac ‘d' = MAX n3 (SUC (d_max' j3))’ \\
     Q_TAC (NEWS_TAC (“L :string list”, “d' :num”)) ‘X'’ \\
    ‘d_max' j3 < LENGTH L /\ n3 <= LENGTH L’ by simp [Abbr ‘d'’, MAX_LE] \\
     Know ‘DISJOINT (set L) (set vs1) /\
           DISJOINT (set L) (set vs2) /\
           DISJOINT (set L) (set vs3) /\
           DISJOINT (set L) (set vs4)’
     >- (rw [Abbr ‘L’, Abbr ‘vs1’, Abbr ‘vs2’, Abbr ‘vs3’, Abbr ‘vs4’] \\
         MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’]) >> STRIP_TAC \\
     Q.PAT_X_ASSUM ‘FINITE X'’ K_TAC \\
     Q.PAT_X_ASSUM ‘DISJOINT (set L) X'’ MP_TAC \\
     qunabbrev_tac ‘X'’ \\
     DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [DISJOINT_UNION']) \\
     STRIP_TAC (* W -h->* ... /\ W' -h->* ... *) \\
    ‘m1 <= d_max' j3 /\ m2 <= d_max' j3’ by simp [Abbr ‘d_max'’] \\
  (* applying hreduce_permutator_shared *)
     MP_TAC (Q.SPECL [‘Ns1''’, ‘d_max + f (j3 :num)’, ‘L’]
                     hreduce_permutator_shared) >> simp [] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘zs1’ (Q.X_CHOOSE_THEN ‘z1’ STRIP_ASSUME_TAC)) \\
  (* applying hreduce_permutator_shared again *)
     MP_TAC (Q.SPECL [‘Ns2''’, ‘d_max + f (j3 :num)’, ‘L’]
                     hreduce_permutator_shared) >> simp [] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘zs2’ (Q.X_CHOOSE_THEN ‘z2’ STRIP_ASSUME_TAC)) \\
     qabbrev_tac ‘P' = P (f j3)’ \\
     Q.PAT_X_ASSUM ‘P' @* Ns1'' -h->* _’ MP_TAC \\
     Q.PAT_X_ASSUM ‘P' @* Ns2'' -h->* _’ MP_TAC \\
     qabbrev_tac ‘h = LAST L’ (* new shared head variable *) \\
     qabbrev_tac ‘L' = FRONT L’ \\
    ‘L <> []’ by rw [GSYM LENGTH_NON_NIL] \\
     NTAC 2 (Q.PAT_X_ASSUM ‘IS_SUFFIX L _’ MP_TAC) \\
    ‘L = SNOC h L'’ by ASM_SIMP_TAC std_ss [Abbr ‘L'’, Abbr ‘h’, SNOC_LAST_FRONT] \\
     POP_ORW \\
     simp [IS_SUFFIX] >> NTAC 2 STRIP_TAC \\
     Q.PAT_X_ASSUM ‘z1 = z2’ (simp o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘h  = z1’ (simp o wrap o SYM) \\
     NTAC 2 STRIP_TAC \\
     qabbrev_tac ‘xs1 = SNOC h zs1’ \\ (* suffix of L *)
     qabbrev_tac ‘xs2 = SNOC h zs2’ \\ (* suffix of L *)
     Know ‘IS_SUFFIX L xs1 /\ IS_SUFFIX L xs2’
     >- (‘L = SNOC h L'’
           by ASM_SIMP_TAC std_ss [Abbr ‘L'’, Abbr ‘h’, SNOC_LAST_FRONT] \\
         POP_ORW \\
         simp [IS_SUFFIX, Abbr ‘xs1’, Abbr ‘xs2’]) >> STRIP_TAC \\
     Know ‘LAMl vs1 (P' @* Ns1'') -h->*
           LAMl vs1 (LAMl zs1 (LAM h (VAR h @* Ns1'' @* MAP VAR zs1))) /\
           LAMl vs2 (P' @* Ns2'') -h->*
           LAMl vs2 (LAMl zs2 (LAM h (VAR h @* Ns2'' @* MAP VAR zs2)))’
     >- simp [hreduce_LAMl] \\
     Q.PAT_X_ASSUM ‘P' @* Ns1'' -h->* _’ K_TAC \\
     Q.PAT_X_ASSUM ‘P' @* Ns2'' -h->* _’ K_TAC \\
     REWRITE_TAC [GSYM LAMl_APPEND, GSYM appstar_APPEND] \\
     qabbrev_tac ‘Ns1x = Ns1'' ++ MAP VAR zs1’ \\
     qabbrev_tac ‘Ns2x = Ns2'' ++ MAP VAR zs2’ \\
     REWRITE_TAC [GSYM LAMl_SNOC] \\
     qabbrev_tac ‘zs1' = SNOC h (vs1 ++ zs1)’ \\
     qabbrev_tac ‘zs2' = SNOC h (vs2 ++ zs2)’ \\
     STRIP_TAC \\
     Know ‘W  -h->* LAMl zs1' (VAR h @* Ns1x) /\
           W' -h->* LAMl zs2' (VAR h @* Ns2x)’
     >- PROVE_TAC [hreduce_TRANS] \\
     NTAC 2 (POP_ASSUM K_TAC) >> STRIP_TAC \\
     Know ‘LAMl zs1' (VAR h @* Ns1x) = W0 /\
           LAMl zs2' (VAR h @* Ns2x) = W0'’
     >- (‘hnf (LAMl zs1' (VAR h @* Ns1x)) /\ hnf (LAMl zs2' (VAR h @* Ns2x))’
            by rw [hnf_appstar] \\
         METIS_TAC [principal_hnf_thm']) >> STRIP_TAC \\
     Know ‘LENGTH zs1' = n3 /\ LENGTH zs2' = n4’
     >- (Q.PAT_X_ASSUM ‘_ = n3’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = n4’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0’  (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) \\
         simp []) >> STRIP_TAC \\
  (* n3 = LENGTH zs1' = 1 + LENGTH (vs1 ++ zs1) = 1 + d_max + n1 - m1 *)
     Know ‘SUC (d_max' j3) + n1 - m1 = n3 /\
           SUC (d_max' j3) + n2 - m2 = n4’
     >- (Q.PAT_X_ASSUM ‘_ = n3’  (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = n4’  (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0’  (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) \\
         simp [Abbr ‘zs1'’, Abbr ‘zs2'’]) >> STRIP_TAC \\
     Know ‘n4 = n3’
     >- (NTAC 2 (POP_ASSUM (REWRITE_TAC o wrap o SYM)) \\
         simp []) >> DISCH_TAC \\
    ‘vs4 = vs3’ by simp [Abbr ‘vs4’, Abbr ‘vs3’] \\
     simp [head_equivalent_def] \\
     Know ‘m4 = m3’
     >- (Q.PAT_X_ASSUM ‘hnf_children_size W0  = m3’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘hnf_children_size W0' = m4’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0’  (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) \\
         simp [Abbr ‘Ns1x’, Abbr ‘Ns2x’]) >> DISCH_TAC \\
     simp [] (* it remains to prove ‘y3 = y4’ *) \\
  (* NOTE: Now we know:

     1. LAMl zs1' (VAR h @* Ns1x) = W0
     2. LAMl zs2' (VAR h @* Ns2x) = W0'
     3. principal_hnf (W0  @* MAP VAR vs3) = VAR y3 @* Ns3 (= W1 )
     4. principal_hnf (W0' @* MAP VAR vs4) = VAR y4 @* Ns4 (= W1')

     Thus y3 and y4 are the same permutation of h, thus is the same. To
     actually prove it, we can use [principal_hnf_tpm_reduce'], which requires
    ‘DISJOINT (set vs3) (FV (VAR z2 @* Ns1x))’, which is explained below:

     We know that vs3 (vs4) is in ROW r1 (r + LENGTH q), on the other hand,

     - zs2 (part of Ns1x), prefix of L, can be chosen to exclude anything;
     - z2, part of L, can be chosen to exclude anything;
     - Ns1'' (part of Ns1x), FV is equal or less than Ns1';
     - Ns1' is tpm (REVERSE pm) of Ns1;
     - pm = ZIP (vs,ys), vs is in ROW 0, ys s in ROW r;

     - FV (Ns1) <= FV (VAR y1 @* Ns1) <= FV (N0 @* MAP VAR vs1)
                <= FV N + vs1 <= X UNION RANK r1 + vs1 (in ROW r1)

     - vs1     = RNEWS r1 n1 X (NOTE: n1 <> n2)
     - vs2     = RNEWS r1 n2 X
     - vs3/vs4 = RNEWS r1 n3/n4 X

                      ----- L -------------->| (LENGTH = SUC d_max)
     zs1' = |<--- vs1 --->|<--- zs1 ------>|h| (ROW 0 & r1)
     vs3  = |<---(vs1)--- vs3 ----(xs1)----->| (ROW r1)
             (n3 = 1 + d_max + n1 - m1 > n1)

                      ----- L -------------->| (LENGTH = SUC d_max)
     zs2' = |<--- vs2 ------>|<-- zs2 ---->|h| (ROW 0 & r1)
     vs3  = |<---(vs2)----- vs4 ---(xs2)---->| (ROW r1)
             (n4 = 1 + d_max + n2 - m2 > n2)

     now applying RNEWS_prefix first:
   *)
     PRINT_TAC "stage work on subtree_equiv_lemma" \\
     Know ‘vs1 <<= vs3’
     >- (qunabbrevl_tac [‘vs1’, ‘vs3’] \\
         MATCH_MP_TAC RNEWS_prefix >> simp []) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n1'’ STRIP_ASSUME_TAC) \\
    ‘n1' = n1’ by rw [] \\
     Q.PAT_X_ASSUM ‘n1' <= n3’ MP_TAC \\
     Q.PAT_X_ASSUM ‘vs1 = TAKE n1' vs3’ (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
     POP_ORW >> rpt STRIP_TAC \\
     Know ‘vs2 <<= vs3’
     >- (qunabbrevl_tac [‘vs2’, ‘vs3’] \\
         MATCH_MP_TAC RNEWS_prefix >> simp []) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n2'’ STRIP_ASSUME_TAC) \\
    ‘n2' = n2’ by rw [] \\
     Q.PAT_X_ASSUM ‘n2' <= n3’ MP_TAC \\
     Q.PAT_X_ASSUM ‘vs2 = TAKE n2' vs3’ (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
     POP_ORW >> rpt STRIP_TAC \\
    ‘zs1' = vs1 ++ xs1’ by simp [Abbr ‘zs1'’, Abbr ‘xs1’] \\
    ‘zs2' = vs2 ++ xs2’ by simp [Abbr ‘zs2'’, Abbr ‘xs2’] \\
     qabbrev_tac ‘ys1 = DROP n1 vs3’ \\
     qabbrev_tac ‘ys2 = DROP n2 vs3’ \\
  (* NOTE: xs1 is part of L, which excludes vs3 which drops to ys1 *)
     Know ‘DISJOINT (set xs1) (set ys1)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ \\
         reverse CONJ_TAC >- simp [LIST_TO_SET_DROP, Abbr ‘ys1’] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set L’ >> art [] \\
         MATCH_MP_TAC LIST_TO_SET_SUFFIX >> art []) >> DISCH_TAC \\
     Know ‘DISJOINT (set xs2) (set ys2)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ \\
         reverse CONJ_TAC >- simp [LIST_TO_SET_DROP, Abbr ‘ys2’] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set L’ >> art [] \\
         MATCH_MP_TAC LIST_TO_SET_SUFFIX >> art []) >> DISCH_TAC \\
    ‘LENGTH xs1 = LENGTH ys1 /\ LENGTH xs2 = LENGTH ys2’
       by simp [Abbr ‘xs1’, Abbr ‘ys1’, Abbr ‘xs2’, Abbr ‘ys2’] \\
    ‘vs1 ++ ys1 = vs3 /\ vs2 ++ ys2 = vs3’ by METIS_TAC [TAKE_DROP] \\
  (* applying hreduce_BETA_extended:
     W0 @* MAP VAR vs3
     = LAMl zs1' (VAR h @* Ns1x) @* MAP VAR vs3
     = LAMl (vs1 ++ xs1) (VAR h @* Ns1x) @* MAP VAR (vs1 ++ ys1)
     = LAMl vs1 (LAMl xs1 (VAR h @* Ns1x)) @* MAP VAR vs1 @* MAP VAR ys1
          -h->* (LAMl xs1 (VAR h @* Ns1x)) @* MAP VAR ys1
   *)
     Know ‘W0 @* MAP VAR vs3 -h->* LAMl xs1 (VAR h @* Ns1x) @* MAP VAR ys1’
     >- (Q.PAT_X_ASSUM ‘_ = W0’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘zs1' = vs1 ++ xs1’ (REWRITE_TAC o wrap) \\
         Q.PAT_X_ASSUM ‘vs1 ++ ys1 = vs3’ (REWRITE_TAC o wrap o SYM) \\
         REWRITE_TAC [LAMl_APPEND, MAP_APPEND, appstar_APPEND] \\
         REWRITE_TAC [hreduce_BETA_extended]) >> DISCH_TAC \\
     Know ‘W0' @* MAP VAR vs3 -h->* LAMl xs2 (VAR h @* Ns2x) @* MAP VAR ys2’
     >- (Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘zs2' = vs2 ++ xs2’ (REWRITE_TAC o wrap) \\
         Q.PAT_X_ASSUM ‘vs2 ++ ys2 = vs3’ (REWRITE_TAC o wrap o SYM) \\
         REWRITE_TAC [LAMl_APPEND, MAP_APPEND, appstar_APPEND] \\
         REWRITE_TAC [hreduce_BETA_extended]) >> DISCH_TAC \\
  (* NOTE: The following disjointness hold for names from different rows *)
     Know ‘DISJOINT (set vs) (set ys1) /\
           DISJOINT (set vs) (set ys2)’
     >- (CONJ_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ \\
         simp [Abbr ‘ys1’, Abbr ‘ys2’, LIST_TO_SET_DROP] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs0’ >> art [] \\
         qunabbrevl_tac [‘vs0’, ‘vs3’] \\
         MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’]) >> STRIP_TAC \\
     Know ‘DISJOINT (set ys) (set ys1) /\
           DISJOINT (set ys) (set ys2)’
     >- (CONJ_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ \\
         simp [Abbr ‘ys1’, Abbr ‘ys2’, LIST_TO_SET_DROP] \\
         qunabbrevl_tac [‘ys’, ‘vs3’] \\
         MATCH_MP_TAC DISJOINT_RNEWS \\
        ‘0 < LENGTH q’ by rw [LENGTH_NON_NIL] \\
         simp [Abbr ‘r1’]) >> STRIP_TAC \\
  (* NOTE: xs1 is part of L, ys1 is part of vs3 *)
     Know ‘DISJOINT (set xs1) (set ys1)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ \\
         reverse CONJ_TAC >- simp [Abbr ‘ys1’, LIST_TO_SET_DROP] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set L’ >> art [] \\
         MATCH_MP_TAC LIST_TO_SET_SUFFIX >> art []) >> DISCH_TAC \\
     Know ‘DISJOINT (set xs2) (set ys2)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ \\
         reverse CONJ_TAC >- simp [Abbr ‘ys2’, LIST_TO_SET_DROP] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set L’ >> art [] \\
         MATCH_MP_TAC LIST_TO_SET_SUFFIX >> art []) >> DISCH_TAC \\
    ‘ALL_DISTINCT xs1 /\ ALL_DISTINCT xs2’ by METIS_TAC [IS_SUFFIX_ALL_DISTINCT] \\
    ‘ALL_DISTINCT ys1 /\ ALL_DISTINCT ys2’ by METIS_TAC [ALL_DISTINCT_DROP] \\
  (* applying hreduce_tpm_reduce *)
     Know ‘LAMl xs1 (VAR h @* Ns1x) @* MAP VAR ys1 -h->*
           tpm (ZIP (xs1,ys1)) (VAR h @* Ns1x)’
     >- (MATCH_MP_TAC hreduce_tpm_reduce \\
         simp [hnf_appstar, Abbr ‘Ns1x’] \\
         Know ‘FV (VAR h @* (Ns1'' ++ MAP VAR zs1)) =
               set xs1 UNION BIGUNION (IMAGE FV (set Ns1''))’
         >- (simp [appstar_APPEND, FV_appstar_MAP_VAR] \\
             simp [FV_appstar, Abbr ‘xs1’, LIST_TO_SET_SNOC] \\
             SET_TAC []) >> Rewr' \\
         simp [Once DISJOINT_SYM, DISJOINT_UNION'] \\
         simp [MEM_EL] >> rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘_ = FV x’ (REWRITE_TAC o wrap) >> POP_ORW \\
         rename1 ‘i < m1’ >> POP_ASSUM MP_TAC \\
         simp [Abbr ‘Ns1''’, EL_MAP] >> DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV (EL i Ns1')’ \\
         reverse CONJ_TAC
         >- (MP_TAC (Q.SPECL [‘ss’, ‘EL i Ns1'’] FV_ISUB_upperbound) \\
             simp [EL_MAP, Abbr ‘Ns1'’]) \\
      (* The key is to prove DISJOINT (set vsx) (FV (EL i Ns1)) *)
         POP_ASSUM MP_TAC \\
         simp [Abbr ‘Ns1'’, EL_listpm, Abbr ‘pm’, REVERSE_ZIP] >> DISCH_TAC \\
      (* applying FV_tpm_disjoint *)
         MATCH_MP_TAC FV_tpm_disjoint \\
         simp [ALL_DISTINCT_REVERSE] \\
      (* goal: DISJOINT (set ys1) (FV (EL i Ns1)) *)
         Know ‘FV N0 SUBSET X UNION RANK r1’
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV N’ >> art [] \\
             qunabbrev_tac ‘N0’ \\
             MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) >> DISCH_TAC \\
      (* applying FV_subterm_lemma *)
         Know ‘FV (EL i Ns1) SUBSET FV N UNION set vs1’
         >- (MATCH_MP_TAC FV_subterm_lemma \\
             qexistsl_tac [‘X’, ‘r1’, ‘N0’, ‘n1’, ‘m1’, ‘N1’] >> simp []) \\
         DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV N UNION set vs1’ >> art [] \\
         REWRITE_TAC [DISJOINT_UNION'] \\
         reverse CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs3’ MP_TAC \\
             Q.PAT_X_ASSUM ‘vs1 ++ ys1 = vs3’ (REWRITE_TAC o wrap o SYM) \\
             simp [ALL_DISTINCT_APPEND, DISJOINT_ALT']) \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘X UNION RANK r1’ >> art [] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs3’ \\
         reverse CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘vs1 ++ ys1 = vs3’ (REWRITE_TAC o wrap o SYM) \\
             simp [SUBSET_DEF]) \\
         simp [DISJOINT_UNION'] \\
         qunabbrev_tac ‘vs3’ \\
         MATCH_MP_TAC DISJOINT_RNEWS_RANK' >> art []) >> DISCH_TAC \\
  (* applying hreduce_tpm_reduce again, proof is symmetric with the above *)
     Know ‘LAMl xs2 (VAR h @* Ns2x) @* MAP VAR ys2 -h->*
           tpm (ZIP (xs2,ys2)) (VAR h @* Ns2x)’
     >- (MATCH_MP_TAC hreduce_tpm_reduce \\
         simp [hnf_appstar, Abbr ‘Ns2x’] \\
         Know ‘FV (VAR h @* (Ns2'' ++ MAP VAR zs2)) =
               set xs2 UNION BIGUNION (IMAGE FV (set Ns2''))’
         >- (simp [appstar_APPEND, FV_appstar_MAP_VAR] \\
             simp [FV_appstar, Abbr ‘xs2’, LIST_TO_SET_SNOC] \\
             SET_TAC []) >> Rewr' \\
         simp [Once DISJOINT_SYM, DISJOINT_UNION'] \\
         simp [MEM_EL] >> rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘_ = FV x’ (REWRITE_TAC o wrap) >> POP_ORW \\
         rename1 ‘i < m2’ >> POP_ASSUM MP_TAC \\
         simp [Abbr ‘Ns2''’, EL_MAP] >> DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV (EL i Ns2')’ \\
         reverse CONJ_TAC
         >- (MP_TAC (Q.SPECL [‘ss’, ‘EL i Ns2'’] FV_ISUB_upperbound) \\
             simp [EL_MAP, Abbr ‘Ns2'’]) \\
         POP_ASSUM MP_TAC \\
         simp [Abbr ‘Ns2'’, EL_listpm, Abbr ‘pm’, REVERSE_ZIP] >> DISCH_TAC \\
      (* applying FV_tpm_disjoint *)
         MATCH_MP_TAC FV_tpm_disjoint \\
         simp [ALL_DISTINCT_REVERSE] \\
      (* goal: DISJOINT (set ys2) (FV (EL i Ns2)) *)
         Know ‘FV N0' SUBSET X UNION RANK r1’
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV N'’ >> art [] \\
             qunabbrev_tac ‘N0'’ \\
             MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) >> DISCH_TAC \\
      (* applying FV_subterm_lemma *)
         Know ‘FV (EL i Ns2) SUBSET FV N' UNION set vs2’
         >- (MATCH_MP_TAC FV_subterm_lemma \\
             qexistsl_tac [‘X’, ‘r1’, ‘N0'’, ‘n2’, ‘m2’, ‘N1'’] >> simp []) \\
         DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV N' UNION set vs2’ >> art [] \\
         REWRITE_TAC [DISJOINT_UNION'] \\
         reverse CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs3’ MP_TAC \\
             Q.PAT_X_ASSUM ‘vs2 ++ ys2 = vs3’ (REWRITE_TAC o wrap o SYM) \\
             simp [ALL_DISTINCT_APPEND, DISJOINT_ALT']) \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘X UNION RANK r1’ >> art [] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs3’ \\
         reverse CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘vs2 ++ ys2 = vs3’ (REWRITE_TAC o wrap o SYM) \\
             simp [SUBSET_DEF]) \\
         simp [DISJOINT_UNION'] \\
         qunabbrev_tac ‘vs3’ \\
         MATCH_MP_TAC DISJOINT_RNEWS_RANK' >> art []) >> DISCH_TAC \\
  (* stage work *)
     qabbrev_tac ‘pm1 = ZIP (xs1,ys1)’ \\
     qabbrev_tac ‘pm2 = ZIP (xs2,ys2)’ \\
    ‘W0  @* MAP VAR vs3 -h->* tpm pm1 (VAR h @* Ns1x) /\
     W0' @* MAP VAR vs3 -h->* tpm pm2 (VAR h @* Ns2x)’
       by PROVE_TAC [hreduce_TRANS] \\
     Q.PAT_X_ASSUM ‘_ -h->* LAMl xs1 (VAR h @* Ns1x) @* MAP VAR ys1’ K_TAC \\
     Q.PAT_X_ASSUM ‘_ -h->* LAMl xs2 (VAR h @* Ns2x) @* MAP VAR ys2’ K_TAC \\
     Q.PAT_X_ASSUM ‘LAMl xs1 (VAR h @* Ns1x) @* MAP VAR ys1 -h->* _’ K_TAC \\
     Q.PAT_X_ASSUM ‘LAMl xs2 (VAR h @* Ns2x) @* MAP VAR ys2 -h->* _’ K_TAC \\
  (* applying hreduces_hnf_imp_principal_hnf *)
     Know ‘W1  = tpm pm1 (VAR h @* Ns1x) /\
           W1' = tpm pm2 (VAR h @* Ns2x)’
     >- (simp [Abbr ‘W1’, Abbr ‘W1'’] \\
         CONJ_TAC (* 2 subgoals, same tactics *) \\
         MATCH_MP_TAC hreduces_hnf_imp_principal_hnf \\
         simp [hnf_appstar]) \\
     Q.PAT_X_ASSUM ‘_ = W1 ’ (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = W1'’ (REWRITE_TAC o wrap o SYM) \\
     simp [tpm_appstar] \\
     Suff ‘lswapstr pm1 h = lswapstr pm2 h’ >- simp [] \\
  (* NOTE: Now finding a common replacement for pm1 and pm2:

     |<--L--|<------------ ls -------------->|
     zs1' = |<--- xs1'--->|<--- zs1 ------>|h| (ROW 0)
                          |<------ xs1 ----->| (ROW r1)
     vs3  = |<---(vs1)--->|<------(ys1)----->| (ROW r1)
                                   pm1 = ZIP (xs1,ys1)
     |<--L--|<------------ ls -------------->|
     zs2' = |<--- xs2'------>|<-- zs2 ---->|h| (ROW 0)
                             |<--- xs2 ----->| (ROW r1)
     vs3  = |<---(vs2)------>|<---(ys2)----->| (ROW r1)
                                   pm2 = ZIP (xs2,ys2)
   *)
     qabbrev_tac ‘ls = LASTN n3 L’ \\
    ‘LENGTH ls = n3’ by simp [LENGTH_LASTN, Abbr ‘ls’] \\
     Know ‘set ls SUBSET set L’
     >- (SIMP_TAC list_ss [Abbr ‘ls’, SUBSET_DEF] \\
         REWRITE_TAC [MEM_LASTN]) >> DISCH_TAC \\
     qabbrev_tac ‘pm3 = ZIP (ls,vs3)’ \\
  (* applying IS_SUFFIX_IMP_LASTN *)
     Know ‘DROP n1 ls = xs1 /\ DROP n2 ls = xs2’
     >- (PRINT_TAC "stage work on subtree_equiv_lemma" \\
        ‘xs1 = LASTN (LENGTH xs1) L’ by simp [IS_SUFFIX_IMP_LASTN] \\
         POP_ORW \\
        ‘xs2 = LASTN (LENGTH xs2) L’ by simp [IS_SUFFIX_IMP_LASTN] \\
         POP_ORW \\
         MP_TAC (ISPECL [“n1 :num”, “ls :string list”] DROP_LASTN) \\
         MP_TAC (ISPECL [“n2 :num”, “ls :string list”] DROP_LASTN) \\
         simp [Abbr ‘ls’, LENGTH_LASTN] \\
         NTAC 2 (DISCH_THEN K_TAC) \\
         Know ‘LASTN (n3 - n1) (LASTN n3 L) = LASTN (n3 - n1) L’
         >- (irule LASTN_LASTN >> simp []) >> Rewr' \\
         Know ‘LASTN (n3 - n2) (LASTN n3 L) = LASTN (n3 - n2) L’
         >- (irule LASTN_LASTN >> simp []) >> Rewr' \\
         Suff ‘LENGTH ys1 = n3 - n1 /\ LENGTH ys2 = n3 - n2’ >- Rewr \\
         simp [Abbr ‘ys1’, Abbr ‘ys2’, LENGTH_DROP]) >> STRIP_TAC \\
     PRINT_TAC "stage work on subtree_equiv_lemma" \\
  (* preparing for lswapstr_unchanged' *)
     qabbrev_tac ‘xs1' = TAKE n1 ls’ \\
     qabbrev_tac ‘xs2' = TAKE n2 ls’ \\
     Know ‘xs1' ++ xs1 = ls /\ xs2' ++ xs2 = ls’
     >- (Q.PAT_X_ASSUM ‘_ = xs1’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = xs2’ (REWRITE_TAC o wrap o SYM) \\
         simp [TAKE_DROP, Abbr ‘xs1'’, Abbr ‘xs2'’]) >> STRIP_TAC \\
    ‘LENGTH xs1' = n1 /\ LENGTH xs2' = n2’
       by simp [LENGTH_TAKE, Abbr ‘xs1'’, Abbr ‘xs2'’] \\
     Know ‘ZIP (xs1',vs1) ++ pm1 = pm3’
     >- (qunabbrevl_tac [‘pm1’, ‘pm2’, ‘pm3’] \\
         Q.PAT_X_ASSUM ‘xs1' ++ xs1 = ls’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘vs1 ++ ys1 = vs3’ (REWRITE_TAC o wrap o SYM) \\
         MATCH_MP_TAC ZIP_APPEND >> art []) >> DISCH_TAC \\
     Know ‘ZIP (xs2',vs2) ++ pm2 = pm3’
     >- (qunabbrevl_tac [‘pm1’, ‘pm2’, ‘pm3’] \\
         Q.PAT_X_ASSUM ‘xs2' ++ xs2 = ls’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘vs2 ++ ys2 = vs3’ (REWRITE_TAC o wrap o SYM) \\
         MATCH_MP_TAC ZIP_APPEND >> art []) >> DISCH_TAC \\
  (* applying lswapstr_append *)
     Know ‘lswapstr (ZIP (xs1',vs1) ++ pm1) h =
           lswapstr (ZIP (xs2',vs2) ++ pm2) h’ >- rw [] \\
     REWRITE_TAC [lswapstr_append] \\
     qabbrev_tac ‘t1 = lswapstr pm1 h’ \\
     qabbrev_tac ‘t2 = lswapstr pm2 h’ \\
     Suff ‘lswapstr (ZIP (xs1',vs1)) t1 = t1 /\
           lswapstr (ZIP (xs2',vs2)) t2 = t2’ >- Rewr \\
  (* NOTE: The key is to get a upper bound for t1 and t2.

     |<--L--|<------------ ls -------------->|
            |<--- xs1'--->|<--- zs1 ------>|h| (ROW 0)
                          |<------ xs1 ----->| (ROW r1)
     vs3  = |<---(vs1)--->|<------(ys1)----->| (ROW r1)
                                   pm1 = ZIP (xs1,ys1)
     |<--L--|<------------ ls -------------->|
            |<--- xs2'------>|<-- zs2 ---->|h| (ROW 0)
                             |<--- xs2 ----->| (ROW r1)
     vs3  = |<---(vs2)------>|<---(ys2)----->| (ROW r1)
                                   pm2 = ZIP (xs2,ys2)
   *)
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC lswapstr_unchanged' >> simp [MAP_ZIP] \\
       Know ‘t1 IN set ys1’
       >- (qunabbrevl_tac [‘t1’, ‘pm1’] \\
           MATCH_MP_TAC MEM_lswapstr >> art [] \\
           simp [Abbr ‘xs1’, LIST_TO_SET_SNOC]) \\
       Suff ‘DISJOINT (set ys1) (set xs1') /\
             DISJOINT (set ys1) (set vs1)’ >- rw [DISJOINT_ALT] \\
       reverse CONJ_TAC
       >- (ONCE_REWRITE_TAC [DISJOINT_SYM] \\
           Know ‘ALL_DISTINCT (vs1 ++ ys1)’ >- art [] \\
           SIMP_TAC bool_ss [ALL_DISTINCT_APPEND']) \\
       MATCH_MP_TAC DISJOINT_SUBSET' >> Q.EXISTS_TAC ‘set vs3’ \\
       reverse CONJ_TAC >- simp [Abbr ‘ys1’, LIST_TO_SET_DROP] \\
       MATCH_MP_TAC DISJOINT_SUBSET >> Q.EXISTS_TAC ‘set ls’ \\
       reverse CONJ_TAC >- simp [Abbr ‘xs1'’, LIST_TO_SET_TAKE] \\
       ONCE_REWRITE_TAC [DISJOINT_SYM] \\
       MATCH_MP_TAC DISJOINT_SUBSET' \\
       Q.EXISTS_TAC ‘set L’ >> art [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC lswapstr_unchanged' >> simp [MAP_ZIP] \\
       Know ‘t2 IN set ys2’
       >- (qunabbrevl_tac [‘t2’, ‘pm2’] \\
           MATCH_MP_TAC MEM_lswapstr >> art [] \\
           simp [Abbr ‘xs2’, LIST_TO_SET_SNOC]) \\
       Suff ‘DISJOINT (set ys2) (set xs2') /\
             DISJOINT (set ys2) (set vs2)’ >- rw [DISJOINT_ALT] \\
       reverse CONJ_TAC
       >- (ONCE_REWRITE_TAC [DISJOINT_SYM] \\
           Know ‘ALL_DISTINCT (vs2 ++ ys2)’ >- art [] \\
           SIMP_TAC bool_ss [ALL_DISTINCT_APPEND']) \\
       MATCH_MP_TAC DISJOINT_SUBSET' >> Q.EXISTS_TAC ‘set vs3’ \\
       reverse CONJ_TAC >- simp [Abbr ‘ys2’, LIST_TO_SET_DROP] \\
       MATCH_MP_TAC DISJOINT_SUBSET >> Q.EXISTS_TAC ‘set ls’ \\
       reverse CONJ_TAC >- simp [Abbr ‘xs2'’, LIST_TO_SET_TAKE] \\
       ONCE_REWRITE_TAC [DISJOINT_SYM] \\
       MATCH_MP_TAC DISJOINT_SUBSET' \\
       Q.EXISTS_TAC ‘set L’ >> art [] ])
 (* final goal (before applying MONO_NOT_EQ):

    !M N. MEM M Ms /\ MEM N Ms /\
          subtree_equiv X (apply pi M) (apply pi N) p r ==>
          subtree_equiv' X M N p r
  *)
 >> PRINT_TAC "stage work on subtree_equiv_lemma"
 >> rpt GEN_TAC >> STRIP_TAC
 >> POP_ASSUM MP_TAC
 >> ONCE_REWRITE_TAC [MONO_NOT_EQ]
 (* NOTE: The antecedent “~subtree_equiv' X t1 t2 q r” makes sure that
   ‘n1 + m2 <> n1 + m1’ is always assumed (instead of ‘y1 <> y2’). And
    the goal is to prove ‘y3 <> y4 \/ n3 + m3 <> n4 + m4’.
  *)
 >> NTAC 2 (Q.PAT_X_ASSUM ‘MEM _ Ms’ MP_TAC)
 >> simp [MEM_EL]
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘j1’ STRIP_ASSUME_TAC)
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘j2’ STRIP_ASSUME_TAC)
 >> Q.PAT_X_ASSUM ‘_ = M j1’ (REWRITE_TAC o wrap)
 >> Q.PAT_X_ASSUM ‘_ = M j2’ (REWRITE_TAC o wrap)
 >> qabbrev_tac ‘M' = \i. apply pi (M i)’
 (* real goal: ~subtree_equiv X (M j1) (M j2) p r ==>
               ~subtree_equiv X (M' j1) (M' j2) p r
  *)
 >> simp [subtree_equiv_def]
 >> Know ‘BT' X (M' j1) r = BT' X (principal_hnf (M' j1)) r’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC BT_of_principal_hnf \\
     simp [Abbr ‘M'’] \\
     METIS_TAC [lameq_solvable_cong])
 >> Rewr'
 >> Know ‘BT' X (M' j2) r = BT' X (principal_hnf (M' j2)) r’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC BT_of_principal_hnf \\
     simp [Abbr ‘M'’] \\
     METIS_TAC [lameq_solvable_cong])
 >> Rewr'
 >> simp [Abbr ‘M'’] (* now H is involved instead of ‘apply pi ...’ *)
 (* special case: q = [] *)
 >> Cases_on ‘q = []’
 >- (Q.PAT_X_ASSUM ‘!q. q <<= p /\ q <> [] ==> _’ K_TAC \\
     POP_ORW >> simp [BT_ltree_el_NIL] \\
     Know ‘!i. principal_hnf (H i) = H i’
     >- (rw [Abbr ‘H’] >> MATCH_MP_TAC principal_hnf_reduce \\
         rw [hnf_appstar]) >> Rewr' \\
     Q.PAT_X_ASSUM ‘!i. solvable (H i)’ K_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> FV (H i) SUBSET X UNION RANK r’ K_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> d_max <= LENGTH (hnf_children (H i))’ K_TAC \\
     simp [Abbr ‘H’, GSYM appstar_APPEND, hnf_head_appstar] \\
     simp [head_equivalent_def] \\
     qabbrev_tac ‘vs1 = TAKE (n j1) vs’ \\
     qabbrev_tac ‘vs2 = TAKE (n j2) vs’ \\
    ‘ALL_DISTINCT vs1 /\ ALL_DISTINCT vs2’
       by simp [Abbr ‘vs1’, Abbr ‘vs2’, ALL_DISTINCT_TAKE] \\
    ‘LENGTH vs1 = n j1’
       by (qunabbrev_tac ‘vs1’ \\
           MATCH_MP_TAC LENGTH_TAKE >> art [] \\
           FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
    ‘LENGTH vs2 = n j2’
       by (qunabbrev_tac ‘vs2’ \\
           MATCH_MP_TAC LENGTH_TAKE >> art [] \\
           FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     Q_TAC (RNEWS_TAC (“ys1 :string list”, “r :num”,
                       “(n :num -> num) j1”)) ‘X’ \\
     Q_TAC (RNEWS_TAC (“ys2 :string list”, “r :num”,
                       “(n :num -> num) j2”)) ‘X’ \\
     Know ‘DISJOINT (set vs1) (set ys1)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs’ \\
         reverse CONJ_TAC >- rw [Abbr ‘vs1’, LIST_TO_SET_TAKE] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs0’ >> art [] \\
         qunabbrevl_tac [‘vs0’, ‘ys1’] \\
         MATCH_MP_TAC DISJOINT_RNEWS >> simp []) >> DISCH_TAC \\
     Know ‘DISJOINT (set vs2) (set ys2)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs’ \\
         reverse CONJ_TAC >- rw [Abbr ‘vs2’, LIST_TO_SET_TAKE] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs0’ >> art [] \\
         qunabbrevl_tac [‘vs0’, ‘ys2’] \\
         MATCH_MP_TAC DISJOINT_RNEWS >> simp []) >> DISCH_TAC \\
     qabbrev_tac ‘t1 = VAR (y j1) @* args j1’ \\
     qabbrev_tac ‘t2 = VAR (y j2) @* args j2’ \\
  (* applying for principal_hnf_tpm_reduce *)
     Know ‘principal_hnf (LAMl vs1 t1 @* MAP VAR ys1) = tpm (ZIP (vs1,ys1)) t1’
     >- (‘hnf t1’ by rw [Abbr ‘t1’, hnf_appstar] \\
         MATCH_MP_TAC principal_hnf_tpm_reduce' >> art [] \\
         MATCH_MP_TAC subterm_disjoint_lemma \\
         qexistsl_tac [‘X’, ‘r’, ‘n j1’] >> simp [] \\
         MATCH_MP_TAC SUBSET_TRANS \\
         Q.EXISTS_TAC ‘Z’ >> art [] \\
         rw [Abbr ‘t1’, FV_appstar]) >> Rewr' \\
     Know ‘principal_hnf (LAMl vs2 t2 @* MAP VAR ys2) = tpm (ZIP (vs2,ys2)) t2’
     >- (‘hnf t2’ by rw [Abbr ‘t2’, hnf_appstar] \\
         MATCH_MP_TAC principal_hnf_tpm_reduce' >> art [] \\
         MATCH_MP_TAC subterm_disjoint_lemma \\
         qexistsl_tac [‘X’, ‘r’, ‘n j2’] >> simp [] \\
         MATCH_MP_TAC SUBSET_TRANS \\
         Q.EXISTS_TAC ‘Z’ >> art [] \\
         rw [Abbr ‘t2’, FV_appstar]) >> Rewr' \\
     simp [Abbr ‘t1’, Abbr ‘t2’, tpm_appstar] \\
     PRINT_TAC "stage work on subtree_equiv_lemma" \\
     qabbrev_tac ‘pm1 = ZIP (vs1,ys1)’ \\
     qabbrev_tac ‘pm2 = ZIP (vs2,ys2)’ \\
     qabbrev_tac ‘vs1' = DROP (n j1) vs’ \\
     qabbrev_tac ‘vs2' = DROP (n j2) vs’ \\
  (* current situation:
        |<--------- vs (n_max) --------->|
        |<--- vs1 ----->|<---- vs1'----->|      y j1  ---+
        |<------ vs2 ------->|<--vs2'--->|      y j2  ---|--+
     ----------------------------------------------------|--|----
        |<--- ys1 ----->|------ys1'----->|      y' <-----+  |
        |<------ ys2 ------->|<--ys2'--->|      y' <--------+
   *)
     Know ‘ys1 <<= ys’
     >- (qunabbrevl_tac [‘ys1’, ‘ys’] \\
         MATCH_MP_TAC RNEWS_prefix >> simp []) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n1'’ STRIP_ASSUME_TAC) \\
     Know ‘n1' = n j1’
     >- (POP_ASSUM (MP_TAC o AP_TERM “LENGTH :string list -> num”) \\
         simp [LENGTH_TAKE]) >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘n1' <= n_max’ MP_TAC \\
     Q.PAT_X_ASSUM ‘ys1 = TAKE n1' ys’
       (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
     POP_ORW >> NTAC 2 DISCH_TAC \\
     qabbrev_tac ‘ys1' = DROP (n j1) ys’ \\
    ‘vs1 ++ vs1' = vs /\ ys1 ++ ys1' = ys’ by METIS_TAC [TAKE_DROP] \\
     Know ‘ys2 <<= ys’
     >- (qunabbrevl_tac [‘ys2’, ‘ys’] \\
         MATCH_MP_TAC RNEWS_prefix >> simp []) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n2'’ STRIP_ASSUME_TAC) \\
     Know ‘n2' = n j2’
     >- (POP_ASSUM (MP_TAC o AP_TERM “LENGTH :string list -> num”) \\
         simp [LENGTH_TAKE]) >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘n2' <= n_max’ MP_TAC \\
     Q.PAT_X_ASSUM ‘ys2 = TAKE n2' ys’
       (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
     POP_ORW >> NTAC 2 DISCH_TAC \\
     qabbrev_tac ‘ys2' = DROP (n j2) ys’ \\
    ‘vs2 ++ vs2' = vs /\ ys2 ++ ys2' = ys’ by METIS_TAC [TAKE_DROP] \\
  (* stage work *)
     Know ‘lswapstr pm1 (y j1) = lswapstr pm (y j1)’
     >- (‘LENGTH vs1' = LENGTH ys1'’ by rw [Abbr ‘vs1'’, Abbr ‘ys1'’] \\
         Know ‘pm = pm1 ++ ZIP (vs1',ys1')’
         >- (simp [Abbr ‘pm’, Abbr ‘pm1’] \\
            ‘LENGTH vs1 = LENGTH ys1’ by rw [Abbr ‘vs1'’] \\
             simp [ZIP_APPEND]) >> Rewr' \\
         simp [lswapstr_append, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC lswapstr_unchanged' >> simp [MAP_ZIP] \\
         reverse CONJ_TAC (* easy goal first *)
         >- (‘y j1 IN X UNION RANK r’ by METIS_TAC [SUBSET_DEF] \\
             Suff ‘DISJOINT (X UNION RANK r) (set ys1')’
             >- (REWRITE_TAC [DISJOINT_ALT] \\
                 DISCH_THEN MATCH_MP_TAC >> art []) \\
             MATCH_MP_TAC DISJOINT_SUBSET \\
             Q.EXISTS_TAC ‘set ys’ \\
             reverse CONJ_TAC >- simp [Abbr ‘ys1'’, LIST_TO_SET_DROP] \\
             simp [DISJOINT_UNION', Once DISJOINT_SYM] \\
             simp [Abbr ‘ys’, Once DISJOINT_SYM, DISJOINT_RNEWS_RANK]) \\
        ‘y j1 IN Y UNION set vs1’ by rw [Abbr ‘vs1’] \\
         Suff ‘DISJOINT (Y UNION set vs1) (set vs1')’
         >- (REWRITE_TAC [DISJOINT_ALT] \\
             DISCH_THEN MATCH_MP_TAC >> art []) \\
         REWRITE_TAC [DISJOINT_UNION] \\
         reverse CONJ_TAC (* easy goal first *)
         >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs’ MP_TAC \\
             Q.PAT_X_ASSUM ‘vs1 ++ vs1' = vs’ (REWRITE_TAC o wrap o SYM) \\
             simp [ALL_DISTINCT_APPEND']) \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs’ >> simp [Once DISJOINT_SYM] \\
         simp [Abbr ‘vs1'’, LIST_TO_SET_DROP]) >> Rewr' \\
     Know ‘lswapstr pm2 (y j2) = lswapstr pm (y j2)’
     >- (‘LENGTH vs2' = LENGTH ys2'’ by rw [Abbr ‘vs2'’, Abbr ‘ys2'’] \\
         Know ‘pm = pm2 ++ ZIP (vs2',ys2')’
         >- (simp [Abbr ‘pm’, Abbr ‘pm2’] \\
            ‘LENGTH vs2 = LENGTH ys2’ by rw [Abbr ‘vs2'’] \\
             simp [ZIP_APPEND]) >> Rewr' \\
         simp [lswapstr_append, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC lswapstr_unchanged' >> simp [MAP_ZIP] \\
         reverse CONJ_TAC (* easy goal first *)
         >- (‘y j2 IN X UNION RANK r’ by METIS_TAC [SUBSET_DEF] \\
             Suff ‘DISJOINT (X UNION RANK r) (set ys2')’
             >- (REWRITE_TAC [DISJOINT_ALT] \\
                 DISCH_THEN MATCH_MP_TAC >> art []) \\
             MATCH_MP_TAC DISJOINT_SUBSET \\
             Q.EXISTS_TAC ‘set ys’ \\
             reverse CONJ_TAC >- simp [Abbr ‘ys2'’, LIST_TO_SET_DROP] \\
             simp [DISJOINT_UNION', Once DISJOINT_SYM] \\
             simp [Abbr ‘ys’, Once DISJOINT_SYM, DISJOINT_RNEWS_RANK]) \\
        ‘y j2 IN Y UNION set vs2’ by rw [Abbr ‘vs2’] \\
         Suff ‘DISJOINT (Y UNION set vs2) (set vs2')’
         >- (REWRITE_TAC [DISJOINT_ALT] \\
             DISCH_THEN MATCH_MP_TAC >> art []) \\
         REWRITE_TAC [DISJOINT_UNION] \\
         reverse CONJ_TAC (* easy goal first *)
         >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs’ MP_TAC \\
             Q.PAT_X_ASSUM ‘vs2 ++ vs2' = vs’ (REWRITE_TAC o wrap o SYM) \\
             simp [ALL_DISTINCT_APPEND']) \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs’ >> simp [Once DISJOINT_SYM] \\
         simp [Abbr ‘vs2'’, LIST_TO_SET_DROP]) >> Rewr' \\
     simp [] \\
    ‘f j1 < k /\ f j2 < k’ by rw [] \\
    ‘b j1 = EL (j j1) xs /\ b j2 = EL (j j2) xs’ by rw [] \\
     NTAC 2 POP_ORW \\
     Know ‘EL (j j1) xs = EL (j j2) xs <=> j j1 = j j2’
     >- (Q.PAT_X_ASSUM ‘!i. i < k ==> EL (j i) xs = b i /\ _’ K_TAC \\
         MATCH_MP_TAC ALL_DISTINCT_EL_IMP >> art [] \\
         simp [Abbr ‘j’, Abbr ‘args2’, Abbr ‘d_max'’]) >> Rewr' \\
  (* !i. i < k ==> LENGTH (args' i ++ args2 i) <= d_max' i *)
     Know ‘LENGTH (args' j1 ++ args2 j1) <= d_max' j1 /\
           LENGTH (args' j2 ++ args2 j2) <= d_max' j2’
     >- simp [] \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> LENGTH (args' i ++ args2 i) <= d_max' i’ K_TAC \\
     simp [Abbr ‘Ns’, Abbr ‘tl’, Abbr ‘d_max'’, Abbr ‘args2’] \\
  (* arithmetic cleanups *)
     Know ‘d_max + (k + (n_max + (f j2 + (m j2 + SUC d_max)))) -
           (n j2 + SUC (d_max + f j2)) =
           d_max + k + n_max + m j2 - n j2’ >- simp [] >> Rewr' \\
     Know ‘d_max + (k + (n_max + (f j1 + (m j1 + SUC d_max)))) -
           (n j1 + SUC (d_max + f j1)) =
           d_max + k + n_max + m j1 - n j1’ >- simp [] >> Rewr' \\
     Know ‘d_max + k + n_max + m j2 - n j2 =
           d_max + k + n_max + m j1 - n j1 <=> m j2 + n j1 = m j1 + n j2’
     >- simp [] >> Rewr' \\
     simp [Abbr ‘j’] \\
     Cases_on ‘y j1 = y j2’ >> simp [] (* only one goal is left *) \\
     Cases_on ‘m j2 + n j1 = m j1 + n j2’ >> simp [] (* 1s left *) \\
    ‘m j1 <= d /\ m j2 <= d’ by rw [] \\
     STRIP_TAC \\
     qabbrev_tac ‘a1 = n_max + m j1’ \\
     qabbrev_tac ‘a2 = n_max + m j2’ \\
     qabbrev_tac ‘b1 = d_max + (f j1 + n j1)’ \\
     qabbrev_tac ‘b2 = d_max + (f j2 + n j2)’ \\
     Know ‘b1 - a1 <> b2 - a2 <=> b1 + a2 <> b2 + a1’ >- simp [] >> Rewr' \\
     qunabbrevl_tac [‘a1’, ‘a2’, ‘b1’, ‘b2’] \\
     Suff ‘f j1 <> f j2’ >- simp [Abbr ‘d_max’] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 (* instantiating the key substitution assumption with q <> [] *)
 >> Q.PAT_X_ASSUM ‘!q. q <<= p /\ q <> [] ==> _’ (MP_TAC o Q.SPEC ‘q’)
 >> simp [] >> DISCH_TAC
 (* some easy cases *)
 >> reverse (Cases_on ‘solvable (subterm' X (M j1) q r)’)
 >- (Know ‘unsolvable (subterm' X (M j1) q r) <=>
           ltree_el (BT' X (M j1) r) q = SOME bot’
     >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> rw []) \\
     simp [] >> DISCH_THEN K_TAC \\
     Know ‘unsolvable (subterm' X (H j1) q r)’
     >- (ASM_SIMP_TAC std_ss [] \\
         MATCH_MP_TAC unsolvable_ISUB \\
         simp [solvable_tpm]) >> DISCH_TAC \\
  (* extra goal *)
     Know ‘unsolvable (subterm' X (apply pi (M j1)) q r)’
     >- (Suff ‘subterm X (apply pi (M j1)) q r = subterm X (H j1) q r’
         >- (Rewr >> art []) \\
         FULL_SIMP_TAC std_ss [] \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> principal_hnf (apply pi (M i)) = H i’
           (MP_TAC o Q.SPEC ‘j1’) >> art [] \\
         DISCH_THEN (ONCE_REWRITE_TAC o wrap o SYM) \\
         ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC subterm_of_principal_hnf >> simp []) >> Rewr \\
     reverse (Cases_on ‘solvable (subterm' X (M j2) q r)’)
     >- (Know ‘unsolvable (subterm' X (M j2) q r) <=>
               ltree_el (BT' X (M j2) r) q = SOME bot’
         >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> rw []) \\
         simp []) \\
     Know ‘unsolvable (subterm' X (H j1) q r) <=>
           ltree_el (BT' X (H j1) r) q = SOME bot’
     >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> simp []) \\
     simp [] >> DISCH_THEN K_TAC \\
     MP_TAC (Q.SPECL [‘q’, ‘X’, ‘M (j2 :num)’, ‘r’] BT_subterm_thm) \\
     simp [] >> STRIP_TAC \\
     NTAC 3 (Cases_on ‘x’ >> fs []) \\
     qabbrev_tac ‘r2 = r + LENGTH q’ \\
     rename1 ‘subterm X (M j2) q r = SOME (N,r2)’ \\
     qabbrev_tac ‘N0 = principal_hnf N’ \\
     qabbrev_tac ‘m2 = hnf_children_size N0’ \\
     rename1 ‘ltree_el (BT' X (M j2) r) q = SOME (SOME (vs2,y2),SOME m2)’ \\
     Q.PAT_X_ASSUM ‘_ = SOME (vs2,y2)’ K_TAC >> gs [] \\
     Q.PAT_X_ASSUM ‘_ = r2’            K_TAC \\
     Q.PAT_X_ASSUM ‘_ = SOME m2’       K_TAC \\
     qabbrev_tac ‘n2 = LAMl_size N0’ \\
  (* decompose N *)
     Q.PAT_X_ASSUM ‘RNEWS r2 n2 X = vs2’ (fs o wrap o SYM) \\
     Q_TAC (RNEWS_TAC (“vs2 :string list”, “r2 :num”, “n2 :num”)) ‘X’ \\
     qabbrev_tac ‘N1 = principal_hnf (N0 @* MAP VAR vs2)’ \\
     Q_TAC (HNF_TAC (“N0 :term”, “vs2 :string list”,
                     “y2' :string”, “Ns2 :term list”)) ‘N1’ \\
    ‘TAKE (LAMl_size N0) vs2 = vs2’ by rw [] \\
     POP_ASSUM (rfs o wrap) \\
    ‘subterm X (H j2) q r <> NONE’ by ASM_SIMP_TAC std_ss [] \\
     Know ‘IMAGE y (count k) SUBSET X UNION RANK r2’
     >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘X UNION RANK r’ \\
         reverse CONJ_TAC
         >- (Suff ‘RANK r SUBSET RANK r2’ >- SET_TAC [] \\
             rw [RANK_MONO, Abbr ‘r2’]) \\
         rw [SUBSET_DEF] >> rename1 ‘i < k’ \\
         Know ‘y i IN Z’ >- rw [] \\
         Suff ‘Z SUBSET X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
         FIRST_X_ASSUM ACCEPT_TAC) >> DISCH_TAC \\
     Know ‘set vs SUBSET X UNION RANK r2’
     >- (Suff ‘set vs SUBSET RANK r2’ >- SET_TAC [] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘RANK r’ >> art [] \\
         simp [Abbr ‘r2’, RANK_MONO]) >> DISCH_TAC \\
     Know ‘set ys SUBSET X UNION RANK r2’
     >- (Suff ‘set ys SUBSET RANK r2’ >- SET_TAC [] \\
         qunabbrev_tac ‘ys’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp [Abbr ‘r2’] \\
         rw [LENGTH_NON_NIL]) >> DISCH_TAC \\
     Know ‘FV (tpm (REVERSE pm) N) SUBSET X UNION RANK r2’
     >- (MATCH_MP_TAC FV_tpm_lemma \\
         Q.EXISTS_TAC ‘r2’ >> simp [Abbr ‘pm’, MAP_REVERSE, MAP_ZIP]) \\
     DISCH_TAC \\
     Know ‘m2 <= d_max’
     >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘d’ \\
         reverse CONJ_TAC >- rw [Abbr ‘d_max’] \\
         Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width (M j2) q’ \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC subterm_width_inclusive \\
             Q.EXISTS_TAC ‘p’ >> simp []) \\
         qunabbrevl_tac [‘m2’, ‘N0’] \\
        ‘N = subterm' X (M j2) q r’ by rw [] >> POP_ORW \\
         MATCH_MP_TAC subterm_width_last >> simp []) >> DISCH_TAC \\
     Know ‘solvable (subterm' X (H j2) q r)’
     >- (ASM_SIMP_TAC std_ss [] \\
         MATCH_MP_TAC (cj 1 solvable_isub_permutator_alt) \\
         qexistsl_tac [‘X’, ‘r2’, ‘d_max’, ‘y’, ‘k’] \\
         simp [subterm_width_nil, principal_hnf_tpm'] \\
         POP_ASSUM MP_TAC >> rw [Abbr ‘m2’] \\
         Know ‘y i IN X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
         Suff ‘RANK r SUBSET RANK r2’ >- SET_TAC [] \\
         rw [Abbr ‘r2’, RANK_MONO]) >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> subterm X (H i) q r <> NONE /\ _’ ASSUME_TAC \\
     MP_TAC (Q.SPECL [‘q’, ‘X’, ‘H (j2 :num)’, ‘r’] BT_subterm_thm) \\
     simp [] >> STRIP_TAC (* this asserts ‘x’ *) \\
     NTAC 3 (Cases_on ‘x’ >> fs []) \\
     simp [head_equivalent_def])
 (* stage work *)
 >> reverse (Cases_on ‘solvable (subterm' X (M j2) q r)’)
 >- (Know ‘unsolvable (subterm' X (M j2) q r) <=>
           ltree_el (BT' X (M j2) r) q = SOME bot’
     >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> rw []) \\
     simp [] >> DISCH_THEN K_TAC \\
     reverse (Cases_on ‘solvable (subterm' X (M j1) q r)’)
     >- (Know ‘unsolvable (subterm' X (M j1) q r) <=>
               ltree_el (BT' X (M j1) r) q = SOME bot’
         >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> rw []) \\
         simp []) \\
     Know ‘unsolvable (subterm' X (H j2) q r)’
     >- (ASM_SIMP_TAC std_ss [] \\
         MATCH_MP_TAC unsolvable_ISUB \\
         simp [solvable_tpm]) >> DISCH_TAC \\
     Know ‘unsolvable (subterm' X (H j2) q r) <=>
           ltree_el (BT' X (H j2) r) q = SOME bot’
     >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> simp []) \\
     simp [] >> DISCH_THEN K_TAC \\
     MP_TAC (Q.SPECL [‘q’, ‘X’, ‘M (j1 :num)’, ‘r’] BT_subterm_thm) \\
     simp [] >> STRIP_TAC \\
     NTAC 3 (Cases_on ‘x’ >> fs []) \\
     qabbrev_tac ‘r1 = r + LENGTH q’ \\
     rename1 ‘subterm X (M j1) q r = SOME (N,r1)’ \\
     qabbrev_tac ‘N0 = principal_hnf N’ \\
     qabbrev_tac ‘m1 = hnf_children_size N0’ \\
     rename1 ‘ltree_el (BT' X (M j1) r) q = SOME (SOME (vs1,y1),SOME m1)’ \\
     Q.PAT_X_ASSUM ‘_ = SOME (vs1,y1)’ K_TAC >> gs [] \\
     Q.PAT_X_ASSUM ‘_ = r1’      K_TAC \\
     Q.PAT_X_ASSUM ‘_ = SOME m1’ K_TAC \\
     qabbrev_tac ‘n1 = LAMl_size N0’ \\
  (* decompose N *)
     Q.PAT_X_ASSUM ‘RNEWS r1 n1 X = vs1’ (fs o wrap o SYM) \\
     Q_TAC (RNEWS_TAC (“vs1 :string list”, “r1 :num”, “n1 :num”)) ‘X’ \\
     qabbrev_tac ‘N1 = principal_hnf (N0 @* MAP VAR vs1)’ \\
     Q_TAC (HNF_TAC (“N0 :term”, “vs1 :string list”,
                     “y1' :string”, “Ns1 :term list”)) ‘N1’ \\
    ‘TAKE (LAMl_size N0) vs1 = vs1’ by rw [] \\
     POP_ASSUM (rfs o wrap) \\
    ‘subterm X (H j1) q r <> NONE’ by ASM_SIMP_TAC std_ss [] \\
     Know ‘IMAGE y (count k) SUBSET X UNION RANK r1’
     >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘X UNION RANK r’ \\
         reverse CONJ_TAC
         >- (Suff ‘RANK r SUBSET RANK r1’ >- SET_TAC [] \\
             rw [RANK_MONO, Abbr ‘r1’]) \\
         rw [SUBSET_DEF] >> rename1 ‘i < k’ \\
         Know ‘y i IN Z’ >- rw [] \\
         Suff ‘Z SUBSET X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
         FIRST_X_ASSUM ACCEPT_TAC) >> DISCH_TAC \\
     Know ‘set vs SUBSET X UNION RANK r1’
     >- (Suff ‘set vs SUBSET RANK r1’ >- SET_TAC [] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘RANK r’ >> art [] \\
         simp [Abbr ‘r1’, RANK_MONO]) >> DISCH_TAC \\
     Know ‘set ys SUBSET X UNION RANK r1’
     >- (Suff ‘set ys SUBSET RANK r1’ >- SET_TAC [] \\
         qunabbrev_tac ‘ys’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp [Abbr ‘r1’] \\
         rw [LENGTH_NON_NIL]) >> DISCH_TAC \\
     Know ‘FV (tpm (REVERSE pm) N) SUBSET X UNION RANK r1’
     >- (MATCH_MP_TAC FV_tpm_lemma \\
         Q.EXISTS_TAC ‘r1’ >> simp [Abbr ‘pm’, MAP_REVERSE, MAP_ZIP]) \\
     DISCH_TAC \\
     Know ‘m1 <= d_max’
     >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘d’ \\
         reverse CONJ_TAC >- rw [Abbr ‘d_max’] \\
         Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width (M j1) q’ \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC subterm_width_inclusive \\
             Q.EXISTS_TAC ‘p’ >> simp []) \\
         qunabbrevl_tac [‘m1’, ‘N0’] \\
        ‘N = subterm' X (M j1) q r’ by rw [] >> POP_ORW \\
         MATCH_MP_TAC subterm_width_last >> simp []) >> DISCH_TAC \\
     Know ‘solvable (subterm' X (H j1) q r)’
     >- (ASM_SIMP_TAC std_ss [] \\
         MATCH_MP_TAC (cj 1 solvable_isub_permutator_alt) \\
         qexistsl_tac [‘X’, ‘r1’, ‘d_max’, ‘y’, ‘k’] \\
         simp [subterm_width_nil, principal_hnf_tpm'] \\
         POP_ASSUM MP_TAC >> rw [Abbr ‘m1’] \\
         Know ‘y i IN X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
         Suff ‘RANK r SUBSET RANK r1’ >- SET_TAC [] \\
         rw [Abbr ‘r1’, RANK_MONO]) >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> subterm X (H i) q r <> NONE /\ _’ ASSUME_TAC \\
     MP_TAC (Q.SPECL [‘q’, ‘X’, ‘H (j1 :num)’, ‘r’] BT_subterm_thm) \\
     simp [] >> STRIP_TAC (* this asserts ‘x’ *) \\
     NTAC 3 (Cases_on ‘x’ >> fs []) \\
     simp [head_equivalent_def])
 (* stage work, now “subterm' X (M j1) p r)” and “subterm' X (M j2) p r)”
    are both solvable.
  *)
 >> PRINT_TAC "stage work on subtree_equiv_lemma"
 >> MP_TAC (Q.SPECL [‘q’, ‘X’, ‘M (j1 :num)’, ‘r’] BT_subterm_thm)
 >> simp [] >> STRIP_TAC (* this asserts ‘x’ *)
 >> NTAC 3 (Cases_on ‘x’ >> fs [])
 >> qabbrev_tac ‘r1 = r + LENGTH q’
 >> rename1 ‘subterm X (M j1) q r = SOME (N,r1)’
 >> qabbrev_tac ‘N0 = principal_hnf N’
 >> qabbrev_tac ‘m1 = hnf_children_size N0’
 >> rename1 ‘ltree_el (BT' X (M j1) r) q = SOME (SOME (vs1,y1),SOME m1)’
 >> Q.PAT_X_ASSUM ‘_ = SOME (vs1,y1)’ K_TAC >> gs []
 >> Q.PAT_X_ASSUM ‘_ = r1’            K_TAC
 >> Q.PAT_X_ASSUM ‘_ = SOME m1’       K_TAC
 >> qabbrev_tac ‘n1 = LAMl_size N0’
 >> MP_TAC (Q.SPECL [‘q’, ‘X’, ‘M (j2 :num)’, ‘r’] BT_subterm_thm)
 >> simp [] >> STRIP_TAC (* this asserts ‘x’ *)
 >> NTAC 3 (Cases_on ‘x’ >> fs [])
 >> rename1 ‘subterm X (M j2) q r = SOME (N',r1)’
 >> qabbrev_tac ‘N0' = principal_hnf N'’
 >> qabbrev_tac ‘m2 = hnf_children_size N0'’
 >> rename1 ‘ltree_el (BT' X (M j2) r) q = SOME (SOME (vs2,y2),SOME m2)’
 >> Q.PAT_X_ASSUM ‘_ = SOME (vs2,y2)’ K_TAC >> gs []
 >> Q.PAT_X_ASSUM ‘_ = r1’            K_TAC
 >> Q.PAT_X_ASSUM ‘_ = SOME m2’       K_TAC
 >> qabbrev_tac ‘n2 = LAMl_size N0'’
 >> simp [head_equivalent_def]
 (* decompose N *)
 >> Q.PAT_X_ASSUM ‘RNEWS r1 n1 X = vs1’ (fs o wrap o SYM)
 >> Q_TAC (RNEWS_TAC (“vs1 :string list”, “r1 :num”, “n1 :num”)) ‘X’
 >> qabbrev_tac ‘N1 = principal_hnf (N0 @* MAP VAR vs1)’
 >> Q_TAC (HNF_TAC (“N0 :term”, “vs1 :string list”,
                    “y1' :string”, “Ns1 :term list”)) ‘N1’
 >> ‘TAKE (LAMl_size N0) vs1 = vs1’ by rw []
 >>  POP_ASSUM (rfs o wrap) >> T_TAC
 >> ‘LENGTH Ns1 = m1 /\ hnf_headvar N1 = y1' /\ hnf_children N1 = Ns1’
       by rw [Abbr ‘m1’]
 >> Q.PAT_X_ASSUM ‘N0 = _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘N1 = _’ (ASSUME_TAC o SYM)
  (* decompose N' *)
 >> Q.PAT_X_ASSUM ‘RNEWS r1 n2 X = vs2’ (fs o wrap o SYM)
 >> Q_TAC (RNEWS_TAC (“vs2 :string list”, “r1 :num”, “n2 :num”)) ‘X’
 >> qabbrev_tac ‘N1' = principal_hnf (N0' @* MAP VAR vs2)’
 >> Q_TAC (HNF_TAC (“N0' :term”, “vs2 :string list”,
                    “y2' :string”, “Ns2 :term list”)) ‘N1'’
 >> ‘TAKE (LAMl_size N0') vs2 = vs2’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> ‘LENGTH Ns2 = m2 /\ hnf_headvar N1' = y2' /\ hnf_children N1' = Ns2’
       by rw [Abbr ‘m2’]
 >> Q.PAT_X_ASSUM ‘N0' = _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘N1' = _’ (ASSUME_TAC o SYM)
 >> fs []
 >> Q.PAT_X_ASSUM ‘y2' = y2’ (fs o wrap)
 >> Q.PAT_X_ASSUM ‘y1' = y1’ (fs o wrap)
 >> Know ‘subterm X (H j1) q r <> NONE /\
          subterm X (H j2) q r <> NONE’
 >- ASM_SIMP_TAC std_ss []
 >> STRIP_TAC
 >> Know ‘IMAGE y (count k) SUBSET X UNION RANK r1’
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘X UNION RANK r’ \\
     reverse CONJ_TAC
     >- (Suff ‘RANK r SUBSET RANK r1’ >- SET_TAC [] \\
         rw [RANK_MONO, Abbr ‘r1’]) \\
     rw [SUBSET_DEF] >> rename1 ‘i < k’ \\
     Know ‘y i IN Z’ >- rw [] \\
     Suff ‘Z SUBSET X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
     FIRST_X_ASSUM ACCEPT_TAC)
 >> DISCH_TAC
 >> Know ‘set vs SUBSET X UNION RANK r1’
 >- (Suff ‘set vs SUBSET RANK r1’ >- SET_TAC [] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘RANK r’ >> art [] \\
     simp [Abbr ‘r1’, RANK_MONO])
 >> DISCH_TAC
 >> Know ‘set ys SUBSET X UNION RANK r1’
 >- (Suff ‘set ys SUBSET RANK r1’ >- SET_TAC [] \\
     qunabbrev_tac ‘ys’ \\
     MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp [Abbr ‘r1’] \\
     rw [LENGTH_NON_NIL])
 >> DISCH_TAC
 >> Know ‘FV (tpm (REVERSE pm) N)  SUBSET X UNION RANK r1 /\
          FV (tpm (REVERSE pm) N') SUBSET X UNION RANK r1’
 >- (CONJ_TAC \\
     MATCH_MP_TAC FV_tpm_lemma \\
     Q.EXISTS_TAC ‘r1’ >> simp [Abbr ‘pm’, MAP_REVERSE, MAP_ZIP])
 >> STRIP_TAC
 >> Know ‘m1 <= d’ (* m1 = hnf_children_size N0 *)
 >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width (M j1) q’ \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC subterm_width_inclusive \\
         Q.EXISTS_TAC ‘p’ >> simp []) \\
     simp [Abbr ‘m1’, Abbr ‘N0’] \\
    ‘N = subterm' X (M j1) q r’ by rw [] >> POP_ORW \\
     MATCH_MP_TAC subterm_width_last >> simp [])
 >> DISCH_TAC
 >> Know ‘m1 <= d_max’ (* m1 = hnf_children_size N0 *)
 >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘d’ \\
     rw [Abbr ‘d_max’])
 >> DISCH_TAC
 >> Know ‘m2 <= d’ (* m2 = hnf_children_size N0' *)
 >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width (M j2) q’ \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC subterm_width_inclusive \\
         Q.EXISTS_TAC ‘p’ >> simp []) \\
     qunabbrevl_tac [‘m2’, ‘N0'’] \\
    ‘N' = subterm' X (M j2) q r’ by rw [] >> POP_ORW \\
     MATCH_MP_TAC subterm_width_last >> simp [])
 >> DISCH_TAC
 >> Know ‘m2 <= d_max’ (* m2 = hnf_children_size N0' *)
 >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘d’ \\
     rw [Abbr ‘d_max’])
 >> DISCH_TAC
 >> Know ‘solvable (subterm' X (H j1) q r) /\
          solvable (subterm' X (H j2) q r)’
 >- (ASM_SIMP_TAC std_ss [] \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC (cj 1 solvable_isub_permutator_alt) \\
       qexistsl_tac [‘X’, ‘r1’, ‘d_max’, ‘y’, ‘k’] \\
       simp [subterm_width_nil, principal_hnf_tpm'] \\
       POP_ASSUM MP_TAC >> rw [Abbr ‘m1’] \\
       Q.PAT_X_ASSUM ‘IMAGE y (count k) SUBSET X UNION RANK r1’ MP_TAC \\
       rw [SUBSET_DEF] \\
       POP_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘i’ >> art [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC (cj 1 solvable_isub_permutator_alt) \\
       qexistsl_tac [‘X’, ‘r1’, ‘d_max’, ‘y’, ‘k’] \\
       simp [subterm_width_nil, principal_hnf_tpm'] \\
       POP_ASSUM MP_TAC >> rw [Abbr ‘m1’] \\
       Q.PAT_X_ASSUM ‘IMAGE y (count k) SUBSET X UNION RANK r1’ MP_TAC \\
       rw [SUBSET_DEF] \\
       POP_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘i’ >> art [] ])
 >> STRIP_TAC
 >> PRINT_TAC "stage work on subtree_equiv_lemma"
 >> Q.PAT_X_ASSUM ‘!i. i < k ==> subterm X (H i) q r <> NONE /\ _’ ASSUME_TAC
 >> MP_TAC (Q.SPECL [‘q’, ‘X’, ‘H (j1 :num)’, ‘r’] BT_subterm_thm)
 >> simp [] >> STRIP_TAC (* this asserts ‘x’ *)
 >> NTAC 3 (Cases_on ‘x’ >> fs [])
 >> rename1 ‘subterm X (H j1) q r = SOME (W,r1)’
 >> qabbrev_tac ‘W0 = principal_hnf W’
 >> qabbrev_tac ‘m3 = hnf_children_size W0’
 >> rename1 ‘ltree_el (BT' X (H j1) r) q = SOME (SOME (vs3,y3),SOME m3)’
 >> Q.PAT_X_ASSUM ‘_ = SOME (vs3,y3)’ K_TAC
 >> Q.PAT_X_ASSUM ‘_ = SOME m3’       K_TAC
 >> qabbrev_tac ‘n3 = LAMl_size W0’
 >> Q.PAT_X_ASSUM ‘_ = r1’ (fs o wrap) >> T_TAC
 >> MP_TAC (Q.SPECL [‘q’, ‘X’, ‘H (j2 :num)’, ‘r’] BT_subterm_thm)
 >> simp [] >> STRIP_TAC (* this asserts ‘x’ *)
 >> NTAC 3 (Cases_on ‘x’ >> fs [])
 >> rename1 ‘subterm X (H j2) q r = SOME (W',r1)’
 >> qabbrev_tac ‘W0' = principal_hnf W'’
 >> qabbrev_tac ‘m4 = hnf_children_size W0'’
 >> rename1 ‘ltree_el (BT' X (H j2) r) q = SOME (SOME (vs4,y4),SOME m4)’
 >> Q.PAT_X_ASSUM ‘_ = SOME (vs4,y4)’ K_TAC
 >> Q.PAT_X_ASSUM ‘_ = SOME m4’       K_TAC
 >> qabbrev_tac ‘n4 = LAMl_size W0'’
 >> Q.PAT_X_ASSUM ‘_ = r1’ (fs o wrap) >> T_TAC
 (* decompose W *)
 >> Q.PAT_X_ASSUM ‘RNEWS r1 n3 X = vs3’ (fs o wrap o SYM)
 >> Q_TAC (RNEWS_TAC (“vs3 :string list”, “r1 :num”, “n3 :num”)) ‘X’
 >> qabbrev_tac ‘W1 = principal_hnf (W0 @* MAP VAR vs3)’
 >> Q_TAC (HNF_TAC (“W0 :term”, “vs3 :string list”,
                    “y3' :string”, “Ns3 :term list”)) ‘W1’
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs3) (FV W0)’ K_TAC
  (* decompose W' *)
 >> Q.PAT_X_ASSUM ‘RNEWS r1 n4 X = vs4’ (fs o wrap o SYM)
 >> Q_TAC (RNEWS_TAC (“vs4 :string list”, “r1 :num”, “n4 :num”)) ‘X’
 >> qabbrev_tac ‘W1' = principal_hnf (W0' @* MAP VAR vs4)’
 >> Q_TAC (HNF_TAC (“W0' :term”, “vs4 :string list”,
                    “y4' :string”, “Ns4 :term list”)) ‘W1'’
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs4) (FV W0')’ K_TAC
  (* decompose W and W' (ending part) *)
 >> Know ‘TAKE (LAMl_size W0) vs3 = vs3 /\ TAKE (LAMl_size W0') vs4 = vs4’
 >- simp []
 >> DISCH_THEN (rfs o CONJUNCTS)
 >> Q.PAT_X_ASSUM ‘hnf_headvar (principal_hnf (W0 @* MAP VAR vs3)) = y3’ MP_TAC
 >> simp [] (* y3' = y3 *)
 >> DISCH_THEN (rfs o wrap)
 >> Q.PAT_X_ASSUM ‘hnf_headvar (principal_hnf (W0' @* MAP VAR vs4)) = y4’ MP_TAC
 >> simp [] (* y4' = y4 *)
 >> DISCH_THEN (rfs o wrap)
 (* properties of W0 *)
 >> ‘LAMl_size W0 = n3 /\ hnf_children_size W0 = m3 /\
     hnf_headvar W1 = y3’ by rw []
 >> Q.PAT_X_ASSUM ‘W0 = _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘W1 = _’ (ASSUME_TAC o SYM)
 (* properties of W0' *)
 >> ‘LAMl_size W0' = n4 /\ hnf_children_size W0' = m4 /\
     hnf_headvar W1' = y4’ by rw []
 >> Q.PAT_X_ASSUM ‘W0' = _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘W1' = _’ (ASSUME_TAC o SYM)
 >> simp [head_equivalent_def]
 (* final shape of the goal:
    y1 <> y2 \/ m2 + n1 <> m1 + n2 ==> y3 <> y4 \/ m4 + n3 <> m3 + n4
  *)
 >> Know ‘W = tpm (REVERSE pm) N ISUB ss’
 >- (Q.PAT_X_ASSUM ‘!i. i < k ==> subterm X (H i) q r <> NONE /\ _’
       (MP_TAC o Q.SPEC ‘j1’) >> simp [])
 >> DISCH_TAC
 >> Know ‘W' = tpm (REVERSE pm) N' ISUB ss’
 >- (Q.PAT_X_ASSUM ‘!i. i < k ==> subterm X (H i) q r <> NONE /\ _’
       (MP_TAC o Q.SPEC ‘j2’) >> simp [])
 >> DISCH_TAC
 (* applying hreduce_ISUB and tpm_hreduces *)
 >> ‘N -h->* N0 /\ N' -h->* N0'’ by METIS_TAC [principal_hnf_thm']
 >> Know ‘W  -h->* tpm (REVERSE pm) N0  ISUB ss /\
          W' -h->* tpm (REVERSE pm) N0' ISUB ss’
 >- simp [hreduce_ISUB, tpm_hreduces]
 >> Q.PAT_ASSUM ‘LAMl vs1 _ = N0’  (REWRITE_TAC o wrap o SYM)
 >> Q.PAT_ASSUM ‘LAMl vs2 _ = N0'’ (REWRITE_TAC o wrap o SYM)
 >> Q.PAT_ASSUM ‘_ = N1’  (REWRITE_TAC o wrap o SYM)
 >> Q.PAT_ASSUM ‘_ = N1'’ (REWRITE_TAC o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘W  = tpm (REVERSE pm) N  ISUB ss’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘W' = tpm (REVERSE pm) N' ISUB ss’ (ASSUME_TAC o SYM)
 >> simp [tpm_LAMl, tpm_appstar]
 >> qabbrev_tac ‘y1'  = lswapstr (REVERSE pm) y1’
 >> qabbrev_tac ‘y2'  = lswapstr (REVERSE pm) y2’
 >> qabbrev_tac ‘Ns1' = listpm term_pmact (REVERSE pm) Ns1’
 >> qabbrev_tac ‘Ns2' = listpm term_pmact (REVERSE pm) Ns2’
 >> Know ‘listpm string_pmact (REVERSE pm) vs1 = vs1’
 >- (simp [Once LIST_EQ_REWRITE] \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     MATCH_MP_TAC lswapstr_unchanged' \\
     simp [Abbr ‘pm’, MAP_REVERSE, MAP_ZIP] \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       POP_ASSUM MP_TAC \\
       Suff ‘DISJOINT (set vs1) (set vs)’
       >- (rw [DISJOINT_ALT] \\
           FIRST_X_ASSUM MATCH_MP_TAC >> simp [EL_MEM]) \\
       MATCH_MP_TAC DISJOINT_SUBSET \\
       Q.EXISTS_TAC ‘set vs0’ >> art [] \\
       qunabbrevl_tac [‘vs1’, ‘vs0’] \\
       MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’],
       (* goal 2 (of 2) *)
       POP_ASSUM MP_TAC \\
       Suff ‘DISJOINT (set vs1) (set ys)’
       >- (rw [DISJOINT_ALT] \\
           FIRST_X_ASSUM MATCH_MP_TAC >> simp [EL_MEM]) \\
       qunabbrevl_tac [‘vs1’, ‘ys’] \\
       MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’] ])
 >> Rewr'
 >> Know ‘listpm string_pmact (REVERSE pm) vs2 = vs2’
 >- (simp [Once LIST_EQ_REWRITE] \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     MATCH_MP_TAC lswapstr_unchanged' \\
     simp [Abbr ‘pm’, MAP_REVERSE, MAP_ZIP] \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       POP_ASSUM MP_TAC \\
       Suff ‘DISJOINT (set vs2) (set vs)’
       >- (rw [DISJOINT_ALT] \\
           FIRST_X_ASSUM MATCH_MP_TAC >> simp [EL_MEM]) \\
       MATCH_MP_TAC DISJOINT_SUBSET \\
       Q.EXISTS_TAC ‘set vs0’ >> art [] \\
       qunabbrevl_tac [‘vs2’, ‘vs0’] \\
       MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’],
       (* goal 2 (of 2) *)
       POP_ASSUM MP_TAC \\
       Suff ‘DISJOINT (set vs2) (set ys)’
       >- (rw [DISJOINT_ALT] \\
           FIRST_X_ASSUM MATCH_MP_TAC >> simp [EL_MEM]) \\
       qunabbrevl_tac [‘vs2’, ‘ys’] \\
       MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’] ])
 >> Rewr'
 >> Know ‘DISJOINT (set vs1) (DOM ss)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘X UNION RANK r’ \\
     reverse CONJ_TAC
     >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘Z’ >> simp [] \\
         rw [SUBSET_DEF] >> simp []) \\
     simp [DISJOINT_UNION', Abbr ‘vs1’] \\
     MATCH_MP_TAC DISJOINT_RNEWS_RANK >> simp [Abbr ‘r1’])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set vs2) (DOM ss)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘X UNION RANK r’ \\
     reverse CONJ_TAC
     >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘Z’ >> simp [] \\
         rw [SUBSET_DEF] >> simp []) \\
     simp [DISJOINT_UNION', Abbr ‘vs2’] \\
     MATCH_MP_TAC DISJOINT_RNEWS_RANK >> simp [Abbr ‘r1’])
 >> DISCH_TAC
 >> simp [LAMl_ISUB, appstar_ISUB]
 >> qabbrev_tac ‘Ns1'' = MAP (\t. t ISUB ss) Ns1'’
 >> qabbrev_tac ‘Ns2'' = MAP (\t. t ISUB ss) Ns2'’
 >> ‘LENGTH Ns1'' = m1 /\ LENGTH Ns2'' = m2’
      by simp [Abbr ‘Ns1''’, Abbr ‘Ns2''’, Abbr ‘Ns1'’, Abbr ‘Ns2'’]
 (* stage work (before final case analysis)

    N  -h->* LAMl vs1 (VAR y1 @* Ns1) (= N0)
    N' -h->* LAMl vs2 (VAR y2 @* Ns2) (= N0')
   --------------------------------------------
    W  -h->* LAMl vs3 (VAR y3 @* Ns3) (= W0)
    W  -h->* LAMl vs1 ((VAR y1' ISUB ss) @* Ns1'')
   --------------------------------------------
    W' -h->* LAMl vs4 (VAR y4 @* Ns4) (= W0')
    W' -h->* LAMl vs2 ((VAR y2' ISUB ss) @* Ns2'')

    Now, to understand the (alternative) principal_hnf of W and W', we need to
    rewrite ‘VAR y1' ISUB ss’ to either VAR y1' or P, resp., depending on if
   ‘y1' IN DOM ss’ or not (and also on ‘y2' IN DOM ss’ or not).
  *)
 >> Cases_on ‘y1' NOTIN DOM ss’ >> Cases_on ‘y2' NOTIN DOM ss’
 (* Case 1 (of 4): easy

    W  -h->* LAMl vs3 (VAR y3  @* Ns3) (= W0)
    W  -h->* LAMl vs1 (VAR y1' @* Ns1''), thus y3 = y1'
   --------------------------------------------
    W' -h->* LAMl vs4 (VAR y4  @* Ns4) (= W0')
    W' -h->* LAMl vs2 (VAR y2' @* Ns2''), thus y4 = y2'

    Abbrev (y1' = lswapstr (REVERSE pm) y1)
    Abbrev (y2' = lswapstr (REVERSE pm) y2)
  *)
 >- (simp [ISUB_VAR_FRESH'] >> STRIP_TAC \\
    ‘hnf (LAMl vs1 (VAR y1' @* Ns1'')) /\
     hnf (LAMl vs2 (VAR y2' @* Ns2''))’ by rw [hnf_appstar] \\
    ‘LAMl vs1 (VAR y1' @* Ns1'') = W0 /\
     LAMl vs2 (VAR y2' @* Ns2'') = W0'’ by METIS_TAC [principal_hnf_thm'] \\
    ‘LAMl_size W0 = n1 /\ LAMl_size W0' = n2’ by rw [LAMl_size_hnf] \\
    ‘n3 = n1 /\ n4 = n2’ by PROVE_TAC [] \\
     Know ‘y3 = y1' /\ y4 = y2' /\ Ns1'' = Ns3 /\ Ns2'' = Ns4’
     >- (Q.PAT_X_ASSUM ‘LAMl vs3 _ = W0’ MP_TAC \\
         Q.PAT_X_ASSUM ‘_ = W1’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘LAMl vs4 _ = W0'’ MP_TAC \\
         Q.PAT_X_ASSUM ‘_ = W1'’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) \\
         fs []) >> STRIP_TAC \\
     simp [] \\
     qunabbrevl_tac [‘m3’, ‘m4’] \\
     Q.PAT_X_ASSUM ‘_ = W0’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) \\
     simp [Abbr ‘y1'’, Abbr ‘y2'’])
 (* Case 2 (of 4): hard, we try to directly prove ‘y1' <> y4’

    N  -h->* LAMl vs1  (VAR y1  @* Ns1) (= N0)
    N' -h->* LAMl vs2  (VAR y2  @* Ns2) (= N0')
   --------------------------------------------
    W  -h->* LAMl vs3  (VAR y3  @* Ns3) (= W0)
           = LAMl vs1  (VAR y1' @* Ns1''), thus y1' = y3
   --------------------------------------------
    W' -h->* LAMl vs4  (VAR y4  @* Ns4) (= W0') --+
    W' -h->* LAMl vs2  (P       @* Ns2'')         |=
       -h->* LAMl zs2' (VAR h   @* Ns2x) ---------+

    Abbrev (y1' = lswapstr (REVERSE pm) y1)

    main goal: y1' <> y4 (y2 seems irrelevant now, same is ‘y1 <> y2’)

    Structure of W0:

    LAMl |<--------- vs3 --------->| VAR y3/y1'

    d_max = d + n_max, where d >= m2 /\ n_max >= n3, thus n3 < n4 /\ vs3 <<= vs4

    Structure of W0':

    LAMl |<---(vs2)--- vs4 ------------>| VAR y4 (= LAST vs4)
    LAMl |<----------- zs2' ----------->| VAR h
    LAMl |<----vs2----->|<----zs2---->|h| VAR h
        n4 =   n2      +  d_max - m2  +1
  *)
 >- (PRINT_TAC "stage work on subtree_equiv_lemma" \\
     POP_ASSUM MP_TAC >> simp [ISUB_VAR_FRESH'] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘j3’ STRIP_ASSUME_TAC) \\
    ‘(LEAST j. y j = y2') = f j3’ by rw [] >> POP_ORW \\
     ONCE_REWRITE_TAC [TAUT ‘p /\ q ==> r <=> p ==> q ==> r’] >> STRIP_TAC \\
    ‘hnf (LAMl vs1 (VAR y1' @* Ns1''))’ by rw [hnf_appstar] \\
    ‘LAMl vs1 (VAR y1' @* Ns1'') = W0’ by METIS_TAC [principal_hnf_thm'] \\
    ‘LAMl_size W0 = n1’ by rw [LAMl_size_hnf] \\
    ‘n3 = n1’ by PROVE_TAC [] \\
     Know ‘y3 = y1' /\ Ns1'' = Ns3’
     >- (Q.PAT_X_ASSUM ‘LAMl vs3 _ = W0’ MP_TAC \\
         Q.PAT_X_ASSUM ‘_ = W0’ (REWRITE_TAC o wrap o SYM) \\
         simp [] \\
         Q.PAT_X_ASSUM ‘_ = W1’ (REWRITE_TAC o wrap o SYM) \\
         fs []) >> STRIP_TAC \\
     simp [] \\
  (* NOTE: The proof completes if we can just show ‘y3 <> y4’. *)
     qabbrev_tac ‘X' = set vs4 UNION FV W1' UNION
                       BIGUNION (IMAGE FV (set Ns2''))’ \\
    ‘FINITE X'’ by rw [Abbr ‘X'’] \\
     qabbrev_tac ‘d' = MAX n4 (SUC (d_max' j3))’ \\
     Q_TAC (NEWS_TAC (“L :string list”, “d' :num”)) ‘X'’ \\
    ‘d_max' j3 < LENGTH L /\ n4 <= LENGTH L’ by simp [Abbr ‘d'’, MAX_LE] \\
     Know ‘DISJOINT (set L) (set vs2) /\
           DISJOINT (set L) (set vs4)’
     >- (rw [Abbr ‘L’, Abbr ‘vs2’, Abbr ‘vs4’] (* 2 subgoals, same tactics *) \\
         MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’]) >> STRIP_TAC \\
     Q.PAT_X_ASSUM ‘FINITE X'’ K_TAC \\
     Q.PAT_X_ASSUM ‘DISJOINT (set L) X'’ MP_TAC \\
     qunabbrev_tac ‘X'’ \\
     DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [DISJOINT_UNION']) \\
     STRIP_TAC (* W -h->* ... *) \\
    ‘m2 <= d_max' j3’ by simp [Abbr ‘d_max'’] \\
  (* applying hreduce_permutator_shared *)
     MP_TAC (Q.SPECL [‘Ns2''’, ‘d_max + f (j3 :num)’, ‘L’]
                     hreduce_permutator_shared) >> simp [] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘zs2’ (Q.X_CHOOSE_THEN ‘z2’ STRIP_ASSUME_TAC)) \\
     qabbrev_tac ‘P' = P (f j3)’ \\
     Q.PAT_X_ASSUM ‘P' @* Ns2'' -h->* _’ MP_TAC \\
     qabbrev_tac ‘h = LAST L’ (* the new shared head variable *) \\
     qabbrev_tac ‘L' = FRONT L’ \\
    ‘L <> []’ by rw [GSYM LENGTH_NON_NIL] \\
     Q.PAT_X_ASSUM ‘IS_SUFFIX L _’ MP_TAC \\
    ‘L = SNOC h L'’ by ASM_SIMP_TAC std_ss [Abbr ‘L'’, Abbr ‘h’, SNOC_LAST_FRONT] \\
     POP_ORW \\
     simp [IS_SUFFIX] >> STRIP_TAC \\
     Q.PAT_X_ASSUM ‘h = z2’ (simp o wrap o SYM) \\
     STRIP_TAC (* P @* Ns2'' -h->* ... *) \\
     qabbrev_tac ‘xs2 = SNOC h zs2’ \\ (* suffix of L *)
     Know ‘IS_SUFFIX L xs2’
     >- (‘L = SNOC h L'’
           by ASM_SIMP_TAC std_ss [Abbr ‘L'’, Abbr ‘h’, SNOC_LAST_FRONT] \\
         POP_ORW \\
         simp [IS_SUFFIX, Abbr ‘xs2’]) >> DISCH_TAC \\
    ‘ALL_DISTINCT xs2’ by PROVE_TAC [IS_SUFFIX_ALL_DISTINCT] \\
     Know ‘LAMl vs2 (P' @* Ns2'') -h->*
           LAMl vs2 (LAMl zs2 (LAM h (VAR h @* Ns2'' @* MAP VAR zs2)))’
     >- simp [hreduce_LAMl] \\
     Q.PAT_X_ASSUM ‘P' @* Ns2'' -h->* _’ K_TAC \\
     REWRITE_TAC [GSYM LAMl_APPEND, GSYM appstar_APPEND] \\
     qabbrev_tac ‘Ns2x = Ns2'' ++ MAP VAR zs2’ \\
     REWRITE_TAC [GSYM LAMl_SNOC] \\
     qabbrev_tac ‘zs2' = SNOC h (vs2 ++ zs2)’ \\
     STRIP_TAC \\
     Know ‘W' -h->* LAMl zs2' (VAR h @* Ns2x)’
     >- PROVE_TAC [hreduce_TRANS] \\
     POP_ASSUM K_TAC >> STRIP_TAC \\
     Know ‘LAMl zs2' (VAR h @* Ns2x) = W0'’
     >- (‘hnf (LAMl zs2' (VAR h @* Ns2x))’ by rw [hnf_appstar] \\
         METIS_TAC [principal_hnf_thm']) >> DISCH_TAC \\
     Know ‘LENGTH zs2' = n4’
     >- (Q.PAT_X_ASSUM ‘_ = n4’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) \\
         simp []) >> DISCH_TAC \\
     Know ‘SUC (d_max' j3) + n2 - m2 = n4’
     >- (POP_ASSUM (REWRITE_TAC o wrap o SYM) \\
         simp [Abbr ‘zs2'’]) >> DISCH_TAC \\
     Know ‘vs2 <<= vs4’
     >- (qunabbrevl_tac [‘vs2’, ‘vs4’] \\
         MATCH_MP_TAC RNEWS_prefix >> simp []) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n2'’ STRIP_ASSUME_TAC) \\
    ‘n2' = n2’ by rw [] \\
     Q.PAT_X_ASSUM ‘n2' <= n4’ MP_TAC \\
     Q.PAT_X_ASSUM ‘vs2 = TAKE n2' vs4’ (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
     POP_ORW >> NTAC 2 DISCH_TAC \\
    ‘zs2' = vs2 ++ xs2’ by simp [Abbr ‘zs2'’, Abbr ‘xs2’] \\
     qabbrev_tac ‘ys2 = DROP n2 vs4’ \\
    ‘ALL_DISTINCT ys2’ by simp [Abbr ‘ys2’, ALL_DISTINCT_DROP] \\
  (* Structure of W0:

     LAMl |<--------- vs3 --------->| VAR y3/y1'

     W -h->* LAMl vs3  (VAR y3  @* Ns3) (= W0)
           = LAMl vs1  (VAR y1' @* Ns1''), thus y1' = y3

           m3 = m1, n3 = n1

     Structure of W0':

     LAMl |<---(vs2)--- vs4 ---(ys2)---->| VAR y4 (= LAST vs4)
   --------------------------------------------------------------
          |<----------- zs2' ----------->|
     LAMl |<----vs2----->|<--- zs2 --->|h| VAR h @* Ns2x = Ns2'' ++ zs2
                         |<---- xs2 ---->|
             n4 = n2 + d_max' - m2 + 1
             m4 = LENGTH Ns2x = LENGTH Ns2'' + LENGTH zs2
                = m2 + d_max - m2 = d_max'

      (m1 + n1 =) d_max + n1 = m1 + n2 + d_max - m2 + 1 (= m3 + n4)
                          n1 = m1 + n2 - m2 + 1
                     m2 + n1 = m1 + n2 + 1 <=/=> m2 + n1 = m1 + n2
   *)
     Know ‘DISJOINT (set xs2) (set ys2)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs4’ \\
         reverse CONJ_TAC >- simp [LIST_TO_SET_DROP, Abbr ‘ys2’] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set L’ >> art [] \\
         MATCH_MP_TAC LIST_TO_SET_SUFFIX >> art []) >> DISCH_TAC \\
    ‘LENGTH xs2 = LENGTH ys2’ by simp [Abbr ‘xs2’, Abbr ‘ys2’] \\
     Know ‘LAMl vs4 (VAR y4 @* Ns4) = LAMl zs2' (VAR h @* Ns2x)’
     >- rw [] \\
    ‘vs4 = vs2 ++ ys2’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
     Q.PAT_X_ASSUM ‘zs2' = _’ (ONCE_REWRITE_TAC o wrap) \\
     simp [LAMl_APPEND] \\
     qabbrev_tac ‘t = VAR h @* Ns2x’ \\
  (* applying LAMl_ALPHA_ssub *)
     qabbrev_tac ‘pm2 = fromPairs xs2 (MAP VAR ys2)’ \\
  (* NOTE: The following disjointness hold for names from different rows *)
     Know ‘DISJOINT (set vs) (set ys2)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs4’ >> simp [Abbr ‘ys2’, LIST_TO_SET_DROP] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs0’ >> art [] \\
         qunabbrevl_tac [‘vs0’, ‘vs4’] \\
         MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’]) >> DISCH_TAC \\
     Know ‘DISJOINT (set ys) (set ys2)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs4’ >> simp [Abbr ‘ys2’, LIST_TO_SET_DROP] \\
         qunabbrevl_tac [‘ys’, ‘vs4’] \\
         MATCH_MP_TAC DISJOINT_RNEWS \\
        ‘0 < LENGTH q’ by rw [LENGTH_NON_NIL] \\
         simp [Abbr ‘r1’]) >> DISCH_TAC \\
     Know ‘LAMl xs2 t = LAMl ys2 (pm2 ' t)’
     >- (simp [Abbr ‘pm2’, fromPairs_def] \\
         MATCH_MP_TAC LAMl_ALPHA_ssub >> art [] \\
      (* goal: DISJOINT (set ys2) (set xs2 UNION FV t) *)
         simp [DISJOINT_UNION'] \\
         CONJ_TAC >- rw [Once DISJOINT_SYM] \\
         simp [Abbr ‘t’, Abbr ‘Ns2x’, appstar_APPEND, FV_appstar_MAP_VAR] \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set xs2’ >> art [] \\
             simp [Abbr ‘xs2’, LIST_TO_SET_SNOC] \\
             SET_TAC []) \\
         simp [FV_appstar] \\
         CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘DISJOINT (set xs2) (set ys2)’ MP_TAC \\
             rw [Abbr ‘xs2’, LIST_TO_SET_SNOC, DISJOINT_ALT]) \\
         simp [MEM_EL] >> rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘_ = FV x’ (REWRITE_TAC o wrap) >> POP_ORW \\
         rename1 ‘i < m2’ >> POP_ASSUM MP_TAC \\
         simp [Abbr ‘Ns2''’, EL_MAP] >> DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘FV (EL i Ns2')’ \\
         reverse CONJ_TAC
         >- (MP_TAC (Q.SPECL [‘ss’, ‘EL i Ns2'’] FV_ISUB_upperbound) \\
             simp [EL_MAP, Abbr ‘Ns2'’]) \\
         simp [Abbr ‘Ns2'’, EL_listpm, Abbr ‘pm’, REVERSE_ZIP] \\
      (* applying FV_tpm_disjoint *)
         ONCE_REWRITE_TAC [DISJOINT_SYM] \\
         MATCH_MP_TAC FV_tpm_disjoint \\
         simp [ALL_DISTINCT_REVERSE] \\
      (* goal: DISJOINT (set ys2) (FV (EL i Ns2)) *)
         Know ‘FV N0' SUBSET X UNION RANK r1’
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV N'’ >> art [] \\
             qunabbrev_tac ‘N0'’ \\
             MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) >> DISCH_TAC \\
      (* applying FV_subterm_lemma *)
         Know ‘FV (EL i Ns2) SUBSET FV N' UNION set vs2’
         >- (MATCH_MP_TAC FV_subterm_lemma \\
             qexistsl_tac [‘X’, ‘r1’, ‘N0'’, ‘n2’, ‘m2’, ‘N1'’] >> simp []) \\
         DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV N' UNION set vs2’ >> art [] \\
         REWRITE_TAC [DISJOINT_UNION'] \\
         reverse CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs4’ MP_TAC \\
            ‘vs4 = vs2 ++ ys2’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
             simp [ALL_DISTINCT_APPEND', Once DISJOINT_SYM]) \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘X UNION RANK r1’ >> art [] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs4’ \\
         reverse CONJ_TAC
         >- (‘vs4 = vs2 ++ ys2’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
             simp [SUBSET_DEF]) \\
         simp [DISJOINT_UNION'] \\
         qunabbrev_tac ‘vs4’ \\
         MATCH_MP_TAC DISJOINT_RNEWS_RANK' >> art []) >> Rewr' \\
    ‘FDOM pm2 = set xs2’ by simp [Abbr ‘pm2’, FDOM_fromPairs] \\
    ‘MEM h xs2’ by simp [Abbr ‘xs2’, LIST_TO_SET_SNOC] \\
     simp [Abbr ‘t’, ssub_appstar] \\
     Know ‘pm2 ' h = VAR (LAST ys2)’
     >- (‘h = LAST xs2’ by rw [Abbr ‘xs2’, LAST_SNOC] >> POP_ORW \\
         ‘xs2 <> []’ by simp [Abbr ‘xs2’] \\
         ‘ys2 <> []’ by METIS_TAC [LENGTH_NON_NIL] \\
         simp [Abbr ‘pm2’, LAST_EL] \\
         qabbrev_tac ‘j4 = PRE (LENGTH ys2)’ \\
        ‘0 < LENGTH ys2’ by rw [LENGTH_NON_NIL] \\
        ‘j4 < LENGTH ys2’ by rw [Abbr ‘j4’] \\
        ‘VAR (EL j4 ys2) = EL j4 (MAP VAR ys2)’ by simp [EL_MAP] >> POP_ORW \\
         MATCH_MP_TAC fromPairs_FAPPLY_EL >> simp []) >> Rewr' \\
     Q.PAT_X_ASSUM ‘_ = W1'’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [] \\
     Know ‘LAST ys2 = LAST vs4’
     >- (‘vs4 = vs2 ++ ys2’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
         ‘xs2 <> []’ by simp [Abbr ‘xs2’] \\
         ‘ys2 <> []’ by METIS_TAC [LENGTH_NON_NIL] \\
         rw [LAST_APPEND_NOT_NIL]) >> Rewr' \\
     STRIP_TAC (* y4 = LAST vs4, etc. *) \\
  (* W -h->* LAMl vs3  (VAR y3 @* Ns3) = LAMl vs1 (VAR y1' @* Ns1'')

     Now we show that n1/n3 is strictly smaller than n4. This is only possible
     after using ‘subterm_length’ when constructing the permutator ‘P’:

      LENGTH zs2 = d_max - m2             (assumption)
      d_max = d + n_max >= m2 + n1        (worst case: d = m2)
   => LENGTH zs2 >= m2 + n1 - m2 = n1     (worst case: LENGTH zs2 = n1)
   => n4 = n2 + LENGTH zs2 + 1 > n1       (worst case: n2 = 0 and n4 = n1 + 1)

     Then, y3 is at most another variable in ROW r1. While y4 is LAST v4, thus
     cannot be the same with y3 since ‘ALL_DISTINCT vs4’.
   *)
     Know ‘n1 <= n_max’ (* n1 = LAMl_size N0 *)
     >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_length (M j1) q’ \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC subterm_length_inclusive \\
             Q.EXISTS_TAC ‘p’ >> simp []) \\
         qunabbrevl_tac [‘n1’, ‘N0’] \\
        ‘N = subterm' X (M j1) q r’ by rw [] >> POP_ORW \\
         MATCH_MP_TAC subterm_length_last >> simp []) >> DISCH_TAC \\
     Know ‘n1 < n4’
     >- (Q_TAC (TRANS_TAC LESS_EQ_LESS_TRANS) ‘n_max’ >> art [] \\
         Q.PAT_X_ASSUM ‘SUC (d_max' j3) + n2 - m2 = n4’
           (REWRITE_TAC o wrap o SYM) \\
         Q_TAC (TRANS_TAC LESS_EQ_LESS_TRANS) ‘d_max' j3 + n2 - m2’ \\
         simp [Abbr ‘d_max’, Abbr ‘d_max'’]) >> DISCH_TAC \\
  (* applying subterm_headvar_lemma' on W *)
     Know ‘hnf_headvar W1 IN FV W UNION set vs3’
     >- (MATCH_MP_TAC subterm_headvar_lemma' \\
         qexistsl_tac [‘X’, ‘r1’, ‘W0’, ‘n3’] >> simp []) \\
     Know ‘hnf_headvar W1 = y3’
     >- (Q.PAT_X_ASSUM ‘_ = W1’ (REWRITE_TAC o wrap o SYM) \\
         simp []) >> Rewr' >> art [] (* y3 -> y1' *) \\
     DISCH_TAC \\
  (* NOTE: FV W SUBSET X UNION RANK r1 *)
     qabbrev_tac ‘X' = X UNION RANK r1’ \\
     Know ‘y1' IN X' UNION set vs3’
     >- (Q.PAT_X_ASSUM ‘y1' IN _’ MP_TAC \\
         Q.PAT_X_ASSUM ‘FV W SUBSET _’ MP_TAC \\
         SET_TAC []) \\
     Q.PAT_X_ASSUM ‘y1' IN _’ K_TAC >> DISCH_TAC \\
     qunabbrev_tac ‘X'’ \\
    ‘0 < n4 /\ vs4 <> []’ by simp [GSYM LENGTH_NON_NIL] \\
     simp [LAST_EL] \\
     Q.PAT_X_ASSUM ‘y1' IN _’ MP_TAC >> simp [IN_UNION] \\
     STRIP_TAC >| (* 3 subgoals *)
     [ (* goal 1 (of 3): y1' IN X *)
       SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE []) \\
       Know ‘MEM y1' vs4’
       >- (POP_ORW >> simp [EL_MEM]) >> DISCH_TAC \\
       Q.PAT_X_ASSUM ‘DISJOINT (set vs4) X’ MP_TAC \\
       simp [DISJOINT_ALT'] \\
       Q.EXISTS_TAC ‘y1'’ >> art [],
       (* goal 2 (of 3): y1' IN RANK r1 *)
       SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE []) \\
       Know ‘MEM y1' vs4’
       >- (POP_ORW >> simp [EL_MEM]) >> DISCH_TAC \\
       Know ‘DISJOINT (set vs4) (RANK r1)’
       >- simp [Abbr ‘vs4’, DISJOINT_RNEWS_RANK'] \\
       simp [DISJOINT_ALT] \\
       Q.EXISTS_TAC ‘y1'’ >> art [],
       (* goal 3 (of 3): MEM y1' vs3 *)
       Know ‘vs3 <<= vs4’
       >- (qunabbrevl_tac [‘vs3’, ‘vs4’] \\
           MATCH_MP_TAC RNEWS_prefix >> simp []) \\
       simp [IS_PREFIX_APPEND] \\
       DISCH_THEN (Q.X_CHOOSE_THEN ‘ls’ STRIP_ASSUME_TAC) \\
       Know ‘LENGTH ls = n4 - n1’
       >- (POP_ASSUM (MP_TAC o AP_TERM “LENGTH :string list -> num”) \\
           simp []) >> DISCH_TAC \\
      ‘ls <> []’ by simp [GSYM LENGTH_NON_NIL] \\
       Know ‘EL (PRE n4) vs4 = LAST ls’
       >- (Q.PAT_X_ASSUM ‘vs4 = vs3 ++ ls’ (REWRITE_TAC o wrap) \\
           simp [EL_APPEND2, LAST_EL, PRE_SUB]) >> Rewr' \\
       SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE []) \\
       Know ‘MEM y1' ls’
       >- (POP_ORW >> simp [MEM_LAST_NOT_NIL]) >> DISCH_TAC \\
       Q.PAT_X_ASSUM ‘ALL_DISTINCT vs4’ MP_TAC \\
       Q.PAT_X_ASSUM ‘vs4 = vs3 ++ ls’ (REWRITE_TAC o wrap) \\
       simp [ALL_DISTINCT_APPEND] \\
       DISJ2_TAC >> Q.EXISTS_TAC ‘y1'’ >> art [] ])
 (* Case 3 (of 4): (almost) symmetric with previous Case 2 *)
 >- (PRINT_TAC "stage work on subtree_equiv_lemma" \\
     Q.PAT_X_ASSUM ‘~(y1' NOTIN DOM ss)’ MP_TAC >> simp [ISUB_VAR_FRESH'] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘j3’ STRIP_ASSUME_TAC) \\
    ‘(LEAST j. y j = y1') = f j3’ by rw [] >> POP_ORW \\
     ONCE_REWRITE_TAC [TAUT ‘p /\ q ==> r <=> q ==> p ==> r’] >> STRIP_TAC \\
    ‘hnf (LAMl vs2 (VAR y2' @* Ns2''))’ by rw [hnf_appstar] \\
    ‘LAMl vs2 (VAR y2' @* Ns2'') = W0'’ by METIS_TAC [principal_hnf_thm'] \\
    ‘LAMl_size W0' = n2’ by rw [LAMl_size_hnf] \\
    ‘n4 = n2’ by PROVE_TAC [] \\
     Know ‘y4 = y2' /\ Ns2'' = Ns4’
     >- (Q.PAT_X_ASSUM ‘LAMl vs4 _ = W0'’ MP_TAC \\
         Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) >> simp [] \\
         Q.PAT_X_ASSUM ‘_ = W1'’ (REWRITE_TAC o wrap o SYM) >> fs []) \\
     STRIP_TAC >> simp [] \\
  (* NOTE: The proof completes if we can just show ‘y3 <> y4’. *)
     qabbrev_tac ‘X' = set vs3 UNION FV W1 UNION
                       BIGUNION (IMAGE FV (set Ns1''))’ \\
    ‘FINITE X'’ by rw [Abbr ‘X'’] \\
     qabbrev_tac ‘d' = MAX n3 (SUC (d_max' j3))’ \\
     Q_TAC (NEWS_TAC (“L :string list”, “d' :num”)) ‘X'’ \\
    ‘d_max' j3 < LENGTH L /\ n3 <= LENGTH L’ by simp [Abbr ‘d'’, MAX_LE] \\
     Know ‘DISJOINT (set L) (set vs1) /\
           DISJOINT (set L) (set vs3)’
     >- (rw [Abbr ‘L’, Abbr ‘vs1’, Abbr ‘vs3’] (* 2 subgoals, same tactics *) \\
         MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’]) >> STRIP_TAC \\
     Q.PAT_X_ASSUM ‘FINITE X'’ K_TAC \\
     Q.PAT_X_ASSUM ‘DISJOINT (set L) X'’ MP_TAC \\
     qunabbrev_tac ‘X'’ \\
     DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [DISJOINT_UNION']) \\
     STRIP_TAC (* W -h->* ... *) \\
    ‘m1 <= d_max' j3’ by simp [Abbr ‘d_max'’] \\
     MP_TAC (Q.SPECL [‘Ns1''’, ‘d_max + f (j3 :num)’, ‘L’]
                     hreduce_permutator_shared) >> simp [] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘zs1’ (Q.X_CHOOSE_THEN ‘z1’ STRIP_ASSUME_TAC)) \\
     qabbrev_tac ‘P' = P (f j3)’ \\
     Q.PAT_X_ASSUM ‘P' @* Ns1'' -h->* _’ MP_TAC \\
     qabbrev_tac ‘h = LAST L’ (* the new shared head variable *) \\
     qabbrev_tac ‘L' = FRONT L’ \\
    ‘L <> []’ by rw [GSYM LENGTH_NON_NIL] \\
     Q.PAT_X_ASSUM ‘IS_SUFFIX L _’ MP_TAC \\
    ‘L = SNOC h L'’ by ASM_SIMP_TAC std_ss [Abbr ‘L'’, Abbr ‘h’, SNOC_LAST_FRONT] \\
     POP_ORW \\
     simp [IS_SUFFIX] >> STRIP_TAC \\
     Q.PAT_X_ASSUM ‘h = z1’ (simp o wrap o SYM) \\
     STRIP_TAC (* P @* Ns1'' -h->* ... *) \\
     qabbrev_tac ‘xs1 = SNOC h zs1’ \\ (* suffix of L *)
     Know ‘IS_SUFFIX L xs1’
     >- (‘L = SNOC h L'’
           by ASM_SIMP_TAC std_ss [Abbr ‘L'’, Abbr ‘h’, SNOC_LAST_FRONT] \\
         POP_ORW >> simp [IS_SUFFIX, Abbr ‘xs1’]) >> DISCH_TAC \\
    ‘ALL_DISTINCT xs1’ by PROVE_TAC [IS_SUFFIX_ALL_DISTINCT] \\
     Know ‘LAMl vs1 (P' @* Ns1'') -h->*
           LAMl vs1 (LAMl zs1 (LAM h (VAR h @* Ns1'' @* MAP VAR zs1)))’
     >- simp [hreduce_LAMl] \\
     Q.PAT_X_ASSUM ‘P' @* Ns1'' -h->* _’ K_TAC \\
     REWRITE_TAC [GSYM LAMl_APPEND, GSYM appstar_APPEND] \\
     qabbrev_tac ‘Ns1x = Ns1'' ++ MAP VAR zs1’ \\
     REWRITE_TAC [GSYM LAMl_SNOC] \\
     qabbrev_tac ‘zs1' = SNOC h (vs1 ++ zs1)’ >> STRIP_TAC \\
     Know ‘W -h->* LAMl zs1' (VAR h @* Ns1x)’
     >- PROVE_TAC [hreduce_TRANS] \\
     POP_ASSUM K_TAC >> STRIP_TAC \\
     Know ‘LAMl zs1' (VAR h @* Ns1x) = W0’
     >- (‘hnf (LAMl zs1' (VAR h @* Ns1x))’ by rw [hnf_appstar] \\
         METIS_TAC [principal_hnf_thm']) >> DISCH_TAC \\
     Know ‘LENGTH zs1' = n3’
     >- (Q.PAT_X_ASSUM ‘_ = n3’ (REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘_ = W0’ (REWRITE_TAC o wrap o SYM) \\
         simp []) >> DISCH_TAC \\
  (* abandon ‘y1 <> y2 \/ m2 + n1 <> m1 + n2’ *)
     DISCH_THEN K_TAC >> DISJ1_TAC \\
     Know ‘SUC (d_max' j3) + n1 - m1 = n3’
     >- (POP_ASSUM (REWRITE_TAC o wrap o SYM) \\
         simp [Abbr ‘zs1'’]) >> DISCH_TAC \\
     Know ‘vs1 <<= vs3’
     >- (qunabbrevl_tac [‘vs1’, ‘vs3’] \\
         MATCH_MP_TAC RNEWS_prefix >> simp []) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n1'’ STRIP_ASSUME_TAC) \\
    ‘n1' = n1’ by rw [] \\
     Q.PAT_X_ASSUM ‘n1' <= n3’ MP_TAC \\
     Q.PAT_X_ASSUM ‘vs1 = TAKE n1' vs3’ (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
     POP_ORW >> NTAC 2 DISCH_TAC \\
    ‘zs1' = vs1 ++ xs1’ by simp [Abbr ‘zs1'’, Abbr ‘xs1’] \\
     qabbrev_tac ‘ys1 = DROP n1 vs3’ \\
    ‘ALL_DISTINCT ys1’ by simp [Abbr ‘ys1’, ALL_DISTINCT_DROP] \\
  (* Structure of W0:

     LAMl |<---(vs1)--- vs3 ---(ys1)---->| VAR y3 (= LAST vs3) in ROW r1
   --------------------------------------------------------------
          |<----------- zs1' ----------->|
     LAMl |<----vs1----->|<--- zs1 --->|h| VAR h @* Ns1x = Ns1'' ++ zs1
                         |<---- xs1 ---->|

     LAMl vs3  (VAR y3 @* Ns3) = W0
     LAMl zs1' (VAR h @* Ns1x) = W0
   *)
     Know ‘DISJOINT (set xs1) (set ys1)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ \\
         reverse CONJ_TAC >- simp [LIST_TO_SET_DROP, Abbr ‘ys1’] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set L’ >> art [] \\
         MATCH_MP_TAC LIST_TO_SET_SUFFIX >> art []) >> DISCH_TAC \\
    ‘LENGTH xs1 = LENGTH ys1’ by simp [Abbr ‘xs1’, Abbr ‘ys1’] \\
     Know ‘LAMl vs3 (VAR y3 @* Ns3) = LAMl zs1' (VAR h @* Ns1x)’ >- rw [] \\
    ‘vs3 = vs1 ++ ys1’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
     Q.PAT_X_ASSUM ‘zs1' = _’ (ONCE_REWRITE_TAC o wrap) \\
     simp [LAMl_APPEND] \\
     qabbrev_tac ‘t = VAR h @* Ns1x’ \\
  (* applying LAMl_ALPHA_ssub *)
     qabbrev_tac ‘pm1 = fromPairs xs1 (MAP VAR ys1)’ \\
  (* NOTE: The following disjointness hold for names from different rows *)
     Know ‘DISJOINT (set vs) (set ys1)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ >> simp [Abbr ‘ys1’, LIST_TO_SET_DROP] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs0’ >> art [] \\
         qunabbrevl_tac [‘vs0’, ‘vs3’] \\
         MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’]) >> DISCH_TAC \\
     Know ‘DISJOINT (set ys) (set ys1)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ >> simp [Abbr ‘ys1’, LIST_TO_SET_DROP] \\
         qunabbrevl_tac [‘ys’, ‘vs3’] \\
         MATCH_MP_TAC DISJOINT_RNEWS \\
        ‘0 < LENGTH q’ by rw [LENGTH_NON_NIL] \\
         simp [Abbr ‘r1’]) >> DISCH_TAC \\
     Know ‘LAMl xs1 t = LAMl ys1 (pm1 ' t)’
     >- (simp [Abbr ‘pm1’, fromPairs_def] \\
         MATCH_MP_TAC LAMl_ALPHA_ssub >> art [] \\
         simp [DISJOINT_UNION'] \\
         CONJ_TAC >- rw [Once DISJOINT_SYM] \\
         simp [Abbr ‘t’, Abbr ‘Ns1x’, appstar_APPEND, FV_appstar_MAP_VAR] \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set xs1’ >> art [] \\
             simp [Abbr ‘xs1’, LIST_TO_SET_SNOC] >> SET_TAC []) \\
         simp [FV_appstar] \\
         CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘DISJOINT (set xs1) (set ys1)’ MP_TAC \\
             rw [Abbr ‘xs1’, LIST_TO_SET_SNOC, DISJOINT_ALT]) \\
         simp [MEM_EL] >> rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘_ = FV x’ (REWRITE_TAC o wrap) >> POP_ORW \\
         rename1 ‘i < m1’ >> POP_ASSUM MP_TAC \\
         simp [Abbr ‘Ns1''’, EL_MAP] >> DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘FV (EL i Ns1')’ \\
         reverse CONJ_TAC
         >- (MP_TAC (Q.SPECL [‘ss’, ‘EL i Ns1'’] FV_ISUB_upperbound) \\
             simp [EL_MAP, Abbr ‘Ns1'’]) \\
         simp [Abbr ‘Ns1'’, EL_listpm, Abbr ‘pm’, REVERSE_ZIP] \\
      (* applying FV_tpm_disjoint *)
         ONCE_REWRITE_TAC [DISJOINT_SYM] \\
         MATCH_MP_TAC FV_tpm_disjoint \\
         simp [ALL_DISTINCT_REVERSE] \\
      (* goal: DISJOINT (set ys1) (FV (EL i Ns1)) *)
         Know ‘FV N0 SUBSET X UNION RANK r1’
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV N’ >> art [] \\
             qunabbrev_tac ‘N0’ \\
             MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) >> DISCH_TAC \\
      (* applying FV_subterm_lemma *)
         Know ‘FV (EL i Ns1) SUBSET FV N UNION set vs1’
         >- (MATCH_MP_TAC FV_subterm_lemma \\
             qexistsl_tac [‘X’, ‘r1’, ‘N0’, ‘n1’, ‘m1’, ‘N1’] >> simp []) \\
         DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV N UNION set vs1’ >> art [] \\
         REWRITE_TAC [DISJOINT_UNION'] \\
         reverse CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs3’ MP_TAC \\
            ‘vs3 = vs1 ++ ys1’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
             simp [ALL_DISTINCT_APPEND', Once DISJOINT_SYM]) \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘X UNION RANK r1’ >> art [] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs3’ \\
         reverse CONJ_TAC
         >- (‘vs3 = vs1 ++ ys1’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
             simp [SUBSET_DEF]) \\
         simp [DISJOINT_UNION'] \\
         qunabbrev_tac ‘vs3’ \\
         MATCH_MP_TAC DISJOINT_RNEWS_RANK' >> art []) >> Rewr' \\
    ‘FDOM pm1 = set xs1’ by simp [Abbr ‘pm1’, FDOM_fromPairs] \\
    ‘MEM h xs1’ by simp [Abbr ‘xs1’, LIST_TO_SET_SNOC] \\
     simp [Abbr ‘t’, ssub_appstar] \\
     Know ‘pm1 ' h = VAR (LAST ys1)’
     >- (‘h = LAST xs1’ by rw [Abbr ‘xs1’, LAST_SNOC] >> POP_ORW \\
         ‘xs1 <> []’ by simp [Abbr ‘xs1’] \\
         ‘ys1 <> []’ by METIS_TAC [LENGTH_NON_NIL] \\
         simp [Abbr ‘pm1’, LAST_EL] \\
         qabbrev_tac ‘j4 = PRE (LENGTH ys1)’ \\
        ‘0 < LENGTH ys1’ by rw [LENGTH_NON_NIL] \\
        ‘j4 < LENGTH ys1’ by rw [Abbr ‘j4’] \\
        ‘VAR (EL j4 ys1) = EL j4 (MAP VAR ys1)’ by simp [EL_MAP] >> POP_ORW \\
         MATCH_MP_TAC fromPairs_FAPPLY_EL >> simp []) >> Rewr' \\
     Q.PAT_X_ASSUM ‘_ = W1’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [] \\
     Know ‘LAST ys1 = LAST vs3’
     >- (‘vs3 = vs1 ++ ys1’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
         ‘xs1 <> []’ by simp [Abbr ‘xs1’] \\
         ‘ys1 <> []’ by METIS_TAC [LENGTH_NON_NIL] \\
         rw [LAST_APPEND_NOT_NIL]) >> Rewr' \\
     STRIP_TAC (* y4 = LAST vs4, etc. *) \\
  (* stage work *)
     Know ‘n2 <= n_max’ (* n2 = LAMl_size N0' *)
     >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_length (M j2) q’ \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC subterm_length_inclusive \\
             Q.EXISTS_TAC ‘p’ >> simp []) \\
         qunabbrevl_tac [‘n2’, ‘N0'’] \\
        ‘N' = subterm' X (M j2) q r’ by rw [] >> POP_ORW \\
         MATCH_MP_TAC subterm_length_last >> simp []) >> DISCH_TAC \\
     Know ‘n2 < n3’
     >- (Q_TAC (TRANS_TAC LESS_EQ_LESS_TRANS) ‘n_max’ >> art [] \\
         Q.PAT_X_ASSUM ‘SUC (d_max' j3) + n1 - m1 = n3’
           (REWRITE_TAC o wrap o SYM) \\
         Q_TAC (TRANS_TAC LESS_EQ_LESS_TRANS) ‘d_max' j3 + n1 - m1’ \\
         simp [Abbr ‘d_max’, Abbr ‘d_max'’]) >> DISCH_TAC \\
  (* applying subterm_headvar_lemma' on W *)
     Know ‘hnf_headvar W1' IN FV W' UNION set vs4’
     >- (MATCH_MP_TAC subterm_headvar_lemma' \\
         qexistsl_tac [‘X’, ‘r1’, ‘W0'’, ‘n4’] >> simp []) \\
     Know ‘hnf_headvar W1' = y4’
     >- (Q.PAT_X_ASSUM ‘_ = W1'’ (REWRITE_TAC o wrap o SYM) \\
         simp []) >> Rewr' >> art [] (* y3 -> y1' *) \\
     DISCH_TAC \\
  (* NOTE: FV W' SUBSET X UNION RANK r1 *)
     qabbrev_tac ‘X' = X UNION RANK r1’ \\
     Know ‘y2' IN X' UNION set vs4’
     >- (Q.PAT_X_ASSUM ‘y2' IN _’ MP_TAC \\
         Q.PAT_X_ASSUM ‘FV W' SUBSET _’ MP_TAC \\
         SET_TAC []) \\
     Q.PAT_X_ASSUM ‘y2' IN _’ K_TAC >> DISCH_TAC \\
     qunabbrev_tac ‘X'’ \\
    ‘0 < n3 /\ vs3 <> []’ by simp [GSYM LENGTH_NON_NIL] \\
     simp [LAST_EL] \\
     Q.PAT_X_ASSUM ‘y2' IN _’ MP_TAC >> simp [IN_UNION] \\
     STRIP_TAC >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [Once EQ_SYM_EQ]) \\
       Know ‘MEM y2' vs3’
       >- (POP_ORW >> simp [EL_MEM]) >> DISCH_TAC \\
       Q.PAT_X_ASSUM ‘DISJOINT (set vs3) X’ MP_TAC \\
       simp [DISJOINT_ALT'] >> Q.EXISTS_TAC ‘y2'’ >> art [],
       (* goal 2 (of 3) *)
       SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [Once EQ_SYM_EQ]) \\
       Know ‘MEM y2' vs3’
       >- (POP_ORW >> simp [EL_MEM]) >> DISCH_TAC \\
       Know ‘DISJOINT (set vs3) (RANK r1)’
       >- simp [Abbr ‘vs3’, DISJOINT_RNEWS_RANK'] \\
       simp [DISJOINT_ALT] \\
       Q.EXISTS_TAC ‘y2'’ >> art [],
       (* goal 3 (of 3) *)
       Know ‘vs4 <<= vs3’
       >- (qunabbrevl_tac [‘vs3’, ‘vs4’] \\
           MATCH_MP_TAC RNEWS_prefix >> simp []) \\
       simp [IS_PREFIX_APPEND] \\
       DISCH_THEN (Q.X_CHOOSE_THEN ‘ls’ STRIP_ASSUME_TAC) \\
       Know ‘LENGTH ls = n3 - n2’
       >- (POP_ASSUM (MP_TAC o AP_TERM “LENGTH :string list -> num”) \\
           simp []) >> DISCH_TAC \\
      ‘ls <> []’ by simp [GSYM LENGTH_NON_NIL] \\
       Know ‘EL (PRE n3) vs3 = LAST ls’
       >- (Q.PAT_X_ASSUM ‘vs3 = vs4 ++ ls’ (REWRITE_TAC o wrap) \\
           simp [EL_APPEND2, LAST_EL, PRE_SUB]) >> Rewr' \\
       SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [Once EQ_SYM_EQ]) \\
       Know ‘MEM y2' ls’
       >- (POP_ORW >> simp [MEM_LAST_NOT_NIL]) >> DISCH_TAC \\
       Q.PAT_X_ASSUM ‘ALL_DISTINCT vs3’ MP_TAC \\
       Q.PAT_X_ASSUM ‘vs3 = vs4 ++ ls’ (REWRITE_TAC o wrap) \\
       simp [ALL_DISTINCT_APPEND] \\
       DISJ2_TAC >> Q.EXISTS_TAC ‘y2'’ >> art [] ])
 (* Case 4 (of 4): hardest *)
 >> PRINT_TAC "stage work on subtree_equiv_lemma"
 >> NTAC 2 (POP_ASSUM (MP_TAC o REWRITE_RULE []))
 >> simp []
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘j3’ STRIP_ASSUME_TAC)
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘j4’ STRIP_ASSUME_TAC)
 >> qabbrev_tac ‘X' = set vs3 UNION set vs4 UNION
                      FV W1 UNION FV W1' UNION
                      BIGUNION (IMAGE FV (set Ns1'')) UNION
                      BIGUNION (IMAGE FV (set Ns2''))’
 >> ‘FINITE X'’ by rw [Abbr ‘X'’]
 >> qabbrev_tac ‘d' = MAX (MAX n3 n4)
                          (MAX (SUC (d_max' j3))
                               (SUC (d_max' j4)))’
 >> Q_TAC (NEWS_TAC (“L :string list”, “d' :num”)) ‘X'’
 >> ‘n3 <= LENGTH L /\ n4 <= LENGTH L /\
     d_max' j3 < LENGTH L /\ d_max' j4 < LENGTH L’ by simp [Abbr ‘d'’, MAX_LE]
 >> Know ‘DISJOINT (set L) (set vs1) /\
          DISJOINT (set L) (set vs2) /\
          DISJOINT (set L) (set vs3) /\
          DISJOINT (set L) (set vs4)’
 >- (rw [Abbr ‘L’, Abbr ‘vs1’, Abbr ‘vs2’, Abbr ‘vs3’, Abbr ‘vs4’] \\
     MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’])
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘FINITE X'’ K_TAC
 >> Q.PAT_X_ASSUM ‘DISJOINT (set L) X'’ MP_TAC
 >> qunabbrev_tac ‘X'’
 >> DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [DISJOINT_UNION'])
 >> simp [] (* VAR (y j3) ISUB ss = P (f j3), etc. *)
 >> STRIP_TAC (* W -h->* ... *)
 >> ‘m1 <= d_max' j3 /\ m2 <= d_max' j4’ by simp [Abbr ‘d_max'’]
 (* applying hreduce_permutator_shared *)
 >> MP_TAC (Q.SPECL [‘Ns1''’, ‘d_max + f (j3 :num)’, ‘L’] hreduce_permutator_shared)
 >> simp []
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘zs1’ (Q.X_CHOOSE_THEN ‘z1’ STRIP_ASSUME_TAC))
 (* applying hreduce_permutator_shared again *)
 >> MP_TAC (Q.SPECL [‘Ns2''’, ‘d_max + f (j4 :num)’, ‘L’] hreduce_permutator_shared)
 >> simp []
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘zs2’ (Q.X_CHOOSE_THEN ‘z2’ STRIP_ASSUME_TAC))
 >> qabbrev_tac ‘P3 = P (f j3)’
 >> qabbrev_tac ‘P4 = P (f j4)’
 >> Q.PAT_X_ASSUM ‘P3 @* Ns1'' -h->* _’ MP_TAC
 >> Q.PAT_X_ASSUM ‘P4 @* Ns2'' -h->* _’ MP_TAC
 >> qabbrev_tac ‘h = LAST L’ (* The new shared head variable *)
 >> qabbrev_tac ‘L' = FRONT L’
 >> ‘L <> []’ by rw [GSYM LENGTH_NON_NIL]
 >> NTAC 2 (Q.PAT_X_ASSUM ‘IS_SUFFIX L _’ MP_TAC)
 >> ‘L = SNOC h L'’ by ASM_SIMP_TAC std_ss [Abbr ‘L'’, Abbr ‘h’, SNOC_LAST_FRONT]
 >> POP_ORW >> simp [IS_SUFFIX]
 >> NTAC 2 STRIP_TAC
 >> Q.PAT_X_ASSUM ‘z1 = z2’ (simp o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘h  = z1’ (simp o wrap o SYM)
 >> NTAC 2 DISCH_TAC
 >> qabbrev_tac ‘xs1 = SNOC h zs1’ (* suffix of L *)
 >> qabbrev_tac ‘xs2 = SNOC h zs2’ (* suffix of L *)
 >> Know ‘IS_SUFFIX L xs1 /\ IS_SUFFIX L xs2’
 >- (‘L = SNOC h L'’
        by ASM_SIMP_TAC std_ss [Abbr ‘L'’, Abbr ‘h’, SNOC_LAST_FRONT] \\
     POP_ORW >> simp [IS_SUFFIX, Abbr ‘xs1’, Abbr ‘xs2’])
 >> STRIP_TAC
 >> ‘ALL_DISTINCT xs1 /\ ALL_DISTINCT xs2’ by PROVE_TAC [IS_SUFFIX_ALL_DISTINCT]
 >> Know ‘LAMl vs1 (P3 @* Ns1'') -h->*
          LAMl vs1 (LAMl zs1 (LAM h (VAR h @* Ns1'' @* MAP VAR zs1))) /\
          LAMl vs2 (P4 @* Ns2'') -h->*
          LAMl vs2 (LAMl zs2 (LAM h (VAR h @* Ns2'' @* MAP VAR zs2)))’
 >- simp [hreduce_LAMl]
 >> Q.PAT_X_ASSUM ‘P3 @* Ns1'' -h->* _’ K_TAC
 >> Q.PAT_X_ASSUM ‘P4 @* Ns2'' -h->* _’ K_TAC
 >> REWRITE_TAC [GSYM LAMl_APPEND, GSYM appstar_APPEND]
 >> qabbrev_tac ‘Ns1x = Ns1'' ++ MAP VAR zs1’
 >> qabbrev_tac ‘Ns2x = Ns2'' ++ MAP VAR zs2’
 >> REWRITE_TAC [GSYM LAMl_SNOC]
 >> qabbrev_tac ‘zs1' = SNOC h (vs1 ++ zs1)’
 >> qabbrev_tac ‘zs2' = SNOC h (vs2 ++ zs2)’
 >> STRIP_TAC
 >> Know ‘W  -h->* LAMl zs1' (VAR h @* Ns1x) /\
          W' -h->* LAMl zs2' (VAR h @* Ns2x)’
 >- PROVE_TAC [hreduce_TRANS]
 >> NTAC 2 (POP_ASSUM K_TAC) >> STRIP_TAC
 >> qunabbrevl_tac [‘P3’, ‘P4’]
 >> Know ‘LAMl zs1' (VAR h @* Ns1x) = W0 /\
          LAMl zs2' (VAR h @* Ns2x) = W0'’
 >- (‘hnf (LAMl zs1' (VAR h @* Ns1x)) /\ hnf (LAMl zs2' (VAR h @* Ns2x))’
       by rw [hnf_appstar] \\
     METIS_TAC [principal_hnf_thm'])
 >> STRIP_TAC
 >> Know ‘LENGTH zs1' = n3 /\ LENGTH zs2' = n4’
 >- (Q.PAT_X_ASSUM ‘_ = n3’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = n4’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = W0’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) >> simp [])
 >> STRIP_TAC
 (* key equations about n3 and n4, m3 and m4 *)
 >> Know ‘d_max' j3 = m3 /\ d_max' j4 = m4’
 >- (Q.PAT_X_ASSUM ‘_ = m3’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = m4’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = W0’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = W0'’ (REWRITE_TAC o wrap o SYM) \\
     simp [Abbr ‘Ns1x’, Abbr ‘Ns2x’])
 >> STRIP_TAC
 >> Know ‘SUC (d_max' j3) + n1 - m1 = n3 /\
          SUC (d_max' j4) + n2 - m2 = n4’
 >- (Q.PAT_X_ASSUM ‘_ = n3’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = n4’  (REWRITE_TAC o wrap o SYM) \\
     simp [Abbr ‘zs1'’, Abbr ‘zs2'’])
 >> simp [] >> STRIP_TAC
 (* stage work *)
 >> Know ‘LAST vs3 = y3’
 >- (Know ‘vs1 <<= vs3’
     >- (qunabbrevl_tac [‘vs1’, ‘vs3’] \\
         MATCH_MP_TAC RNEWS_prefix >> simp []) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n1'’ STRIP_ASSUME_TAC) \\
    ‘n1' = n1’ by rw [] \\
     Q.PAT_X_ASSUM ‘n1' <= n3’ MP_TAC \\
     Q.PAT_X_ASSUM ‘vs1 = TAKE n1' vs3’ (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
     POP_ORW >> NTAC 2 DISCH_TAC \\
    ‘vs1 ++ xs1 = zs1'’ by simp [Abbr ‘zs1'’, Abbr ‘xs1’] \\
     qabbrev_tac ‘ys1 = DROP n1 vs3’ \\
    ‘ALL_DISTINCT ys1’ by simp [Abbr ‘ys1’, ALL_DISTINCT_DROP] \\
     Know ‘DISJOINT (set xs1) (set ys1)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ \\
         reverse CONJ_TAC >- simp [LIST_TO_SET_DROP, Abbr ‘ys1’] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set L’ >> art [] \\
         MATCH_MP_TAC LIST_TO_SET_SUFFIX >> art []) >> DISCH_TAC \\
    ‘LENGTH xs1 = LENGTH ys1’ by simp [Abbr ‘xs1’, Abbr ‘ys1’] \\
     Know ‘LAMl vs3 (VAR y3 @* Ns3) = LAMl zs1' (VAR h @* Ns1x)’ >- rw [] \\
    ‘vs3 = vs1 ++ ys1’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
     Q.PAT_X_ASSUM ‘_ = zs1'’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [LAMl_APPEND] \\
     qabbrev_tac ‘t = VAR h @* Ns1x’ \\
  (* applying LAMl_ALPHA_ssub *)
     qabbrev_tac ‘pm1 = fromPairs xs1 (MAP VAR ys1)’ \\
  (* NOTE: The following disjointness hold for names from different rows *)
     Know ‘DISJOINT (set vs) (set ys1)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ >> simp [Abbr ‘ys1’, LIST_TO_SET_DROP] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs0’ >> art [] \\
         qunabbrevl_tac [‘vs0’, ‘vs3’] \\
         MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’]) >> DISCH_TAC \\
     Know ‘DISJOINT (set ys) (set ys1)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs3’ >> simp [Abbr ‘ys1’, LIST_TO_SET_DROP] \\
         qunabbrevl_tac [‘ys’, ‘vs3’] \\
         MATCH_MP_TAC DISJOINT_RNEWS \\
        ‘0 < LENGTH q’ by rw [LENGTH_NON_NIL] \\
         simp [Abbr ‘r1’]) >> DISCH_TAC \\
     Know ‘LAMl xs1 t = LAMl ys1 (pm1 ' t)’
     >- (simp [Abbr ‘pm1’, fromPairs_def] \\
         MATCH_MP_TAC LAMl_ALPHA_ssub >> art [] \\
         simp [DISJOINT_UNION'] \\
         CONJ_TAC >- rw [Once DISJOINT_SYM] \\
         simp [Abbr ‘t’, Abbr ‘Ns1x’, appstar_APPEND, FV_appstar_MAP_VAR] \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set xs1’ >> art [] \\
             simp [Abbr ‘xs1’, LIST_TO_SET_SNOC] >> SET_TAC []) \\
         simp [FV_appstar] \\
         CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘DISJOINT (set xs1) (set ys1)’ MP_TAC \\
             rw [Abbr ‘xs1’, LIST_TO_SET_SNOC, DISJOINT_ALT]) \\
         simp [MEM_EL] >> rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘_ = FV x’ (REWRITE_TAC o wrap) >> POP_ORW \\
         rename1 ‘i < m1’ >> POP_ASSUM MP_TAC \\
         simp [Abbr ‘Ns1''’, EL_MAP] >> DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘FV (EL i Ns1')’ \\
         reverse CONJ_TAC
         >- (MP_TAC (Q.SPECL [‘ss’, ‘EL i Ns1'’] FV_ISUB_upperbound) \\
             simp [EL_MAP, Abbr ‘Ns1'’]) \\
         simp [Abbr ‘Ns1'’, EL_listpm, Abbr ‘pm’, REVERSE_ZIP] \\
      (* applying FV_tpm_disjoint *)
         ONCE_REWRITE_TAC [DISJOINT_SYM] \\
         MATCH_MP_TAC FV_tpm_disjoint \\
         simp [ALL_DISTINCT_REVERSE] \\
      (* goal: DISJOINT (set ys1) (FV (EL i Ns1)) *)
         Know ‘FV N0 SUBSET X UNION RANK r1’
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV N’ >> art [] \\
             qunabbrev_tac ‘N0’ \\
             MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) >> DISCH_TAC \\
      (* applying FV_subterm_lemma *)
         Know ‘FV (EL i Ns1) SUBSET FV N UNION set vs1’
         >- (MATCH_MP_TAC FV_subterm_lemma \\
             qexistsl_tac [‘X’, ‘r1’, ‘N0’, ‘n1’, ‘m1’, ‘N1’] >> simp []) \\
         DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV N UNION set vs1’ >> art [] \\
         REWRITE_TAC [DISJOINT_UNION'] \\
         reverse CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs3’ MP_TAC \\
            ‘vs3 = vs1 ++ ys1’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
             simp [ALL_DISTINCT_APPEND', Once DISJOINT_SYM]) \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘X UNION RANK r1’ >> art [] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs3’ \\
         reverse CONJ_TAC
         >- (‘vs3 = vs1 ++ ys1’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
             simp [SUBSET_DEF]) \\
         simp [DISJOINT_UNION'] \\
         qunabbrev_tac ‘vs3’ \\
         MATCH_MP_TAC DISJOINT_RNEWS_RANK' >> art []) >> Rewr' \\
    ‘vs1 ++ ys1 = vs3’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
    ‘FDOM pm1 = set xs1’ by simp [Abbr ‘pm1’, FDOM_fromPairs] \\
    ‘MEM h xs1’ by simp [Abbr ‘xs1’, LIST_TO_SET_SNOC] \\
     simp [Abbr ‘t’, ssub_appstar] \\
     Know ‘pm1 ' h = VAR (LAST ys1)’
     >- (‘h = LAST xs1’ by rw [Abbr ‘xs1’, LAST_SNOC] >> POP_ORW \\
         ‘xs1 <> []’ by simp [Abbr ‘xs1’] \\
         ‘ys1 <> []’ by METIS_TAC [LENGTH_NON_NIL] \\
         simp [Abbr ‘pm1’, LAST_EL] \\
         qabbrev_tac ‘j5 = PRE (LENGTH ys1)’ \\
         ‘0 < LENGTH ys1’ by rw [LENGTH_NON_NIL] \\
         ‘j5 < LENGTH ys1’ by rw [Abbr ‘j5’] \\
         ‘VAR (EL j5 ys1) = EL j5 (MAP VAR ys1)’ by simp [EL_MAP] >> POP_ORW \\
         MATCH_MP_TAC fromPairs_FAPPLY_EL >> simp []) >> Rewr' \\
     Q.PAT_X_ASSUM ‘_ = W1’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     Know ‘LAST ys1 = LAST vs3’
     >- (‘vs3 = vs1 ++ ys1’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
         ‘xs1 <> []’ by simp [Abbr ‘xs1’] \\
         ‘ys1 <> []’ by METIS_TAC [LENGTH_NON_NIL] \\
         rw [LAST_APPEND_NOT_NIL]) >> Rewr' \\
     simp [])
 >> DISCH_TAC
 >> Know ‘LAST vs4 = y4’
 >- (Know ‘vs2 <<= vs4’
     >- (qunabbrevl_tac [‘vs2’, ‘vs4’] \\
         MATCH_MP_TAC RNEWS_prefix >> simp []) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n2'’ STRIP_ASSUME_TAC) \\
    ‘n2' = n2’ by rw [] \\
     Q.PAT_X_ASSUM ‘n2' <= n4’ MP_TAC \\
     Q.PAT_X_ASSUM ‘vs2 = TAKE n2' vs4’ (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
     POP_ORW >> NTAC 2 DISCH_TAC \\
    ‘vs2 ++ xs2 = zs2'’ by simp [Abbr ‘zs2'’, Abbr ‘xs2’] \\
     qabbrev_tac ‘ys2 = DROP n2 vs4’ \\
    ‘ALL_DISTINCT ys2’ by simp [Abbr ‘ys2’, ALL_DISTINCT_DROP] \\
     Know ‘DISJOINT (set xs2) (set ys2)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs4’ \\
         reverse CONJ_TAC >- simp [LIST_TO_SET_DROP, Abbr ‘ys2’] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set L’ >> art [] \\
         MATCH_MP_TAC LIST_TO_SET_SUFFIX >> art []) >> DISCH_TAC \\
    ‘LENGTH xs2 = LENGTH ys2’ by simp [Abbr ‘xs2’, Abbr ‘ys2’] \\
     Know ‘LAMl vs4 (VAR y4 @* Ns4) = LAMl zs2' (VAR h @* Ns2x)’ >- rw [] \\
    ‘vs4 = vs2 ++ ys2’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
     Q.PAT_X_ASSUM ‘_ = zs2'’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [LAMl_APPEND] \\
     qabbrev_tac ‘t = VAR h @* Ns2x’ \\
  (* applying LAMl_ALPHA_ssub *)
     qabbrev_tac ‘pm2 = fromPairs xs2 (MAP VAR ys2)’ \\
     Know ‘DISJOINT (set vs) (set ys2)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs4’ >> simp [Abbr ‘ys2’, LIST_TO_SET_DROP] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs0’ >> art [] \\
         qunabbrevl_tac [‘vs0’, ‘vs4’] \\
         MATCH_MP_TAC DISJOINT_RNEWS >> simp [Abbr ‘r1’]) >> DISCH_TAC \\
     Know ‘DISJOINT (set ys) (set ys2)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set vs4’ >> simp [Abbr ‘ys2’, LIST_TO_SET_DROP] \\
         qunabbrevl_tac [‘ys’, ‘vs4’] \\
         MATCH_MP_TAC DISJOINT_RNEWS \\
        ‘0 < LENGTH q’ by rw [LENGTH_NON_NIL] \\
         simp [Abbr ‘r1’]) >> DISCH_TAC \\
     Know ‘LAMl xs2 t = LAMl ys2 (pm2 ' t)’
     >- (simp [Abbr ‘pm2’, fromPairs_def] \\
         MATCH_MP_TAC LAMl_ALPHA_ssub >> art [] \\
         simp [DISJOINT_UNION'] \\
         CONJ_TAC >- rw [Once DISJOINT_SYM] \\
         simp [Abbr ‘t’, Abbr ‘Ns2x’, appstar_APPEND, FV_appstar_MAP_VAR] \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set xs2’ >> art [] \\
             simp [Abbr ‘xs2’, LIST_TO_SET_SNOC] \\
             SET_TAC []) \\
         simp [FV_appstar] \\
         CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘DISJOINT (set xs2) (set ys2)’ MP_TAC \\
             rw [Abbr ‘xs2’, LIST_TO_SET_SNOC, DISJOINT_ALT]) \\
         simp [MEM_EL] >> rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘_ = FV x’ (REWRITE_TAC o wrap) >> POP_ORW \\
         rename1 ‘i < m2’ >> POP_ASSUM MP_TAC \\
         simp [Abbr ‘Ns2''’, EL_MAP] >> DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘FV (EL i Ns2')’ \\
         reverse CONJ_TAC
         >- (MP_TAC (Q.SPECL [‘ss’, ‘EL i Ns2'’] FV_ISUB_upperbound) \\
             simp [EL_MAP, Abbr ‘Ns2'’]) \\
         simp [Abbr ‘Ns2'’, EL_listpm, Abbr ‘pm’, REVERSE_ZIP] \\
      (* applying FV_tpm_disjoint *)
         ONCE_REWRITE_TAC [DISJOINT_SYM] \\
         MATCH_MP_TAC FV_tpm_disjoint \\
         simp [ALL_DISTINCT_REVERSE] \\
      (* goal: DISJOINT (set ys2) (FV (EL i Ns2)) *)
         Know ‘FV N0' SUBSET X UNION RANK r1’
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV N'’ >> art [] \\
             qunabbrev_tac ‘N0'’ \\
             MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) >> DISCH_TAC \\
      (* applying FV_subterm_lemma *)
         Know ‘FV (EL i Ns2) SUBSET FV N' UNION set vs2’
         >- (MATCH_MP_TAC FV_subterm_lemma \\
             qexistsl_tac [‘X’, ‘r1’, ‘N0'’, ‘n2’, ‘m2’, ‘N1'’] >> simp []) \\
         DISCH_TAC \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV N' UNION set vs2’ >> art [] \\
         REWRITE_TAC [DISJOINT_UNION'] \\
         reverse CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT vs4’ MP_TAC \\
            ‘vs4 = vs2 ++ ys2’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
             simp [ALL_DISTINCT_APPEND', Once DISJOINT_SYM]) \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘X UNION RANK r1’ >> art [] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs4’ \\
         reverse CONJ_TAC
         >- (‘vs4 = vs2 ++ ys2’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
             simp [SUBSET_DEF]) \\
         simp [DISJOINT_UNION'] \\
         qunabbrev_tac ‘vs4’ \\
         MATCH_MP_TAC DISJOINT_RNEWS_RANK' >> art []) >> Rewr' \\
    ‘vs2 ++ ys2 = vs4’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
    ‘FDOM pm2 = set xs2’ by simp [Abbr ‘pm2’, FDOM_fromPairs] \\
    ‘MEM h xs2’ by simp [Abbr ‘xs2’, LIST_TO_SET_SNOC] \\
     simp [Abbr ‘t’, ssub_appstar] \\
     Know ‘pm2 ' h = VAR (LAST ys2)’
     >- (‘h = LAST xs2’ by rw [Abbr ‘xs2’, LAST_SNOC] >> POP_ORW \\
         ‘xs2 <> []’ by simp [Abbr ‘xs2’] \\
         ‘ys2 <> []’ by METIS_TAC [LENGTH_NON_NIL] \\
         simp [Abbr ‘pm2’, LAST_EL] \\
         qabbrev_tac ‘j5 = PRE (LENGTH ys2)’ \\
        ‘0 < LENGTH ys2’ by rw [LENGTH_NON_NIL] \\
        ‘j5 < LENGTH ys2’ by rw [Abbr ‘j5’] \\
        ‘VAR (EL j5 ys2) = EL j5 (MAP VAR ys2)’ by simp [EL_MAP] >> POP_ORW \\
         MATCH_MP_TAC fromPairs_FAPPLY_EL >> simp []) >> Rewr' \\
     Q.PAT_X_ASSUM ‘_ = W1'’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     Know ‘LAST ys2 = LAST vs4’
     >- (‘vs4 = vs2 ++ ys2’ by METIS_TAC [TAKE_DROP] >> POP_ORW \\
         ‘xs2 <> []’ by simp [Abbr ‘xs2’] \\
         ‘ys2 <> []’ by METIS_TAC [LENGTH_NON_NIL] \\
         rw [LAST_APPEND_NOT_NIL]) >> Rewr' \\
     simp [])
 >> DISCH_TAC
 >> PRINT_TAC "stage work on subtree_equiv_lemma"
 >> Know ‘y3 = y4 <=> n3 = n4’
 >- (Q.PAT_X_ASSUM ‘LAST vs3 = y3’ (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘LAST vs4 = y4’ (REWRITE_TAC o wrap o SYM) \\
     qabbrev_tac ‘n5 = MAX n3 n4’ \\
     Q_TAC (RNEWS_TAC (“vs5 :string list”, “r1 :num”, “n5 :num”)) ‘X’ \\
    ‘n3 <= n5 /\ n4 <= n5’ by simp [Abbr ‘n5’, MAX_LE] \\
     Know ‘vs3 <<= vs5’
     >- (qunabbrevl_tac [‘vs3’, ‘vs5’] \\
         MATCH_MP_TAC RNEWS_prefix >> simp []) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n3'’ STRIP_ASSUME_TAC) \\
     Know ‘n3' = n3’
     >- (POP_ASSUM (MP_TAC o (AP_TERM “LENGTH :string list -> num”)) \\
         simp []) >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘n3' <= n5’ MP_TAC \\
     Q.PAT_X_ASSUM ‘vs3 = TAKE n3' vs5’ (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
     POP_ORW >> NTAC 2 DISCH_TAC \\
     Know ‘vs4 <<= vs5’
     >- (qunabbrevl_tac [‘vs4’, ‘vs5’] \\
         MATCH_MP_TAC RNEWS_prefix >> simp []) \\
     simp [IS_PREFIX_EQ_TAKE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n4'’ STRIP_ASSUME_TAC) \\
     Know ‘n4' = n4’
     >- (POP_ASSUM (MP_TAC o (AP_TERM “LENGTH :string list -> num”)) \\
         simp []) >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘n4' <= n5’ MP_TAC \\
     Q.PAT_X_ASSUM ‘vs4 = TAKE n4' vs5’ (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) \\
     POP_ORW >> NTAC 2 DISCH_TAC \\
    ‘vs3 <> [] /\ vs4 <> []’ by simp [GSYM LENGTH_NON_NIL] \\
     simp [LAST_EL] \\
     Q.PAT_X_ASSUM ‘TAKE n3 vs5 = vs3’ (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘TAKE n4 vs5 = vs4’ (REWRITE_TAC o wrap o SYM) \\
     simp [EL_TAKE] \\
  (* applying ALL_DISTINCT_EL_IMP *)
     Know ‘EL (PRE n3) vs5 = EL (PRE n4) vs5 <=> PRE n3 = PRE n4’
     >- (MATCH_MP_TAC ALL_DISTINCT_EL_IMP >> simp []) >> Rewr' \\
     simp [INV_PRE_EQ])
 >> Rewr'
 (* Current situation:

    N  -h->* LAMl vs1  (VAR y1  @* Ns1) (= N0)
    N' -h->* LAMl vs2  (VAR y2  @* Ns2) (= N0')
   --------------------------------------------
    W  -h->* LAMl vs3  (VAR y3  @* Ns3) (= W0) ---+  (y3 = LAST vs3)
    W  -h->* LAMl vs1  (P3      @* Ns1'')         |=
       -h->* LAMl zs1' (VAR h   @* Ns1x) ---------+
   --------------------------------------------
    W' -h->* LAMl vs4  (VAR y4  @* Ns4) (= W0') --+  (y4 = LAST vs4)
    W' -h->* LAMl vs2  (P4      @* Ns2'')         |=
       -h->* LAMl zs2' (VAR h   @* Ns2x) ---------+

    Structure of W0:

    LAMl |<---(vs1)--- vs3 -------(ys1)------->| VAR y3 (= LAST vs3)
    LAMl |<----------- zs1' ------------------>| VAR h
    LAMl |<--- vs1 ---->|<------- zs1 ------>|h| VAR h
                        |<------- xs1 -------->|
        n3 =   n1      +  d_max' j3 - m1 + 1
       (m3 =   m1      +  d_max' j3 - m1   = d_max' j3)

    Structure of W0':

    LAMl |<---(vs2)----- vs4 ----(ys2)--->| VAR y4 (= LAST vs4)
    LAMl |<------------- zs2' ----------->| VAR h
    LAMl |<--- vs2 ----->|<---- zs2 --->|h| VAR h
                         |<---- xs2 ----->|
        n4 =   n2      +  d_max' j4 - m2 + 1
       (m4 =   m2      +  d_max' j4 - m2   = d_max' j4)
  *)
 >> PRINT_TAC "stage work on subtree_equiv_lemma"
 >> Cases_on ‘y1 = y2’ >> simp []
 (* now: y1 <> y2 *)
 >> ‘y1' <> y2'’ by rw [Abbr ‘y1'’, Abbr ‘y2'’]
 >> ‘y j3 <> y j4’ by rw []
 >> Suff ‘m3 <> m4’ >- simp []
 (* final goal (uniqueness of f) *)
 >> Q.PAT_X_ASSUM ‘_ = m3’ (REWRITE_TAC o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘_ = m4’ (REWRITE_TAC o wrap o SYM)
 >> simp [Abbr ‘d_max'’]
QED

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
           let M0 = principal_hnf M;
               N0 = principal_hnf N;
               n  = LAMl_size M0;
               n' = LAMl_size N0;
               vs = NEWS (MAX n n') (FV M UNION FV N);
              vsM = TAKE n  vs;
              vsN = TAKE n' vs;
               M1 = principal_hnf (M0 @* MAP VAR vsM);
               N1 = principal_hnf (N0 @* MAP VAR vsN);
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
           let M0 = principal_hnf M;
               N0 = principal_hnf N;
               n1 = LAMl_size M0;
               n2 = LAMl_size N0;
              vs1 = RNEWS r n1 X;
              vs2 = RNEWS r n2 X;
               M1 = principal_hnf (M0 @* MAP VAR vs1);
               N1 = principal_hnf (N0 @* MAP VAR vs2);
               y1  = hnf_head M1;
               y2 = hnf_head N1;
               m1 = LENGTH (hnf_children M1);
               m2 = LENGTH (hnf_children N1);
           in
               y1 = y2 /\ n1 + m2 = n2 + m1
        else
           ~solvable M /\ ~solvable N
End

Theorem equivalent2_refl[simp] :
    equivalent2 X M M r
Proof
    RW_TAC std_ss [equivalent2_def]
 >> ‘n1 = n2’ by rw [Abbr ‘n1’, Abbr ‘n2’]
 >> POP_ASSUM (fs o wrap)
 >> Q.PAT_X_ASSUM ‘vs2 = vs1’ (fs o wrap)
 >> Q.PAT_X_ASSUM ‘N1 = M1’ (fs o wrap)
QED

Theorem equivalent2_comm :
    !X M N r. equivalent2 X M N r <=> equivalent2 X N M r
Proof
    RW_TAC std_ss [equivalent2_def] >> fs []
 >> Q.PAT_X_ASSUM ‘n2' = n1’ (fs o wrap)
 >> Q.PAT_X_ASSUM ‘vs2' = vs1’ (fs o wrap)
 >> Q.PAT_X_ASSUM ‘N1' = M1’ (fs o wrap)
 >> Q.PAT_X_ASSUM ‘m2' = m1’ (fs o wrap)
 >> Q.PAT_X_ASSUM ‘y2' = y1’ (fs o wrap)
 >> PROVE_TAC []
QED

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
     MATCH_MP_TAC principal_hnf_FV_SUBSET \\
     simp [has_hnf_def] \\
     qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs1)’ \\
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
         MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) \\
     Suff ‘set vs1 SUBSET RANK r’ >- SET_TAC [] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs’ \\
     simp [Abbr ‘vs1’, LIST_TO_SET_TAKE] \\
     qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC RNEWS_SUBSET_RANK >> art [])
 >> DISCH_TAC
 >> Know ‘FV N1 SUBSET FV (N0 @* MAP VAR vs2)’
 >- (qunabbrev_tac ‘N1’ \\
     MATCH_MP_TAC principal_hnf_FV_SUBSET \\
     simp [has_hnf_def] \\
     qabbrev_tac ‘N1 = principal_hnf (N0 @* MAP VAR vs2)’ \\
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
         MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) \\
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
          let M0 = principal_hnf M;
              N0 = principal_hnf N;
              n  = LAMl_size M0;
              n' = LAMl_size N0;
              vs = NEWS (MAX n n') (FV M UNION FV N);
             vsM = TAKE n  vs;
             vsN = TAKE n' vs;
              M1 = principal_hnf (M0 @* MAP VAR vsM);
              N1 = principal_hnf (N0 @* MAP VAR vsN);
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
           let M0 = principal_hnf M;
               N0 = principal_hnf N;
               n1 = LAMl_size M0;
               n2 = LAMl_size N0;
              vs1 = RNEWS r n1 X;
              vs2 = RNEWS r n2 X;
               M1 = principal_hnf (M0 @* MAP VAR vs1);
               N1 = principal_hnf (N0 @* MAP VAR vs2);
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
 >> ‘LAMl_size (principal_hnf M) = LAMl_size (principal_hnf N)’
       by METIS_TAC [lameq_principal_hnf_size_eq']
 (* stage work *)
 >> RW_TAC std_ss [equivalent_of_solvables] (* 2 subgoals, same tactics *)
 >> ‘ALL_DISTINCT vs /\ DISJOINT (set vs) X /\ LENGTH vs = n’
       by (rw [Abbr ‘vs’, NEWS_def])
 >> ‘vsM = vs’ by rw [Abbr ‘vsM’, TAKE_LENGTH_ID_rwt]
 >> POP_ASSUM (fs o wrap)
 >> Q.PAT_X_ASSUM ‘vs = vsN’ (fs o wrap o SYM)
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘N’, ‘M0’, ‘N0’, ‘n’, ‘vs’, ‘M1’, ‘N1’]
                    lameq_principal_hnf_thm_simple)
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
 >> ‘LAMl_size (principal_hnf M) = LAMl_size (principal_hnf N)’
       by METIS_TAC [lameq_principal_hnf_size_eq']
 (* stage work *)
 >> RW_TAC std_ss [equivalent2_of_solvables] (* 2 subgoals, same tactics *)
 >> qunabbrev_tac ‘vs1’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n1 :num”)) ‘X’
 >> qunabbrev_tac ‘vs2’
 >> MP_TAC (Q.SPECL [‘r’, ‘X’, ‘M’, ‘N’, ‘M0’, ‘N0’, ‘n1’, ‘vs’, ‘M1’, ‘N1’]
                    lameq_principal_hnf_thm')
 >> simp []
QED

(* NOTE: the initial calls of ‘principal_hnf’ get eliminated if the involved
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
              M1 = principal_hnf (M @* MAP VAR vsM);
              N1 = principal_hnf (N @* MAP VAR vsN);
              y  = hnf_head M1;
              y' = hnf_head N1;
              m  = LENGTH (hnf_children M1);
              m' = LENGTH (hnf_children N1)
           in
              y = y' /\ n + m' = n' + m)
Proof
    rpt STRIP_TAC
 >> ‘solvable M /\ solvable N’ by PROVE_TAC [hnf_solvable]
 >> RW_TAC std_ss [equivalent_def, principal_hnf_reduce]
 >> METIS_TAC []
QED

Theorem equivalent2_of_hnf :
    !X M N r. hnf M /\ hnf N ==>
          (equivalent2 X M N r <=>
           let n1 = LAMl_size M;
               n2 = LAMl_size N;
              vs1 = RNEWS r n1 X;
              vs2 = RNEWS r n2 X;
               M1 = principal_hnf (M @* MAP VAR vs1);
               N1 = principal_hnf (N @* MAP VAR vs2);
               y1 = hnf_head M1;
               y2 = hnf_head N1;
               m1 = LENGTH (hnf_children M1);
               m2 = LENGTH (hnf_children N1);
           in
               y1 = y2 /\ n1 + m2 = n2 + m1)

Proof
    rpt STRIP_TAC
 >> ‘solvable M /\ solvable N’ by PROVE_TAC [hnf_solvable]
 >> RW_TAC std_ss [equivalent2_def, principal_hnf_reduce]
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
 >> RW_TAC std_ss [equivalent_of_solvables, principal_hnf_reduce]
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
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vsM)’
 >> qunabbrev_tac ‘N1’
 >> qabbrev_tac ‘N1 = principal_hnf (N0 @* MAP VAR vsN)’
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
                          fs [principal_hnf_beta_reduce1]) \\
     MATCH_MP_TAC principal_hnf_beta >> simp [Abbr ‘u’] \\
     rfs [FV_thm])
 >> DISCH_THEN (rfs o wrap)
 >> Know ‘N1 = [VAR z/v] u’
 >- (qunabbrev_tac ‘N1’ \\
     Cases_on ‘z = v’ >- (POP_ASSUM (rfs o wrap)) \\
     MATCH_MP_TAC principal_hnf_beta >> simp [Abbr ‘u’] \\
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
 >> qabbrev_tac ‘N0 = principal_hnf N’
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
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs1)’
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
 *  subtree_equiv_lemma
 *---------------------------------------------------------------------------*)

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
     >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘BIGUNION (IMAGE FV (set Ms))’ \\
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
    !X M N pi r.
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
 >> qabbrev_tac ‘M1 = \i. principal_hnf (apply p0 (M i))’
 >> Know ‘!i. i < k ==> ?y Ns. M1 i = VAR y @* Ns /\ EVERY (\e. y # e) Ns’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> solvable (apply p0 (M i)) /\ _’ drule \\
     rw [Abbr ‘M1’] \\
     qexistsl_tac [‘y’, ‘Ns’] >> art [] \\
     rw [principal_hnf_thm', hnf_appstar])
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
         MATCH_MP_TAC BT_of_principal_hnf >> simp []) >> Rewr' \\
     Know ‘BT' X (apply p0 (M i)) r = BT' X (M1 i) r’
     >- (SIMP_TAC std_ss [Once EQ_SYM_EQ, Abbr ‘M1’] \\
         MATCH_MP_TAC BT_of_principal_hnf >> simp []) >> Rewr' \\
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
     simp [Abbr ‘M1’, principal_hnf_thm'])
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
         MATCH_MP_TAC BT_of_principal_hnf >> simp []) >> Rewr' \\
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
         simp [Abbr ‘M1’, principal_hnf_thm']) \\
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
    sure whether “principal_hnf (apply (p1 ++ p0) (M i)) = EL h (f i)”.
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
     Q.PAT_X_ASSUM ‘!q M N. q <<= h::p /\ q <> h::p /\
                            MEM M (apply p0 Ms) /\ _ ==> _’
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
         MATCH_MP_TAC BT_of_principal_hnf >> simp []) >> Rewr' \\
     Know ‘BT' X (apply p0 (M b)) r = BT' X (M1 b) r’
     >- (SIMP_TAC std_ss [Once EQ_SYM_EQ, Abbr ‘M1’] \\
         MATCH_MP_TAC BT_of_principal_hnf >> simp []) >> Rewr' \\
     simp [] \\
    ‘!i. solvable (VAR y @* f i)’ by rw [] \\
    ‘!i. principal_hnf (VAR y @* f i) = VAR y @* f i’ by rw [] \\
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
         MATCH_MP_TAC BT_of_principal_hnf >> simp []) >> Rewr' \\
    ‘!i. solvable (VAR y @* f i)’ by rw [] \\
    ‘!i. principal_hnf (VAR y @* f i) = VAR y @* f i’ by rw [] \\
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
    ‘!i. principal_hnf (VAR y @* f i) = VAR y @* f i’ by rw [] \\
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
 >> ‘!i. principal_hnf (VAR y @* f i) = VAR y @* f i’ by rw []
 >> Q_TAC (UNBETA_TAC [subterm_def]) ‘subterm X (VAR y @* f i) (h::p) r’
 >> simp []
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
          LAMl_size (principal_hnf M) <= LAMl_size (principal_hnf N) ==>
          equivalent M N \/
          !P Q. ?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q
Proof
    RW_TAC std_ss [equivalent_of_solvables]
 >> ‘ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M UNION FV N) /\
     LENGTH vs = MAX n n'’ by rw [Abbr ‘vs’, NEWS_def]
 >> ‘DISJOINT (set vs) (FV M) /\ DISJOINT (set vs) (FV N)’
      by METIS_TAC [DISJOINT_SYM, DISJOINT_UNION]
 (* applying principal_hnf_FV_SUBSET' *)
 >> Know ‘DISJOINT (set vs) (FV M0)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET >> Q.EXISTS_TAC ‘FV M’ >> art [] \\
     qunabbrev_tac ‘M0’ >> MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set vs) (FV N0)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET >> Q.EXISTS_TAC ‘FV N’ >> art [] \\
     qunabbrev_tac ‘N0’ >> MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art [])
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
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vsM)’
 >> qunabbrev_tac ‘N1’
 >> qabbrev_tac ‘N1 = principal_hnf (N0 @* MAP VAR vsN)’
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
     proof, where [1, p.254] iterated substition "[LAMl as P/y1] [LAMl as' Q/y2]"
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
           MATCH_MP_TAC lameq_principal_hnf >> art [GSYM solvable_iff_has_hnf]) \\
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
           MATCH_MP_TAC lameq_principal_hnf >> art [GSYM solvable_iff_has_hnf]) \\
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
                    MATCH_MP_TAC lameq_principal_hnf \\
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
                    MATCH_MP_TAC lameq_principal_hnf \\
                    ASM_REWRITE_TAC [GSYM solvable_iff_has_hnf]) \\
       REWRITE_TAC [Boehm_apply_APPEND] \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply pi (y @* args2)’ \\
       reverse CONJ_TAC >- art [] \\
       MATCH_MP_TAC Boehm_apply_lameq_cong \\
       Q.PAT_X_ASSUM ‘y = y'’ (ONCE_REWRITE_TAC o wrap) \\
       Q.PAT_X_ASSUM ‘VAR y2 = y'’ (ONCE_REWRITE_TAC o wrap o SYM) >> art [] ])
QED

(* NOTE: This new version uses “equivalent2” instead of the old “equivalent” *)
Theorem separability_lemma0'[local] :
    !X M N r. FINITE X /\
              FV M SUBSET X UNION RANK r /\
              FV N SUBSET X UNION RANK r /\
              solvable (M :term) /\ solvable N /\
              LAMl_size (principal_hnf M) <= LAMl_size (principal_hnf N) ==>
              equivalent2 X M N r \/
             !P Q. ?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q
Proof
    RW_TAC std_ss [equivalent2_of_solvables]
 >> qunabbrevl_tac [‘vs1’, ‘vs2’]
 >> Q_TAC (RNEWS_TAC (“vs1 :string list”, “r :num”, “n1 :num”)) ‘X’
 >> Q_TAC (RNEWS_TAC (“vs2 :string list”, “r :num”, “n2 :num”)) ‘X’
 >> ‘DISJOINT (set vs1) (FV M) /\ DISJOINT (set vs2) (FV N)’
      by PROVE_TAC [subterm_disjoint_lemma]
 >> ‘vs1 <<= vs2’ by METIS_TAC [RNEWS_prefix]
 >> ‘DISJOINT (set vs1) (FV M0) /\ DISJOINT (set vs2) (FV N0)’
      by PROVE_TAC [subterm_disjoint_lemma']
 >> qunabbrevl_tac [‘y1’, ‘y2’]
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs1 :string list”,
                    “y1 :string”, “args1 :term list”)) ‘M1’
 >> ‘TAKE (LAMl_size M0) vs1 = vs1’ by rw [Abbr ‘vs1’, Abbr ‘n1’]
 >> POP_ASSUM (rfs o wrap)
 >> Q_TAC (HNF_TAC (“N0 :term”, “vs2 :string list”,
                    “y2 :string”, “args2 :term list”)) ‘N1’
 >> ‘TAKE (LAMl_size N0) vs2 = vs2’ by rw [Abbr ‘vs2’, Abbr ‘n2’]
 >> POP_ASSUM (rfs o wrap)
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs1) (FV M0)’ K_TAC
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs2) (FV N0)’ K_TAC
 (* reshaping and reordering assumptions *)
 >> simp [Abbr ‘m1’, Abbr ‘m2’]
 >> qabbrev_tac ‘m1 = LENGTH args1’
 >> qabbrev_tac ‘m2 = LENGTH args2’
 (* Case 1 *)
 >> Cases_on ‘y1 <> y2’
 >- (simp [] >> rpt GEN_TAC \\
     qabbrev_tac ‘k = n2 - n1’ \\
    ‘n1 + k = n2’ by rw [Abbr ‘k’] \\
     qabbrev_tac ‘p0 = MAP rightctxt (REVERSE (MAP VAR vs2))’ \\
  (* properties of p0 *)
    ‘Boehm_transform p0’ by rw [Boehm_transform_def, Abbr ‘p0’, EVERY_MAP] \\
     Know ‘apply p0 N0 == N1’
     >- (rw [Abbr ‘p0’, Boehm_apply_MAP_rightctxt']) >> DISCH_TAC \\
     Know ‘apply p0 M0 == M1 @* DROP n1 (MAP VAR vs2)’
     >- (qunabbrev_tac ‘p0’ \\
         qabbrev_tac ‘l :term list = MAP VAR vs2’ \\
         Know ‘REVERSE l = REVERSE (TAKE n1 l ++ DROP n1 l)’
         >- REWRITE_TAC [TAKE_DROP] >> Rewr' \\
         REWRITE_TAC [REVERSE_APPEND, MAP_APPEND, Boehm_apply_APPEND] \\
         REWRITE_TAC [Boehm_apply_MAP_rightctxt'] \\
         MATCH_MP_TAC lameq_appstar_cong \\
         Suff ‘TAKE n1 l = MAP VAR vs1’
         >- (Rewr' \\
             simp [Abbr ‘l’, Abbr ‘vs1’, GSYM MAP_TAKE]) \\
         simp [Abbr ‘l’, GSYM MAP_TAKE] \\
         AP_TERM_TAC \\
         qunabbrevl_tac [‘vs1’, ‘vs2’] \\
         MATCH_MP_TAC TAKE_RNEWS >> art []) >> DISCH_TAC \\
  (* now use P and Q

     NOTE: This Z = [z1;z2] contains two fresh variables fixing the textbook
     proof, where [1, p.254] iterated substition "[LAMl as P/y1] [LAMl as' Q/y2]"
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
     Q_TAC (NEWS_TAC (“as :string list”, “m1 + k”)) ‘FV P UNION set Z’ \\
     Q_TAC (NEWS_TAC (“as' :string list”, “m2 :num”)) ‘FV Q UNION set Z’ \\
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
         Q.EXISTS_TAC ‘FV P UNION set Z’ >> simp [DISJOINT_UNION'] \\
         simp [FV_SUB] \\
         Cases_on ‘y2 IN FV P’ \\
         rw [SUBSET_DEF, IN_UNION, Abbr ‘z2’] >> art []) \\
     DISCH_TAC \\
     Know ‘DISJOINT (set as') (FV ([VAR z1/y1] Q))’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV Q UNION set Z’ >> simp [DISJOINT_UNION'] \\
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
           MATCH_MP_TAC lameq_principal_hnf >> art [GSYM solvable_iff_has_hnf]) \\
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
                    MATCH_MP_TAC lameq_hnf_fresh_subst >> simp []) \\
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
           MATCH_MP_TAC lameq_principal_hnf >> art [GSYM solvable_iff_has_hnf]) \\
    (* eliminating p0 *)
       REWRITE_TAC [Boehm_apply_APPEND] \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply p1 (M1 @* DROP n1 (MAP VAR vs2))’ \\
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
                    MATCH_MP_TAC lameq_LAMl_appstar_reduce >> simp []) \\
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
 >> qabbrev_tac ‘p0 = MAP rightctxt (REVERSE (MAP VAR vs2))’
 (* properties of p0 *)
 >> ‘Boehm_transform p0’ by rw [Boehm_transform_def, Abbr ‘p0’, EVERY_MAP]
 >> Know ‘apply p0 N0 == N1’
 >- rw [Abbr ‘p0’, Boehm_apply_MAP_rightctxt']
 >> Q.PAT_X_ASSUM ‘N1 = _’ (ONCE_REWRITE_TAC o wrap)
 >> DISCH_TAC
 >> Know ‘apply p0 M0 == M1 @* DROP n1 (MAP VAR vs2)’
 >- (qunabbrev_tac ‘p0’ \\
     qabbrev_tac ‘l :term list = MAP VAR vs2’ \\
     Know ‘REVERSE l = REVERSE (TAKE n1 l ++ DROP n1 l)’
     >- REWRITE_TAC [TAKE_DROP] >> Rewr' \\
     REWRITE_TAC [REVERSE_APPEND, MAP_APPEND, Boehm_apply_APPEND] \\
     REWRITE_TAC [Boehm_apply_MAP_rightctxt'] \\
     MATCH_MP_TAC lameq_appstar_cong \\
     Suff ‘TAKE n1 l = MAP VAR vs1’
     >- (Rewr' \\
         simp [Abbr ‘l’, Abbr ‘vs1’, GSYM MAP_TAKE]) \\
     simp [Abbr ‘l’, GSYM MAP_TAKE] \\
     AP_TERM_TAC \\
     qunabbrevl_tac [‘vs1’, ‘vs2’] \\
     MATCH_MP_TAC TAKE_RNEWS >> art [])
 >> Q.PAT_X_ASSUM ‘M1 = _’ (ONCE_REWRITE_TAC o wrap)
 >> ‘VAR y1 = VAR y2 :term’ by PROVE_TAC [] >> POP_ORW
 >> REWRITE_TAC [GSYM appstar_APPEND]
 >> qabbrev_tac ‘args1' = args1 ++ DROP n1 (MAP VAR vs2)’
 >> DISCH_TAC
 >> qabbrev_tac ‘l = LENGTH args1'’
 >> ‘l <> m2’ by rw [Abbr ‘l’, Abbr ‘args1'’]
 (* stage work *)
 >> ‘m2 < l \/ l < m2’ by rw [] (* 2 subgoals, same ending tactics *)
 >| [ (* goal 1 (of 2) *)
      MP_TAC (Q.SPECL [‘y2’, ‘args1'’, ‘args2’, ‘l - m2’]
                      separability_lemma0_case2) >> simp [] \\
      DISCH_THEN (STRIP_ASSUME_TAC o (Q.SPECL [‘P’, ‘Q’])),
      (* goal 2 (of 2) *)
      MP_TAC (Q.SPECL [‘y2’, ‘args2’, ‘args1'’, ‘m2 - l’]
                      separability_lemma0_case2) >> simp [] \\
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
                    MATCH_MP_TAC lameq_principal_hnf \\
                    ASM_REWRITE_TAC [GSYM solvable_iff_has_hnf]) \\
       REWRITE_TAC [Boehm_apply_APPEND] \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply pi (VAR y2 @* args1')’ \\
       reverse CONJ_TAC >- art [] \\
       MATCH_MP_TAC Boehm_apply_lameq_cong >> art [],
       (* goal 1.2 (of 2) *)
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply (pi ++ p0) N0’ \\
       CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong \\
                    POP_ASSUM (REWRITE_TAC o wrap) \\
                    qunabbrev_tac ‘N0’ >> MATCH_MP_TAC lameq_SYM \\
                    MATCH_MP_TAC lameq_principal_hnf \\
                    ASM_REWRITE_TAC [GSYM solvable_iff_has_hnf]) \\
       REWRITE_TAC [Boehm_apply_APPEND] \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply pi (VAR y1 @* args2)’ \\
       reverse CONJ_TAC >- art [] \\
       MATCH_MP_TAC Boehm_apply_lameq_cong >> art [] \\
       Q.PAT_X_ASSUM ‘y1 = y2’ (ONCE_REWRITE_TAC o wrap) \\
       Q.PAT_X_ASSUM ‘N0 = _’ (ONCE_REWRITE_TAC o wrap o SYM) >> art [] ])
QED

(* Lemma 10.4.1 (i) [1, p.254] *)
Theorem separability_lemma1 :
    !M N. solvable (M :term) /\ solvable N /\ ~equivalent M N ==>
          !P Q. ?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> qabbrev_tac ‘N0 = principal_hnf N’
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

Theorem separability_lemma1' :
    !X M N r.
       FINITE X /\
       FV M SUBSET X UNION RANK r /\
       FV N SUBSET X UNION RANK r /\
       solvable (M :term) /\ solvable N /\ ~equivalent2 X M N r ==>
       !P Q. ?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> qabbrev_tac ‘N0 = principal_hnf N’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> qabbrev_tac ‘n' = LAMl_size N0’
 (* applying separability_lemma0 *)
 >> ‘n <= n' \/ n' <= n’ by rw []
 >- METIS_TAC [separability_lemma0']
 >> MP_TAC (Q.SPECL [‘X’, ‘N’, ‘M’, ‘r’] separability_lemma0')
 >> RW_TAC std_ss [Once equivalent2_comm]
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

Theorem separability_lemma2' :
    !X M N r.
       FINITE X /\
       FV M SUBSET X UNION RANK r /\
       FV N SUBSET X UNION RANK r /\
       solvable M /\ ~equivalent2 X M N r ==>
       !P. ?pi. Boehm_transform pi /\ apply pi M == P /\ ~solvable (apply pi N)
Proof
    rpt STRIP_TAC
 (* applying separability_lemma1, ‘~equivalent M N’ is only used here *)
 >> Cases_on ‘solvable N’
 >- (‘!P Q. ?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q’
         by METIS_TAC [separability_lemma1'] \\
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

(* NOTE: This lemma only depends on [separability_lemma1]. The present version
   is tailored for applying [distinct_bnf_imp_agree_upto] and [agree_upto_thm].
 *)
Theorem separability_lemma3 :
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
     fs [UNION_SUBSET] \\
    ‘?p1. Boehm_transform p1 /\ apply p1 M0 == P /\ apply p1 N0 == Q’
       by PROVE_TAC [separability_lemma1] \\
     Q.EXISTS_TAC ‘p1 ++ p0’ \\
     fs [Abbr ‘M0’, Abbr ‘N0’, Boehm_transform_APPEND, GSYM Boehm_apply_APPEND])
 (* stage work *)
 >> Q.PAT_X_ASSUM ‘_ <=> solvable M0’ (REWRITE_TAC o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘_ <=> solvable N0’ (REWRITE_TAC o wrap o SYM)
 >> fs [SUBSET_UNION]
 >> Know ‘BT_valid_paths M = BT_paths M’
 >- (MATCH_MP_TAC BT_valid_paths_has_bnf >> simp [])
 >> Rewr'
 >> Know ‘BT_valid_paths N = BT_paths N’
 >- (MATCH_MP_TAC BT_valid_paths_has_bnf >> simp [])
 >> Rewr'
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘r’] BT_paths_thm)
 >> simp [] >> DISCH_THEN K_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘N’, ‘r’] BT_paths_thm)
 >> simp []
QED

(* Theorem 10.4.2 (i) [1, p.256]

   NOTE: It is actually "eta-separability" because we have “lameta (apply pi M) P”
   instead of “apply pi M == P”.
 *)
Theorem separability_thm :
    !X M N r.
       FINITE X /\ FV M UNION FV N SUBSET X UNION RANK r /\ 0 < r /\
       has_benf M /\ has_benf N /\ ~(lameta M N) ==>
       !P Q. ?pi. Boehm_transform pi /\
                  lameta (apply pi M) P /\ lameta (apply pi N) Q
Proof
    rw []
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
 >> Know ‘~(M0 == N0)’
 >- (CCONTR_TAC >> fs [] \\
     Q.PAT_X_ASSUM ‘~lameta M N’ MP_TAC >> simp [] \\
    ‘lameta M0 N0’ by PROVE_TAC [lameq_imp_lameta] \\
     MATCH_MP_TAC lameta_TRANS \\
     Q.EXISTS_TAC ‘M0’ >> art [] \\
     MATCH_MP_TAC lameta_TRANS \\
     Q.EXISTS_TAC ‘N0’ >> art [] \\
     MATCH_MP_TAC lameta_SYM >> art [])
 >> DISCH_TAC
 (* applying separability_lemma3 *)
 >> MP_TAC (Q.SPECL [‘X’, ‘M0’, ‘N0’, ‘r’] separability_lemma3) >> rw []
 >> POP_ASSUM (MP_TAC o Q.SPECL [‘P’, ‘Q’])
 >> STRIP_TAC
 >> Q.EXISTS_TAC ‘pi’ >> art []
 >> ‘lameta (apply pi M0) P /\
     lameta (apply pi N0) Q’ by PROVE_TAC [lameq_imp_lameta]
 >> CONJ_TAC
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC lameta_TRANS \\
      Q.EXISTS_TAC ‘apply pi M0’ >> art [] \\
      MATCH_MP_TAC Boehm_apply_lameta_cong >> art [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC lameta_TRANS \\
      Q.EXISTS_TAC ‘apply pi N0’ >> art [] \\
      MATCH_MP_TAC Boehm_apply_lameta_cong >> art [] ]
QED

(* NOTE: We call it "final" if there's no “FINITE X /\ FV M SUBSET X UNION RANK r”
   in antecedents.
 *)
Theorem separability_final :
    !M N. has_benf M /\ has_benf N /\ ~(lameta M N) ==>
          !P Q. ?pi. Boehm_transform pi /\
                     lameta (apply pi M) P /\ lameta (apply pi N) Q
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘FV M UNION FV N’, ‘M’, ‘N’, ‘1’] separability_thm)
 >> simp []
 >> impl_tac >- SET_TAC []
 >> DISCH_THEN (STRIP_ASSUME_TAC o Q.SPECL [‘P’, ‘Q’])
 >> Q.EXISTS_TAC ‘pi’ >> art []
QED

(* Theorem 10.4.2 (ii) [1, p.256] *)
Theorem closed_separability_thm :
    !M N. has_benf M /\ has_benf N /\ ~(lameta M N) /\
          closed M /\ closed N ==>
          !P Q. ?L. lameta (M @* L) P /\ lameta (N @* L) Q
Proof
    rpt STRIP_TAC
 >> ‘?pi. Boehm_transform pi /\
          lameta (apply pi M) P /\ lameta (apply pi N) Q’
       by METIS_TAC [separability_final]
 >> ‘?L. !M. closed M ==> apply pi M == M @* L’
       by METIS_TAC [Boehm_transform_lameq_appstar]
 >> Q.EXISTS_TAC ‘L’
 >> CONJ_TAC (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC lameta_TRANS \\
      Q.EXISTS_TAC ‘apply pi M’ >> art [] \\
      MATCH_MP_TAC lameq_imp_lameta \\
      MATCH_MP_TAC lameq_SYM \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC lameta_TRANS \\
      Q.EXISTS_TAC ‘apply pi N’ >> art [] \\
      MATCH_MP_TAC lameq_imp_lameta \\
      MATCH_MP_TAC lameq_SYM \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [] ]
QED

(* Corollary 10.4.3 (i) [1, p.256] *)
Theorem distinct_benf_imp_inconsistent :
    !M N. has_benf M /\ has_benf N /\ ~(lameta M N) ==>
          inconsistent (conversion (RINSERT (beta RUNION eta) M N))
Proof
    rw [inconsistent_def]
 >> MP_TAC (Q.SPECL [‘M’, ‘N’] separability_final) >> rw []
 >> POP_ASSUM (MP_TAC o Q.SPECL [‘M'’, ‘N'’])
 >> STRIP_TAC
 (* M' ~ apply pi M  ~ apply pi N ~ N' *)
 >> MATCH_MP_TAC conversion_TRANS
 >> Q.EXISTS_TAC ‘apply pi M’
 >> CONJ_TAC
 >- (irule (REWRITE_RULE [RSUBSET] conversion_monotone) \\
     Q.EXISTS_TAC ‘beta RUNION eta’ >> simp [RINSERT] \\
     MATCH_MP_TAC conversion_SYM \\
     rw [beta_eta_lameta])
 >> MATCH_MP_TAC conversion_TRANS
 >> Q.EXISTS_TAC ‘apply pi N’
 >> reverse CONJ_TAC
 >- (irule (REWRITE_RULE [RSUBSET] conversion_monotone) \\
     Q.EXISTS_TAC ‘beta RUNION eta’ >> simp [RINSERT] \\
     rw [beta_eta_lameta])
 >> NTAC 2 (POP_ASSUM K_TAC)
 >> rw [eta_extend_alt_conversion]
 >> qabbrev_tac ‘eqns = UNCURRY eta UNION {(M,N)}’
 >> Know ‘eqns^+ M N’
 >- (MATCH_MP_TAC asmlam_eqn \\
     rw [Abbr ‘eqns’, IN_UNION])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘Boehm_transform pi’ MP_TAC
 >> qid_spec_tac ‘pi’
 >> LIST_INDUCT_TAC >> rw []
 >> fs [solving_transform_def]
 >- rw [asmlam_rules]
 >> MATCH_MP_TAC asmlam_subst >> art []
QED

(* Corollary 10.4.3 (ii) [1, p.256] *)
Theorem lameta_complete :
    !M N. has_benf M /\ has_benf N ==>
          lameta M N \/ inconsistent (conversion (RINSERT (beta RUNION eta) M N))
Proof
    PROVE_TAC [distinct_benf_imp_inconsistent]
QED

Theorem HP_complete_lameta :
    HP_complete (rel_to_reln eta) has_benf
Proof
    RW_TAC std_ss [HP_complete_def, GSYM eta_extend_alt_conversion,
                   GSYM lameta_asmlam, rel_to_reln_IS_UNCURRY]
 >> MATCH_MP_TAC lameta_complete >> art []
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
 [4] Coppo, M. et al.: (Semi-) separability of Finite Sets of Terms in Scott's
     D-infinity-models of the Lambda-calculus. In: LNCS 62 - Automata, Languages
     and Programming (ICALP 1978). Springer (1978).
 *)
