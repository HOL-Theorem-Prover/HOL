(* ========================================================================== *)
(* FILE    : boehmScript.sml (aka chap10Script.sml)                           *)
(* TITLE   : (Effective) Böhm Trees (Barendregt 1984 [1], Chapter 10)     UOK *)
(*                                                                            *)
(* AUTHORS : 2023-2024 The Australian National University (Chun TIAN)         *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

(* core theories *)
open optionTheory arithmeticTheory pred_setTheory listTheory rich_listTheory
     llistTheory relationTheory ltreeTheory pathTheory posetTheory hurdUtils
     pairTheory finite_mapTheory topologyTheory listRangeTheory combinTheory
     tautLib listLib string_numTheory numLib;

(* local theories *)
open basic_swapTheory nomsetTheory termTheory appFOLDLTheory NEWLib chap2Theory
     chap3Theory reductionEval head_reductionTheory head_reductionLib
     standardisationTheory solvableTheory;

(* enable basic monad support *)
open monadsyntax;
val _ = enable_monadsyntax ();
val _ = enable_monad "option";

(* create the theory *)
val _ = new_theory "boehm";

(* These theorems usually give unexpected results, should be applied manually *)
val _ = temp_delsimps [
   "lift_disj_eq", "lift_imp_disj",
   "IN_UNION",     (* |- !s t x. x IN s UNION t <=> x IN s \/ x IN t *)
   "APPEND_ASSOC", (* |- !l1 l2 l3. l1 ++ (l2 ++ l3) = l1 ++ l2 ++ l3 *)
   "SNOC_APPEND"   (* |- !x l. SNOC x l = l ++ [x] *)
];

val _ = hide "B";
val _ = hide "C";
val _ = hide "W";
val _ = hide "Y";

val _ = set_trace "Goalstack.print_goal_at_top" 0;

fun PRINT_TAC pfx g = (print (pfx ^ "\n"); ALL_TAC g);

(* Disable some conflicting overloads from labelledTermsTheory, by
   repeating the desired overloads again (this prioritizes them).
 *)
Overload FV  = “supp term_pmact”
Overload VAR = “term$VAR”

(*---------------------------------------------------------------------------*
 *  ltreeTheory extras
 *---------------------------------------------------------------------------*)

(* ltree_subset A B <=> A results from B by "cutting off" some subtrees. Thus,

   1) The paths of A is a subset of paths of B
   2) The node contents for all paths of A is identical to those of B, but the number
      of successors at those nodes of B may be different (B may have more successors)

   NOTE: Simply defining ‘ltree_subset A B <=> subtrees A SUBSET subtrees B’ is wrong,
         as A may appear as a non-root subtree of B, i.e. ‘A IN subtrees B’ but there's
         no way to "cut off" B to get A, the resulting subtree in B always have some
         more path prefixes.
 *)
Definition ltree_subset_def :
    ltree_subset A B <=>
       (ltree_paths A) SUBSET (ltree_paths B) /\
       !p. p IN ltree_paths A ==>
           ltree_node (THE (ltree_lookup A p)) =
           ltree_node (THE (ltree_lookup B p))
End

(*---------------------------------------------------------------------------*
 *  Boehm Trees (and subterms) - name after Corrado_Böhm [2]             UOK *
 *---------------------------------------------------------------------------*)

(* The type of Boehm trees:

   For each ltree node, ‘NONE’ represents {\bot} (for unsolvable terms), while
  ‘SOME (vs,y)’ represents ‘LAMl vs (VAR y)’. This separation of vs and y has
   at least two advantages:

   1. ‘set vs’ is the set of binding variables at that ltree node.
   2. ‘LAMl vs (VAR y)’ can easily "expand" (w.r.t. eta reduction) into terms
      such as ‘LAMl (vs ++ [z0;z1]) t’ (with two extra children ‘z0’ and ‘z1’)
      without changing the head variable (VAR y).
 *)
Type BT_node[pp]    = “:(string list # string) option”
Type boehm_tree[pp] = “:BT_node ltree”

(* Definition 10.1.9 [1, p.221] (Effective Boehm Tree)

   NOTE: For the correctness of the definition, ‘FINITE X’ and ‘FV M SUBSET X’,
   or something stronger ‘FV M SUBSET X UNION (RANK r X)’ for induction,
   must be assumed in antecedents.
 *)
Definition BT_generator_def :
    BT_generator X (M,r) =
      if solvable M then
         let M0 = principle_hnf M;
              n = LAMl_size M0;
             vs = RNEWS r n X;
             M1 = principle_hnf (M0 @* MAP VAR vs);
             Ms = hnf_children M1;
              y = hnf_headvar M1;
              l = MAP (\e. (e,SUC r)) Ms;
         in
            (SOME (vs,y),fromList l)
      else
            (NONE, LNIL)
End

Definition BT_def[nocompute] :
    BT X = ltree_unfold (BT_generator X)
End

(* NOTE: ‘BT X (M,r)’ will show as ‘BT' X M r’ *)
Overload BT' = “\X M r. BT X (M,r)”

(* Definition 10.1.13 (iii)

   NOTE: The output ‘SOME (M,r)’ allows to write ‘BT X (THE (subterm X M p r))’.
   Defining ‘m = hnf_children_size M0’ instead of ‘LENGTH Ms’ has extra
   benefits in proving subterm_tpm lemmas.
 *)
Definition subterm_def :
    subterm X M     [] r = SOME (M,r) /\
    subterm X M (h::p) r =
      if solvable M then
         let M0 = principle_hnf M;
              n = LAMl_size M0;
             vs = RNEWS r n X;
             M1 = principle_hnf (M0 @* MAP VAR vs);
             Ms = hnf_children M1;
              m = LENGTH Ms
         in
             if h < m then subterm X (EL h Ms) p (SUC r)
             else NONE
      else
         NONE
End

(* NOTE: The use of ‘subterm' X M p r’ assumes that ‘subterm X M p r <> NONE’ *)
Overload subterm' = “\X M p r. FST (THE (subterm X M p r))”

(* |- subterm X M [] r = SOME (M,r) *)
Theorem subterm_NIL[simp] = SPEC_ALL (cj 1 subterm_def)

Theorem subterm_NIL'[simp] :
    subterm' X M [] r = M
Proof
    rw [subterm_NIL]
QED

Theorem subterm_disjoint_lemma :
    !X M r n vs.
           FINITE X /\ FV M SUBSET X UNION RANK r /\ vs = RNEWS r n X
       ==> DISJOINT (set vs) (FV M)
Proof
    rw [DISJOINT_ALT']
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> Know ‘x IN X UNION RANK r’ >- METIS_TAC [SUBSET_DEF]
 >> rw [IN_UNION]
 >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) X’ MP_TAC \\
     rw [DISJOINT_ALT'])
 >> Suff ‘DISJOINT (RANK r) (set vs)’ >- rw [DISJOINT_ALT]
 >> qunabbrev_tac ‘vs’
 >> MATCH_MP_TAC DISJOINT_RANK_RNEWS' >> art []
QED

Theorem subterm_disjoint_lemma' :
    !X M r M0 n vs.
           FINITE X /\ FV M SUBSET X UNION RANK r /\
           solvable M /\ M0 = principle_hnf M /\ vs = RNEWS r n X
       ==> DISJOINT (set vs) (FV M0)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC DISJOINT_SUBSET
 >> Q.EXISTS_TAC ‘FV M’
 >> reverse CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘M0 = _’ (REWRITE_TAC o wrap) \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> MATCH_MP_TAC subterm_disjoint_lemma
 >> qexistsl_tac [‘X’, ‘r’, ‘n’] >> art []
QED

(* NOTE: In general ‘solvable M’ doesn't imply ‘solvable (M @* args)’. The
   present lemma is a special case.
 *)
Theorem solvable_appstar :
    !X M r M0 n n' vs.
           FINITE X /\ FV M SUBSET X UNION RANK r /\
           solvable M /\
           M0 = principle_hnf M /\
            n = LAMl_size M0 /\
           vs = RNEWS r n' X /\ n <= n'
       ==> solvable (M0 @* MAP VAR vs)
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> ‘hnf M0’ by PROVE_TAC [hnf_principle_hnf']
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n' :num”)) ‘X’
 >> Know ‘?y args. M0 = LAMl (TAKE n vs) (VAR y @* args)’
 >- (rw [Abbr ‘n’] >> irule (iffLR hnf_cases_shared) >> rw [] \\
     MATCH_MP_TAC subterm_disjoint_lemma' \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘LENGTH vs’] >> rw [])
 >> STRIP_TAC
 >> qabbrev_tac ‘xs = TAKE n vs’
 >> qabbrev_tac ‘m = hnf_children_size M0’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> Know ‘M1 = VAR y @* args @* DROP n (MAP VAR vs)’
 >- (simp [Abbr ‘M1’] \\
     qabbrev_tac ‘t = VAR y @* args’ \\
     simp [GSYM MAP_DROP] \\
     Know ‘MAP VAR vs = MAP VAR xs ++ MAP VAR (DROP n vs)’
     >- (REWRITE_TAC [GSYM MAP_APPEND] >> AP_TERM_TAC \\
         rw [Abbr ‘xs’, TAKE_DROP]) >> Rewr' \\
     REWRITE_TAC [appstar_APPEND] \\
     qabbrev_tac ‘l = MAP VAR (DROP n vs)’ \\
     MATCH_MP_TAC principle_hnf_beta_reduce_ext \\
     rw [Abbr ‘t’, hnf_appstar])
 >> DISCH_TAC
 >> ‘hnf M1’ by rw [GSYM appstar_APPEND, hnf_appstar]
 >> Know ‘M0 @* MAP VAR vs ==
          LAMl xs (VAR y @* args) @* MAP VAR xs @* MAP VAR (DROP n vs)’
 >- (Know ‘MAP VAR vs = MAP VAR xs ++ MAP VAR (DROP n vs)’
     >- (REWRITE_TAC [GSYM MAP_APPEND] >> AP_TERM_TAC \\
         rw [Abbr ‘xs’, TAKE_DROP]) >> Rewr' \\
     simp [appstar_APPEND])
 >> DISCH_TAC
 >> qabbrev_tac ‘l = MAP VAR (DROP n vs)’
 >> qabbrev_tac ‘t = VAR y @* args’
 >> Know ‘LAMl xs t @* MAP VAR xs @* l == t @* l’
 >- (MATCH_MP_TAC lameq_appstar_cong >> rw [])
 >> DISCH_TAC
 >> ‘M0 @* MAP VAR vs == t @* l’ by PROVE_TAC [lameq_TRANS]
 >> Suff ‘solvable (t @* l)’ >- PROVE_TAC [lameq_solvable_cong]
 >> REWRITE_TAC [solvable_iff_has_hnf]
 >> MATCH_MP_TAC hnf_has_hnf
 >> simp [Abbr ‘t’, GSYM appstar_APPEND, hnf_appstar]
QED

Theorem solvable_appstar' :
    !X M r M0 n vs.
           FINITE X /\ FV M SUBSET X UNION RANK r /\
           solvable M /\
           M0 = principle_hnf M /\
            n = LAMl_size M0 /\
           vs = RNEWS r n X
       ==> solvable (M0 @* MAP VAR vs)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC solvable_appstar
 >> qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘n’] >> simp []
QED

(* NOTE: Essentially, ‘hnf_children_size (principle_hnf M)’ is irrelevant with
         the excluding list. This lemma shows the equivalence in defining ‘m’.
 *)
Theorem hnf_children_size_alt :
    !X M r M0 n vs M1 Ms.
         FINITE X /\ FV M SUBSET X UNION RANK r /\ solvable M /\
         M0 = principle_hnf M /\
          n = LAMl_size M0 /\
         vs = RNEWS r n X /\
         M1 = principle_hnf (M0 @* MAP VAR vs) /\
         Ms = hnf_children M1
     ==> hnf_children_size M0 = LENGTH Ms
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
QED

Theorem subterm_of_solvables :
    !X M h p r. solvable M ==>
       subterm X M (h::p) r =
         let M0 = principle_hnf M;
              n = LAMl_size M0;
             vs = RNEWS r n X;
             M1 = principle_hnf (M0 @* MAP VAR vs);
             Ms = hnf_children M1;
              m = LENGTH Ms
         in
            if h < m then subterm X (EL h Ms) p (SUC r) else NONE
Proof
    rw [subterm_def]
QED

(* NOTE: With [hnf_children_size_alt] now we are ready to prove this alternative
         definition of ‘subterm’.
 *)
Theorem subterm_alt :
    !X M h p r. FINITE X /\ FV M SUBSET X UNION RANK r ==>
       subterm X M (h::p) r =
       if solvable M then
         let M0 = principle_hnf M;
              n = LAMl_size M0;
              m = hnf_children_size M0;
             vs = RNEWS r n X;
             M1 = principle_hnf (M0 @* MAP VAR vs);
             Ms = hnf_children M1
         in
             if h < m then subterm X (EL h Ms) p (SUC r)
             else NONE
       else
         NONE
Proof
    RW_TAC std_ss [subterm_def]
 >> ‘n = n'’ by rw [Abbr ‘n’, Abbr ‘n'’]
 >> POP_ASSUM (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
 >> Suff ‘m = m'’ >- rw []
 >> qunabbrevl_tac [‘m’, ‘m'’]
 >> MATCH_MP_TAC hnf_children_size_alt
 >> qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘vs’, ‘M1’] >> simp []
QED

(* This is the meaning of Boehm tree nodes, ‘fromNote’ translated from BT nodes
   to lambda terms in form of ‘SOME (LAMl vs (VAR y))’ or ‘NONE’.
 *)
Definition fromNode_def :
    fromNode = OPTION_MAP (\(vs,y). LAMl vs (VAR y))
End

(* Boehm tree of a single (free) variable ‘VAR y’ *)
Definition BT_VAR_def :
    BT_VAR y :boehm_tree = Branch (SOME ([],y)) LNIL
End

(* Remarks 10.1.3 (iii) [1, p.216]: unsolvable terms all have the same Boehm
   tree (‘bot’). The following overloaded ‘bot’ may be returned by
  ‘THE (ltree_lookup A p)’ when looking up a terminal node of the Boehm tree.

   See also BT_ltree_lookup_of_unsolvables and BT_ltree_el_of_unsolvables, for
   the raison d'etre of overloading "bot" on two different terms.
 *)
Overload bot = “Branch NONE (LNIL :boehm_tree llist)”

(* Another form of ‘bot’, usually returned by “THE (ltree_el A p)” *)
Overload bot = “(NONE, SOME 0) :(BT_node # num option)”

(* Unicode name: "base" *)
val _ = Unicode.unicode_version {u = UTF8.chr 0x22A5, tmnm = "bot"};
val _ = TeX_notation {hol = "bot", TeX = ("\\ensuremath{\\bot}", 1)};

Theorem BT_of_unsolvables :
    !X M r. unsolvable M ==> BT' X M r = bot
Proof
    rw [BT_def, BT_generator_def, ltree_unfold, ltree_map]
QED

Theorem BT_of_unsolvables_cong :
    !X M N r. unsolvable M /\ unsolvable N ==> BT' X M r = BT' X N r
Proof
    rw [BT_of_unsolvables]
QED

Theorem BT_of_principle_hnf :
    !X M r. solvable M ==> BT' X (principle_hnf M) r = BT' X M r
Proof
    reverse (RW_TAC std_ss [BT_def, BT_generator_def, ltree_unfold])
 >- (Q.PAT_X_ASSUM ‘unsolvable M0’ MP_TAC >> simp [] \\
     rw [Abbr ‘M0’, solvable_iff_has_hnf] \\
     MATCH_MP_TAC hnf_has_hnf \\
     MATCH_MP_TAC hnf_principle_hnf' >> art [])
 >> ‘M0' = M0’ by rw [Abbr ‘M0'’, Abbr ‘M0’, principle_hnf_stable']
 >> qunabbrev_tac ‘M0'’
 >> POP_ASSUM (rfs o wrap)
 >> ‘principle_hnf M0 = M0’ by rw [Abbr ‘M0’, principle_hnf_stable']
 >> POP_ASSUM (rfs o wrap)
QED

Theorem BT_finite_branching :
    !X M r. finite_branching (BT' X M r)
Proof
    rpt GEN_TAC
 >> irule finite_branching_coind'
 >> Q.EXISTS_TAC ‘\b. ?X M r. b = BT' X M r’
 >> rw [] >- (qexistsl_tac [‘X’, ‘M’, ‘r’] >> rw [])
 (* stage work *)
 >> qabbrev_tac ‘A = BT' X M r’
 >> qabbrev_tac ‘a = ltree_node A’
 >> qabbrev_tac ‘ts = ltree_children A’
 >> qexistsl_tac [‘a’, ‘ts’]
 (* A = Branch a ts *)
 >> CONJ_TAC >- rw [Abbr ‘a’, Abbr ‘ts’]
 (* LFINITE ts *)
 >> CONJ_TAC
 >- rw [Abbr ‘A’, Abbr ‘ts’, BT_def, BT_generator_def, Once ltree_unfold,
        LFINITE_fromList]
 >> qabbrev_tac ‘P = \b. ?X M r. b = BT' X M r’
 (* stage work *)
 >> reverse (RW_TAC std_ss [Abbr ‘A’, Abbr ‘ts’, BT_def, BT_generator_def,
                            Once ltree_unfold])
 >- rw []
 >> rw [every_fromList_EVERY, LMAP_fromList, EVERY_MAP, Abbr ‘P’, EVERY_MEM,
        Abbr ‘l’]
 >> rename1 ‘MEM N Ms’
 >> qexistsl_tac [‘X’, ‘N’, ‘SUC r’] >> rw [BT_def]
QED

Theorem subterm_rank_lemma :
    !p X M N r r'. FINITE X /\ FV M SUBSET X UNION RANK r /\
                   subterm X M p r = SOME (N,r')
               ==> r' = r + LENGTH p /\ FV N SUBSET X UNION RANK r'
Proof
    Induct_on ‘p’ >- NTAC 2 (rw [])
 >> rpt GEN_TAC
 >> reverse (Cases_on ‘solvable M’) >- rw [subterm_def]
 >> UNBETA_TAC [subterm_of_solvables] “subterm X M (h::p) r”
 >> STRIP_TAC
 >> qabbrev_tac ‘M' = EL h Ms’
 >> Q.PAT_X_ASSUM ‘!X M N r r'. P’
      (MP_TAC o (Q.SPECL [‘X’, ‘M'’, ‘N’, ‘SUC r’, ‘r'’]))
 >> simp []
 >> Suff ‘FV M' SUBSET X UNION RANK (SUC r)’
 >- rw []
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> ‘Ms = args’ by rw [Abbr ‘Ms’]
 >> POP_ASSUM (rfs o wrap o SYM)
 >> Know ‘!i. i < LENGTH Ms ==> FV (EL i Ms) SUBSET FV M1’
 >- (MATCH_MP_TAC hnf_children_FV_SUBSET \\
     simp [hnf_appstar])
 >> DISCH_TAC
 >> qunabbrev_tac ‘M'’
 >> qabbrev_tac ‘Y  = RANK r’
 >> qabbrev_tac ‘Y' = RANK (SUC r)’
 (* transitivity no.1 *)
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M1’
 >> CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw [])
 (* transitivity no.2 *)
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M0 UNION set vs’
 >> CONJ_TAC >- simp [FV_LAMl]
 (* transitivity no.3 *)
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M UNION set vs’
 >> CONJ_TAC
 >- (Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> rw [SUBSET_DEF, IN_UNION]
 >- (Know ‘x IN X UNION Y’ >- METIS_TAC [SUBSET_DEF] \\
     rw [IN_UNION] >- (DISJ1_TAC >> art []) \\
     DISJ2_TAC \\
     Suff ‘Y SUBSET Y'’ >- METIS_TAC [SUBSET_DEF] \\
     qunabbrevl_tac [‘Y’, ‘Y'’] \\
     MATCH_MP_TAC RANK_MONO >> rw [])
 >> DISJ2_TAC
 >> Suff ‘set vs SUBSET Y'’ >- METIS_TAC [SUBSET_DEF]
 >> qunabbrevl_tac [‘vs’, ‘Y'’]
 >> MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw []
QED

Theorem subterm_induction_lemma :
    !X M r M0 n n' m vs M1 Ms h.
           FINITE X /\ FV M SUBSET X UNION RANK r /\
           solvable M /\
           M0 = principle_hnf M /\
            n = LAMl_size M0 /\
            m = hnf_children_size M0 /\
           vs = RNEWS r n' X /\ n <= n' /\
           M1 = principle_hnf (M0 @* MAP VAR vs) /\
           Ms = hnf_children M1 /\ h < m
       ==> FV (EL h Ms) SUBSET X UNION RANK (SUC r)
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> ‘hnf M0’ by PROVE_TAC [hnf_principle_hnf']
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n' :num”)) ‘X’
 >> Know ‘?y args. M0 = LAMl (TAKE n vs) (VAR y @* args)’
 >- (rw [Abbr ‘n’] >> irule (iffLR hnf_cases_shared) >> rw [] \\
     MATCH_MP_TAC subterm_disjoint_lemma' \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘LENGTH vs’] >> rw [])
 >> STRIP_TAC
 >> qabbrev_tac ‘xs = TAKE n vs’
 >> qabbrev_tac ‘m = hnf_children_size M0’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> Know ‘M1 = VAR y @* args @* DROP n (MAP VAR vs)’
 >- (simp [Abbr ‘M1’] \\
     qabbrev_tac ‘t = VAR y @* args’ \\
     simp [GSYM MAP_DROP] \\
     Know ‘MAP VAR vs = MAP VAR xs ++ MAP VAR (DROP n vs)’
     >- (REWRITE_TAC [GSYM MAP_APPEND] >> AP_TERM_TAC \\
         rw [Abbr ‘xs’, TAKE_DROP]) >> Rewr' \\
     REWRITE_TAC [appstar_APPEND] \\
     qabbrev_tac ‘l = MAP VAR (DROP n vs)’ \\
     MATCH_MP_TAC principle_hnf_beta_reduce_ext \\
     rw [Abbr ‘t’, hnf_appstar])
 >> DISCH_TAC
 >> ‘hnf M1’ by rw [GSYM appstar_APPEND, hnf_appstar]
 >> ‘LENGTH args = m’ by rw [Abbr ‘m’]
 (* 1st SUBSET_TRANS *)
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M1’
 >> CONJ_TAC
 >- (irule hnf_children_FV_SUBSET \\
     rw [GSYM appstar_APPEND, hnf_appstar])
 (* 2nd SUBSET_TRANS *)
 >> Know ‘solvable (M0 @* MAP VAR vs)’
 >- (MATCH_MP_TAC solvable_appstar \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘n'’] >> simp [])
 >> DISCH_TAC
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV (M0 @* MAP VAR vs)’
 >> CONJ_TAC
 >- (qunabbrev_tac ‘M1’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> Q.PAT_X_ASSUM ‘M0 = LAMl xs (VAR y @* args)’ K_TAC
 >> rw [SUBSET_DEF, FV_appstar]
 >> Know ‘x IN FV M UNION set vs’
 >- (POP_ASSUM MP_TAC \\
     Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> POP_ASSUM K_TAC
 >> rw [Once IN_UNION]
 >- (Know ‘x IN X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
     Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
     rw [RANK_MONO])
 >> Know ‘set vs SUBSET RANK (SUC r)’
 >- (qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw [])
 >> DISCH_TAC
 >> Know ‘x IN RANK (SUC r)’ >- METIS_TAC [SUBSET_DEF]
 >> SET_TAC []
QED

Theorem subterm_induction_lemma' :
    !X M r M0 n m vs M1 Ms h.
           FINITE X /\ FV M SUBSET X UNION RANK r /\
           solvable M /\
           M0 = principle_hnf M /\
            n = LAMl_size M0 /\
            m = hnf_children_size M0 /\
           vs = RNEWS r n X /\
           M1 = principle_hnf (M0 @* MAP VAR vs) /\
           Ms = hnf_children M1 /\ h < m
       ==> FV (EL h Ms) SUBSET X UNION RANK (SUC r)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC subterm_induction_lemma
 >> qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []
QED

Theorem FV_subterm_lemma :
    !X M r M0 n m vs M1 Ms h.
           FINITE X /\ FV M SUBSET X UNION RANK r /\
           solvable M /\
           M0 = principle_hnf M /\
            n = LAMl_size M0 /\
           vs = RNEWS r n X /\
           M1 = principle_hnf (M0 @* MAP VAR vs) /\
           Ms = hnf_children M1 /\
            m = LENGTH Ms /\
            h < m
       ==> FV (EL h Ms) SUBSET FV M UNION set vs
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> ‘DISJOINT (set vs) (FV M0)’ by PROVE_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> rfs []
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> qunabbrev_tac ‘M1’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> ‘hnf M1’ by rw [hnf_appstar]
 >> Q.PAT_X_ASSUM ‘M0 = _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = _’ (ASSUME_TAC o SYM)
 >> ‘hnf_children M1 = args’ by rw [hnf_children_hnf]
 >> POP_ASSUM (rfs o wrap)
 >> Know ‘FV (principle_hnf (M0 @* MAP VAR vs)) SUBSET FV (M0 @* MAP VAR vs)’
 >- (MATCH_MP_TAC principle_hnf_FV_SUBSET' \\
    ‘solvable M1’ by rw [solvable_iff_has_hnf, hnf_has_hnf] \\
     Suff ‘M0 @* MAP VAR vs == M1’ >- PROVE_TAC [lameq_solvable_cong] \\
     rw [])
 >> simp []
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
 >> DISCH_TAC
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M0 UNION set vs’
 >> reverse CONJ_TAC
 >- (Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV (VAR y @* args)’ >> art []
 >> POP_ASSUM K_TAC
 >> rw [FV_appstar, SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNION]
 >> DISJ2_TAC
 >> Q.EXISTS_TAC ‘EL h args’ >> art []
 >> MATCH_MP_TAC EL_MEM >> art []
QED

(* NOTE: This lemma is suitable for doing induction. A better upper bound is
   given by the next [subterm_headvar_lemma'].
 *)
Theorem subterm_headvar_lemma :
    !X M r M0 n vs M1.
           FINITE X /\ FV M SUBSET X UNION RANK r /\
           solvable M /\
           M0 = principle_hnf M /\
            n = LAMl_size M0 /\
           vs = RNEWS r n X /\
           M1 = principle_hnf (M0 @* MAP VAR vs)
       ==> hnf_headvar M1 IN X UNION RANK (SUC r)
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n  = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> Know ‘solvable (M0 @* MAP VAR vs)’
 >- (MATCH_MP_TAC solvable_appstar \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘n’] >> simp [])
 >> DISCH_TAC
 >> Suff ‘FV M1 SUBSET X UNION RANK (SUC r)’
 >- rw [SUBSET_DEF, FV_appstar, IN_UNION]
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘FV (M0 @* MAP VAR vs)’
 >> CONJ_TAC >- (qunabbrev_tac ‘M1’ \\
                 MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> REWRITE_TAC [FV_appstar_MAP_VAR]
 >> Q.PAT_X_ASSUM ‘M0 = _’ K_TAC
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘FV M UNION set vs’
 >> CONJ_TAC >- (Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
                 qunabbrev_tac ‘M0’ \\
                 MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> rw [Abbr ‘vs’, SUBSET_DEF, IN_UNION]
 >- (Know ‘x IN X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
     Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
     rw [RANK_MONO])
 >> DISJ2_TAC
 >> Suff ‘set (RNEWS r n X) SUBSET RANK (SUC r)’ >- rw [SUBSET_DEF]
 >> rw [RNEWS_SUBSET_RANK]
QED

(* NOTE: If ‘vs’ is longer than ‘n’, then ‘hnf_headvar M1’ uses at most
   variables from ‘set (TAKE n vs). This result generalizes above lemmas.
 *)
Theorem subterm_headvar_lemma_alt :
    !X M r M0 n n' vs M1.
           FINITE X /\ FV M SUBSET X UNION RANK r /\
           solvable M /\
           M0 = principle_hnf M /\
            n = LAMl_size M0 /\
           vs = RNEWS r n' X /\ n <= n' /\
           M1 = principle_hnf (M0 @* MAP VAR vs)
       ==> hnf_headvar M1 IN FV M UNION set (TAKE n vs)
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n' :num”)) ‘X’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> ‘DISJOINT (set vs) (FV M0)’ by PROVE_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> rfs []
 >> qabbrev_tac ‘xs = TAKE n vs’
 >> Q.PAT_X_ASSUM ‘M1 = _’ K_TAC
 >> Q.PAT_X_ASSUM ‘M0 = _’ (ASSUME_TAC o SYM) >> simp []
 (* redefine M1 *)
 >> qunabbrev_tac ‘M1’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 (* applying principle_hnf_beta_reduce_ext *)
 >> Know ‘M1 = VAR y @* args @* DROP n (MAP VAR vs)’
 >- (qunabbrev_tac ‘M1’ \\
     qabbrev_tac ‘t = VAR y @* args’ \\
     rw [GSYM MAP_DROP] \\
     Know ‘MAP VAR vs = MAP VAR xs ++ MAP VAR (DROP n vs)’
     >- (REWRITE_TAC [GSYM MAP_APPEND] >> AP_TERM_TAC \\
         rw [Abbr ‘xs’, TAKE_DROP]) >> Rewr' \\
     REWRITE_TAC [appstar_APPEND] \\
     qabbrev_tac ‘l = MAP VAR (DROP n vs)’ \\
     MATCH_MP_TAC principle_hnf_beta_reduce_ext \\
     rw [Abbr ‘t’, hnf_appstar])
 >> DISCH_TAC
 >> ‘hnf M1’ by rw [hnf_appstar]
 >> Q.PAT_X_ASSUM ‘M1 = _’ (ASSUME_TAC o SYM)
 >> Know ‘hnf_headvar M1 = y’
 >- (POP_ASSUM (REWRITE_TAC o wrap o SYM) \\
     simp [GSYM appstar_APPEND])
 >> Rewr'
 >> qabbrev_tac ‘M1' = principle_hnf (M0 @* MAP VAR xs)’
 >> Know ‘M1' = VAR y @* args’
 >- (qunabbrev_tac ‘M1'’ \\
     qabbrev_tac ‘t = VAR y @* args’ \\
     Q.PAT_X_ASSUM ‘_ = M0’ (REWRITE_TAC o wrap o SYM) \\
     MATCH_MP_TAC principle_hnf_beta_reduce \\
     rw [Abbr ‘t’, hnf_appstar])
 >> DISCH_THEN (ASSUME_TAC o SYM)
 >> Know ‘FV (principle_hnf (M0 @* MAP VAR xs)) SUBSET FV (M0 @* MAP VAR xs)’
 >- (MATCH_MP_TAC principle_hnf_FV_SUBSET' \\
    ‘solvable M1'’ by rw [solvable_iff_has_hnf, hnf_has_hnf, hnf_appstar] \\
     Suff ‘M0 @* MAP VAR xs == M1'’ >- PROVE_TAC [lameq_solvable_cong] \\
     Q.PAT_X_ASSUM ‘_ = M0’ (REWRITE_TAC o wrap o SYM) \\
     simp [])
 >> simp []
 (* expand M1' *)
 >> POP_ASSUM (REWRITE_TAC o wrap o SYM)
 >> simp [FV_appstar]
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘y IN _’ MP_TAC
 >> Suff ‘FV M0 SUBSET FV M’ >- SET_TAC []
 >> qunabbrev_tac ‘M0’
 >> MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []
QED

Theorem subterm_headvar_lemma' :
    !X M r M0 n vs M1.
           FINITE X /\ FV M SUBSET X UNION RANK r /\
           solvable M /\
           M0 = principle_hnf M /\
            n = LAMl_size M0 /\
           vs = RNEWS r n X /\
           M1 = principle_hnf (M0 @* MAP VAR vs)
       ==> hnf_headvar M1 IN FV M UNION set vs
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> ‘vs = TAKE n vs’ by rw [] >> POP_ORW
 >> MATCH_MP_TAC subterm_headvar_lemma_alt
 >> qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’] >> simp []
QED

(* Proposition 10.1.6 [1, p.219] *)
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

(* NOTE: This theorem indicates that ‘m = LENGTH Ms’ is more natural. *)
Theorem BT_ltree_el_NIL[local] :
    !X M r. ltree_el (BT' X M r) [] =
          if solvable M then
             let
               M0 = principle_hnf M;
                n = LAMl_size M0;
               vs = RNEWS r n X;
               M1 = principle_hnf (M0 @* MAP VAR vs);
               Ms = hnf_children M1;
                y = hnf_headvar M1;
                l = MAP (\e. (e,SUC r)) Ms;
                m = LENGTH Ms;
             in
               SOME (SOME (vs,y),SOME m)
          else
               SOME (NONE,SOME 0)
Proof
    rw [BT_def, Once ltree_unfold, BT_generator_def, ltree_el_def]
 >> simp [LMAP_fromList]
QED

(* This version uses ‘m = hnf_children_size M0’ *)
Theorem BT_ltree_el_NIL_alt[local] :
    !X M r. FINITE X /\ FV M SUBSET X UNION RANK r ==>
          ltree_el (BT' X M r) [] =
          if solvable M then
             let
               M0 = principle_hnf M;
                n = LAMl_size M0;
                m = hnf_children_size M0;
               vs = RNEWS r n X;
               M1 = principle_hnf (M0 @* MAP VAR vs);
               Ms = hnf_children M1;
                y = hnf_headvar M1;
                l = MAP (\e. (e,SUC r)) Ms
             in
               SOME (SOME (vs,y),SOME m)
          else
               SOME (NONE,SOME 0)
Proof
    RW_TAC std_ss [BT_ltree_el_NIL]
 >> ‘n = n'’ by rw [Abbr ‘n’, Abbr ‘n'’]
 >> POP_ASSUM (rfs o wrap o SYM)
 >> qunabbrevl_tac [‘m’, ‘m'’]
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> MATCH_MP_TAC hnf_children_size_alt
 >> qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘vs’, ‘M1’] >> simp []
QED

(*---------------------------------------------------------------------------*
 *  More subterm properties
 *---------------------------------------------------------------------------*)

(* M0 is not needed if M is already an hnf *)
Theorem subterm_of_hnf :
    !X M h p r. FINITE X /\ hnf M ==>
      subterm X M (h::p) r =
        let  n = LAMl_size M;
            vs = RNEWS r n X;
            M1 = principle_hnf (M @* MAP VAR vs);
            Ms = hnf_children M1;
             m = LENGTH Ms;
        in
            if h < m then subterm X (EL h Ms) p (SUC r) else NONE
Proof
    rpt STRIP_TAC
 >> ‘solvable M’ by PROVE_TAC [solvable_iff_has_hnf, hnf_has_hnf]
 >> RW_TAC std_ss [subterm_of_solvables]
 >> ‘M0 = M’ by rw [Abbr ‘M0’, principle_hnf_reduce]
 >> POP_ASSUM (fs o wrap)
 >> Q.PAT_X_ASSUM ‘n' = n’   (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs' = vs’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1' = M1’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms' = Ms’ (fs o wrap o SYM)
QED

Theorem subterm_of_hnf_alt :
    !X M h p r. FINITE X /\ FV M SUBSET X UNION RANK r /\ hnf M ==>
      subterm X M (h::p) r =
        let  n = LAMl_size M;
             m = hnf_children_size M;
            vs = RNEWS r n X;
            M1 = principle_hnf (M @* MAP VAR vs);
            Ms = hnf_children M1
        in
            if h < m then subterm X (EL h Ms) p (SUC r) else NONE
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘solvable M’ by PROVE_TAC [solvable_iff_has_hnf, hnf_has_hnf]
 >> RW_TAC std_ss [subterm_alt]
 >> ‘M0 = M’ by rw [Abbr ‘M0’, principle_hnf_reduce]
 >> POP_ASSUM (fs o wrap)
 >> Q.PAT_X_ASSUM ‘n' = n’   (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs' = vs’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1' = M1’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms' = Ms’ (fs o wrap o SYM)
QED

(* In the extreme case, M is a absfree hnf (i.e. VAR y @* args), and the
   definition of subterm can be greatly simplified.
 *)
Theorem subterm_of_absfree_hnf :
    !X M h p r. hnf M /\ ~is_abs M ==>
       subterm X M (h::p) r =
       let Ms = hnf_children M;
            m = LENGTH Ms
       in
           if h < m then subterm X (EL h Ms) p (SUC r) else NONE
Proof
    rpt STRIP_TAC
 >> ‘solvable M’ by PROVE_TAC [solvable_iff_has_hnf, hnf_has_hnf]
 >> RW_TAC std_ss [subterm_of_solvables]
 >> ‘M0 = M’ by rw [Abbr ‘M0’, principle_hnf_reduce]
 >> fs [Abbr ‘M0’]
 >> Know ‘n = 0’
 >- (qunabbrev_tac ‘n’ \\
     MATCH_MP_TAC LAMl_size_eq_0 >> art [])
 >> DISCH_THEN (fs o wrap)
 >> fs [Abbr ‘vs’]
 >> Q.PAT_X_ASSUM ‘Ms' = Ms’ (fs o wrap o SYM)
QED

Theorem subterm_of_absfree_hnf_explicit :
    !X y Ms h p r.
       subterm X (VAR y @* Ms) (h::p) r =
       if h < LENGTH Ms then
          subterm X (EL h Ms) p (SUC r)
       else
          NONE
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘VAR y @* Ms’, ‘h’, ‘p’, ‘r’] subterm_of_absfree_hnf)
 >> rw [hnf_appstar, is_abs_appstar]
QED

Theorem subterm_of_principle_hnf :
    !X M p r. solvable M /\ p <> [] ==>
              subterm X (principle_hnf M) p r = subterm X M p r
Proof
    rpt STRIP_TAC
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> Cases_on ‘p’ >> fs []
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> ‘solvable M0’ by PROVE_TAC [solvable_principle_hnf]
 >> RW_TAC std_ss [subterm_of_solvables]
 >> ‘M0' = M0’ by rw [Abbr ‘M0'’, Abbr ‘M0’, principle_hnf_stable']
 >> POP_ASSUM (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘n = n'’   (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
QED

(* NOTE: When subterm X M p = NONE, either 1) M or its subterm is unsolvable,
   or 2) p runs out of ltree_paths (BT X M). If we knew subterm X M p <> NONE
   a priori, then p IN ltree_paths (BT X M) must hold.
 *)
Theorem subterm_imp_ltree_paths :
    !p X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              subterm X M p r <> NONE ==>
              p IN ltree_paths (BT' X M r)
Proof
    Induct_on ‘p’ >- rw []
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> POP_ASSUM MP_TAC (* subterm X M (h::p) r <> NONE *)
 >> reverse (Cases_on ‘solvable M’)
 >- simp [subterm_def, ltree_paths_def, ltree_lookup]
 >> UNBETA_TAC [subterm_alt] “subterm X M (h::p) r”
 >> UNBETA_TAC [BT_def, Once ltree_unfold, BT_generator_def] “BT' X M r”
 >> simp [LMAP_fromList, EL_MAP, Abbr ‘l’]
 >> ‘n = n'’ by rw [Abbr ‘n’, Abbr ‘n'’]
 >> POP_ASSUM (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 (* extra work *)
 >> qunabbrev_tac ‘y’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> Cases_on ‘h < m’ >> simp []
 >> ‘Ms = args’ by rw [Abbr ‘Ms’]
 >> POP_ASSUM (fs o wrap)
 >> DISCH_TAC
 >> simp [GSYM BT_def]
 >> fs [ltree_paths_def, ltree_lookup_def, LNTH_fromList, EL_MAP]
 >> T_TAC
 (* extra work *)
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> MATCH_MP_TAC subterm_induction_lemma'
 >> qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []
QED

(* ltree_lookup returns more information (the entire subtree), thus can be
   used to construct the return value of ltree_el.

   NOTE: This theorem connects ‘ltree_el’ and ‘ltree_lookup’ for Boehm trees

   |- !X M p r.
         p IN ltree_paths (BT' X M r) ==>
         ltree_el (BT' X M r) p =
         do t' <- ltree_lookup (BT' X M r) p;
            SOME (ltree_node t',LLENGTH (ltree_children t'))
         od
 *)
Theorem BT_ltree_el_thm =
        ltree_el_alt_ltree_lookup |> INST_TYPE [“:'a” |-> “:BT_node”]
                                  |> Q.SPECL [‘p’, ‘BT' X M r’]
                                  |> Q.GENL [‘X’, ‘M’, ‘p’, ‘r’]

(* Lemma 10.1.15 [1, p.222] (subterm and ltree_lookup) *)
Theorem BT_subterm_lemma :
    !p X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              subterm X M p r <> NONE ==>
              ltree_lookup (BT' X M r) p <> NONE /\
              BT X (THE (subterm X M p r)) = THE (ltree_lookup (BT' X M r) p)
Proof
    Induct_on ‘p’
 >- rw [subterm_def, ltree_lookup_def]
 >> rpt GEN_TAC
 >> UNBETA_TAC [subterm_def] “subterm X M (h::p) r”
 >> UNBETA_TAC [BT_def, Once ltree_unfold, BT_generator_def] “BT' X M r”
 >> simp [LMAP_fromList, EL_MAP, Abbr ‘l’]
 >> ‘n = n'’ by rw [Abbr ‘n’, Abbr ‘n'’]
 >> POP_ASSUM (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
 >> STRIP_TAC
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 (* extra work *)
 >> qabbrev_tac ‘Y = RANK r’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> qunabbrev_tac ‘y’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> simp [ltree_lookup, LNTH_fromList, EL_MAP, GSYM BT_def]
 >> ‘Ms = args’ by rw [Abbr ‘Ms’]
 >> POP_ASSUM (rfs o wrap)
 (* extra work *)
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> MATCH_MP_TAC subterm_induction_lemma'
 >> qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []
QED

(* NOTE: In the above theorem, when the antecedents hold, i.e.

         p IN ltree_paths (BT X M) /\ subterm X M p = NONE

   Then ‘subterm' X M (FRONT p)’ must be an unsolvable term. This result can be
   even improved to an iff, as the present theorem shows.
 *)
Theorem subterm_is_none_iff_parent_unsolvable :
    !p X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              p IN ltree_paths (BT' X M r) ==>
             (subterm X M p r = NONE <=>
              p <> [] /\ subterm X M (FRONT p) r <> NONE /\
              unsolvable (subterm' X M (FRONT p) r))
Proof
    Induct_on ‘p’ >- rw [subterm_def]
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> reverse (Cases_on ‘solvable M’)
 >- (Q.PAT_X_ASSUM ‘h::p IN ltree_paths (BT' X M r)’ MP_TAC \\
     simp [subterm_def, BT_of_unsolvables, ltree_paths_def, ltree_lookup_def])
 >> UNBETA_TAC [subterm_of_solvables] “subterm X M (h::p) r”
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> qabbrev_tac ‘Y = RANK r’
 >> Know ‘DISJOINT (set vs) (FV M0)’
 >- (MATCH_MP_TAC subterm_disjoint_lemma' \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’] >> simp [])
 >> DISCH_TAC
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> ‘Ms = args’ by rw [Abbr ‘Ms’]
 >> POP_ASSUM (rfs o wrap)
 >> qunabbrev_tac ‘Ms’
 (* stage work, now M is solvable *)
 >> Cases_on ‘p = []’
 >- (rw [subterm_NIL] \\
     Q.PAT_X_ASSUM ‘[h] IN ltree_paths (BT' X M r)’ MP_TAC \\
     simp [BT_def, Once ltree_unfold, BT_generator_def, ltree_paths_def,
           ltree_lookup_def, LNTH_fromList] \\
     Cases_on ‘h < m’ >> simp [])
 (* now: p <> [] *)
 >> Know ‘h < m’
 >- (Q.PAT_X_ASSUM ‘h::p IN ltree_paths (BT' X M r)’ MP_TAC \\
     simp [BT_def, Once ltree_unfold, BT_generator_def, ltree_paths_def,
           ltree_lookup_def, LNTH_fromList, EL_MAP] \\
     fs [] \\
     Cases_on ‘h < m’ >> simp [])
 >> DISCH_TAC
 >> simp [FRONT_DEF]
 (* stage work *)
 >> qabbrev_tac ‘N = EL h args’
 >> Know ‘subterm X M (h::FRONT p) r = subterm X N (FRONT p) (SUC r)’
 >- rw [subterm_def]
 >> Rewr'
 >> Q.PAT_X_ASSUM ‘p <> []’ (rfs o wrap)
 >> FIRST_X_ASSUM MATCH_MP_TAC
 (* p IN ltree_paths (BT X N) *)
 >> Q.PAT_X_ASSUM ‘h::p IN ltree_paths (BT' X M r)’ MP_TAC
 >> simp [BT_def, Once ltree_unfold, BT_generator_def, ltree_paths_def,
          ltree_lookup_def, LNTH_fromList, EL_MAP]
 >> fs []
 >> DISCH_THEN K_TAC >> T_TAC
 >> qunabbrev_tac ‘N’
 >> MATCH_MP_TAC subterm_induction_lemma'
 >> qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []
QED

Theorem subterm_is_none_exclusive :
    !p X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              p IN ltree_paths (BT' X M r) /\
              subterm X M p r = NONE ==> subterm X M (FRONT p) r <> NONE
Proof
    METIS_TAC [subterm_is_none_iff_parent_unsolvable]
QED

(* NOTE: for whatever reasons such that ‘subterm X M p = NONE’, even when
        ‘p NOTIN ltree_paths (BT X M)’, the conclusion (rhs) always holds.
 *)
Theorem subterm_is_none_inclusive :
    !X M p r. subterm X M p r = NONE <=>
              !q. p <<= q ==> subterm X M q r = NONE
Proof
    rpt GEN_TAC
 >> reverse EQ_TAC
 >- (DISCH_THEN (MP_TAC o (Q.SPEC ‘p’)) >> rw [])
 >> Q.ID_SPEC_TAC ‘r’
 >> Q.ID_SPEC_TAC ‘M’
 >> Q.ID_SPEC_TAC ‘X’
 >> Q.ID_SPEC_TAC ‘p’
 >> Induct_on ‘p’ >- rw [subterm_NIL]
 >> rw [subterm_def]
 >> Cases_on ‘q’ >> fs [subterm_def]
QED

Theorem subterm_solvable_lemma :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              p <> [] /\ subterm X M p r <> NONE ==>
            (!q. q <<= p ==> subterm X M q r <> NONE) /\
            (!q. q <<= FRONT p ==> solvable (subterm' X M q r))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘p IN ltree_paths (BT' X M r)’ by PROVE_TAC [subterm_imp_ltree_paths]
 >> CONJ_ASM1_TAC
 >- (Q.X_GEN_TAC ‘q’ >> DISCH_TAC \\
     CCONTR_TAC \\
     POP_ASSUM (MP_TAC o (REWRITE_RULE [Once subterm_is_none_inclusive])) \\
     DISCH_THEN (MP_TAC o (Q.SPEC ‘p’)) >> rw [])
 >> ‘0 < LENGTH p’ by rw [GSYM NOT_NIL_EQ_LENGTH_NOT_0]
 >> Q.X_GEN_TAC ‘q’
 >> Suff ‘!l. l <> [] /\ l <<= p ==> solvable (subterm' X M (FRONT l) r)’
 >- (DISCH_TAC \\
     DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [IS_PREFIX_EQ_TAKE])) \\
     Know ‘q = FRONT (TAKE (SUC n) p)’
     >- (Know ‘FRONT (TAKE (SUC n) p) = TAKE (SUC n - 1) p’
         >- (MATCH_MP_TAC FRONT_TAKE \\
             rfs [LENGTH_FRONT]) >> Rewr' \\
         POP_ASSUM (ONCE_REWRITE_TAC o wrap) >> simp [] \\
         MATCH_MP_TAC TAKE_FRONT >> rfs [LENGTH_FRONT]) >> Rewr' \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     qabbrev_tac ‘l = TAKE (SUC n) p’ \\
     CONJ_TAC
     >- (rfs [LENGTH_FRONT, NOT_NIL_EQ_LENGTH_NOT_0, Abbr ‘l’, LENGTH_TAKE]) \\
     rw [IS_PREFIX_EQ_TAKE] \\
     Q.EXISTS_TAC ‘SUC n’ >> rw [Abbr ‘l’] \\
     rfs [LENGTH_FRONT])
 >> rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘l’, ‘X’, ‘M’, ‘r’]
                    subterm_is_none_iff_parent_unsolvable)
 >> ‘l IN ltree_paths (BT' X M r)’ by PROVE_TAC [ltree_paths_inclusive]
 >> simp []
 >> Suff ‘subterm X M (FRONT l) r <> NONE’ >- PROVE_TAC []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> MATCH_MP_TAC IS_PREFIX_TRANS
 >> Q.EXISTS_TAC ‘l’ >> rw []
 >> MATCH_MP_TAC IS_PREFIX_BUTLAST' >> art []
QED

(* Lemma 10.1.15 (related) [1, p.222] (subterm and ltree_el)

   Assuming all involved terms are solvable:

   - “ltree_el (BT X M) p” returns ‘SOME (SOME (vs,y),SOME k)’ (ltree node),
   - “subterm X M p” returns ‘(Z,N)’ where N is the actual subterm.

   Then M0 := principle_hnf N has the explicit form: ‘LAMl vs (VAR y @* Ms)’,
   and ‘LENGTH Ms = k’ (NOTE: vs, y and k come from ‘ltree_el (BT X M) p’.

 *)
Theorem BT_subterm_thm :
    !p X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              subterm X M p r <> NONE /\ solvable (subterm' X M p r)
        ==> do (N,r') <- subterm X M p r;
               (t,m') <- ltree_el (BT' X M r) p;
               (xs,y) <- t;
                   m <- m';
                  M0 <<- principle_hnf N;
                   n <<- LAMl_size M0;
                  vs <<- RNEWS r' n X;
                  M1 <<- principle_hnf (M0 @* MAP VAR vs);
              return (vs = xs /\
                      LAMl_size M0 = n /\
                      hnf_children_size M0 = m /\
                      hnf_headvar M1 = y /\
                      DISJOINT (set vs) (FV M0) /\
                      r' = r + LENGTH p /\
                      FV N SUBSET X UNION RANK r')
            od = SOME T
Proof
    rpt STRIP_TAC
 >> ‘p IN ltree_paths (BT' X M r)’ by PROVE_TAC [subterm_imp_ltree_paths]
 >> Know ‘solvable M’
 >- (Cases_on ‘p = []’ >- fs [] \\
    ‘!q. q <<= FRONT p ==> solvable (subterm' X M q r)’
       by PROVE_TAC [cj 2 subterm_solvable_lemma] \\
     POP_ASSUM (MP_TAC o Q.SPEC ‘[]’) >> rw [])
 >> Know ‘ltree_lookup (BT' X M r) p <> NONE /\
          BT X (THE (subterm X M p r)) = THE (ltree_lookup (BT' X M r) p)’
 >- (MATCH_MP_TAC BT_subterm_lemma >> art [])
 >> STRIP_TAC
 >> POP_ASSUM MP_TAC
 >> gs [GSYM IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS]
 >> rename1 ‘subterm X M p r = SOME t’
 >> Cases_on ‘t’ >> fs []
 >> rename1 ‘subterm X M p r = SOME (N,r')’
 >> rw [BT_ltree_el_thm]
 >> UNBETA_TAC [BT_def, Once ltree_unfold, BT_generator_def] “BT' X N r'”
 >> simp [LMAP_fromList, Abbr ‘l’]
(* stage work *)
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r' :num”, “n :num”)) ‘X’
 >> Know ‘DISJOINT (set vs) (FV M0)’
 >- (MATCH_MP_TAC subterm_disjoint_lemma' \\
     qexistsl_tac [‘X’, ‘N’, ‘r'’, ‘n’] >> simp [] \\
     PROVE_TAC [subterm_rank_lemma])
 >> DISCH_TAC
 (* applying subterm_rank_lemma *)
 >> Know ‘r' = r + LENGTH p /\ FV N SUBSET X UNION RANK r'’
 >- (MATCH_MP_TAC subterm_rank_lemma \\
     Q.EXISTS_TAC ‘M’ >> art [])
 >> STRIP_TAC
 >> simp [Abbr ‘y’]
 >> MATCH_MP_TAC hnf_children_size_alt
 >> qexistsl_tac [‘X’, ‘N’, ‘r'’, ‘n’, ‘vs’, ‘M1’] >> simp []
QED

(* This stronger lemma does not require ‘subterm X M p r <> NONE’ *)
Theorem subterm_valid_path_lemma :
    !X p M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              p IN ltree_paths (BT' X M r) /\ p <> [] ==>
              !q. q <<= FRONT p ==> subterm X M q r <> NONE
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Cases_on ‘subterm X M p r = NONE’
 >- (POP_ASSUM MP_TAC \\
     rw [subterm_is_none_iff_parent_unsolvable] \\
     Cases_on ‘FRONT p = []’ >- fs [] \\
     MP_TAC (Q.SPECL [‘X’, ‘M’, ‘FRONT p’, ‘r’] subterm_solvable_lemma) \\
     rw [])
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘p’, ‘r’] subterm_solvable_lemma)
 >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> MATCH_MP_TAC isPREFIX_TRANS
 >> Q.EXISTS_TAC ‘FRONT p’ >> rw [IS_PREFIX_BUTLAST']
QED

Theorem BT_ltree_el_eq_some_none :
    !X M p r m. FINITE X /\ FV M SUBSET X UNION RANK r /\
                ltree_el (BT' X M r) p = SOME (NONE, m) ==> m = SOME 0
Proof
    Suff ‘!X. FINITE X ==>
              !p M r m. FV M SUBSET X UNION RANK r /\
                        ltree_el (BT' X M r) p = SOME (NONE, m) ==> m = SOME 0’
 >- METIS_TAC []
 >> Q.X_GEN_TAC ‘X’ >> DISCH_TAC
 >> Induct_on ‘p’
 >- rw [BT_def, BT_generator_def, ltree_el_def, Once ltree_unfold]
 >> rw [BT_def, BT_generator_def, ltree_el_def, Once ltree_unfold]
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n  = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> gs [LNTH_fromList, GSYM BT_def]
 >> Cases_on ‘h < LENGTH args’ >> fs [EL_MAP]
 >> qabbrev_tac ‘N = EL h args’
 >> Know ‘FV N SUBSET X UNION RANK (SUC r)’
 >- (qunabbrev_tac ‘N’ \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘hnf_children_size M0’, ‘vs’, ‘M1’] \\
     simp [])
 >> DISCH_TAC
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> qexistsl_tac [‘N’, ‘SUC r’] >> art []
QED

(* NOTE: ‘subterm X M p <> NONE’ implies ‘!q. q <<= FRONT p ==> solvable
  (subterm' X M q)’, and the following theorem deals with the case of
  ‘unsolvable (subterm' X M p)’.
 *)
Theorem BT_ltree_el_of_unsolvables :
    !p X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              subterm X M p r <> NONE ==>
             (unsolvable (subterm' X M p r) <=>
              ltree_el (BT' X M r) p = SOME bot)
Proof
    Induct_on ‘p’
 >- (rpt STRIP_TAC \\
     EQ_TAC >- rw [BT_of_unsolvables, ltree_el_def] \\
     rpt STRIP_TAC \\
     fs [BT_ltree_el_NIL])
 >> rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::p’, ‘r’] subterm_solvable_lemma)
 >> rw []
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘[]’))
 >> rw [] (* solvable M *)
 >> Q.PAT_X_ASSUM ‘subterm X M (h::p) r <> NONE’ MP_TAC
 >> Q.PAT_X_ASSUM ‘!q. q <<= h::p ==> subterm X M q r <> NONE’ K_TAC
 >> UNBETA_TAC [subterm_def] “subterm X M (h::p) r”
 >> UNBETA_TAC [BT_def, Once ltree_unfold, BT_generator_def] “BT' X M r”
 >> simp [LMAP_fromList, EL_MAP, Abbr ‘l’]
 >> ‘n = n'’ by rw [Abbr ‘n’, Abbr ‘n'’]
 >> POP_ASSUM (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
 >> simp [LMAP_fromList, GSYM BT_def, ltree_el, LNTH_fromList, EL_MAP]
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 (* extra work *)
 >> qabbrev_tac ‘Y = RANK r’
 >> Know ‘DISJOINT (set vs) (FV M0)’
 >- (MATCH_MP_TAC subterm_disjoint_lemma' \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’] >> simp [])
 >> DISCH_TAC
 >> qunabbrev_tac ‘y’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> Cases_on ‘h < m’ >> simp []
 >> ‘Ms = args’ by rw [Abbr ‘Ms’]
 >> POP_ASSUM (fs o wrap) >> T_TAC
 >> DISCH_TAC
 (* applying IH *)
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 (* extra goals *)
 >> MATCH_MP_TAC subterm_induction_lemma'
 >> qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []
QED

(* NOTE: This proof is almost identical with the above lemma. Also note that
         the actual term behind ‘bot’ is different with the one above.
 *)
Theorem BT_ltree_lookup_of_unsolvables :
    !p X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              subterm X M p r <> NONE ==>
             (unsolvable (subterm' X M p r) <=>
              ltree_lookup (BT' X M r) p = SOME bot)
Proof
    Induct_on ‘p’
 >- (rpt STRIP_TAC \\
     EQ_TAC >- rw [BT_of_unsolvables, ltree_lookup_def] \\
     rpt STRIP_TAC \\
     fs [ltree_lookup, BT_def, BT_generator_def, Once ltree_unfold])
 >> rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::p’, ‘r’] subterm_solvable_lemma)
 >> rw []
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘[]’))
 >> rw [] (* solvable M *)
 >> Q.PAT_X_ASSUM ‘subterm X M (h::p) r <> NONE’ MP_TAC
 >> Q.PAT_X_ASSUM ‘!q. q <<= h::p ==> subterm X M q r <> NONE’ K_TAC
 >> UNBETA_TAC [subterm_def] “subterm X M (h::p) r”
 >> UNBETA_TAC [BT_def, Once ltree_unfold, BT_generator_def] “BT' X M r”
 >> simp [LMAP_fromList, EL_MAP, Abbr ‘l’]
 >> ‘n = n'’ by rw [Abbr ‘n’, Abbr ‘n'’]
 >> POP_ASSUM (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
 >> simp [LMAP_fromList, GSYM BT_def, ltree_lookup, LNTH_fromList, EL_MAP]
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 (* extra work *)
 >> qabbrev_tac ‘Y = RANK r’
 >> Know ‘DISJOINT (set vs) (FV M0)’
 >- (MATCH_MP_TAC subterm_disjoint_lemma' \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’] >> simp [])
 >> DISCH_TAC
 >> qunabbrev_tac ‘y’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> Cases_on ‘h < m’ >> simp []
 >> ‘Ms = args’ by rw [Abbr ‘Ms’]
 >> POP_ASSUM (fs o wrap)
 >> T_TAC
 >> DISCH_TAC
 (* applying IH *)
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 (* extra goals *)
 >> MATCH_MP_TAC subterm_induction_lemma'
 >> qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []
QED

Theorem lameq_subterm_cong_none :
    !p X M N r. FINITE X /\
                FV M SUBSET X UNION RANK r /\
                FV N SUBSET X UNION RANK r /\ M == N ==>
               (subterm X M p r = NONE <=> subterm X N p r = NONE)
Proof
    Q.X_GEN_TAC ‘p’
 >> Cases_on ‘p = []’ >- rw []
 >> POP_ASSUM MP_TAC
 >> Q.ID_SPEC_TAC ‘p’
 >> Induct_on ‘p’ >- rw []
 >> RW_TAC std_ss []
 >> reverse (Cases_on ‘solvable M’)
 >- (‘unsolvable N’ by METIS_TAC [lameq_solvable_cong] \\
     Cases_on ‘p’ >> fs [subterm_def])
 >> ‘solvable N’ by METIS_TAC [lameq_solvable_cong]
 >> RW_TAC std_ss [subterm_of_solvables]
 >> Know ‘n = n' /\ vs = vs'’
 >- (reverse CONJ_ASM1_TAC >- rw [Abbr ‘vs’, Abbr ‘vs'’] \\
     qunabbrevl_tac [‘n’, ‘n'’, ‘M0’, ‘M0'’] \\
     MATCH_MP_TAC lameq_principle_hnf_size_eq' >> art [])
 (* clean up now duplicated abbreviations: n' and vs' *)
 >> qunabbrevl_tac [‘n'’, ‘vs'’]
 >> DISCH_THEN (rfs o wrap o GSYM)
 (* applying lameq_principle_hnf_thm' *)
 >> MP_TAC (Q.SPECL [‘r’, ‘X’, ‘M’, ‘N’, ‘M0’, ‘M0'’, ‘n’, ‘vs’, ‘M1’, ‘M1'’]
                     lameq_principle_hnf_thm')
 >> simp []
 >> RW_TAC std_ss [Abbr ‘m’, Abbr ‘m'’]
 (* preparing for hnf_children_FV_SUBSET

    Here, once again, we need to get suitable explicit forms of P0 and Q0,
    to show that, P1 and Q1 are absfree hnf.
  *)
 >> qabbrev_tac ‘n = LAMl_size M0'’
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0) /\ DISJOINT (set vs) (FV M0')’
      by METIS_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> Q_TAC (HNF_TAC (“M0':term”, “vs :string list”,
                    “y' :string”, “args':term list”)) ‘M1'’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 (* refine P1 and Q1 again for clear assumptions using them *)
 >> qunabbrevl_tac [‘M1’, ‘M1'’]
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> qabbrev_tac ‘M1' = principle_hnf (M0' @* MAP VAR vs)’
 >> ‘args = Ms’ by rw [Abbr ‘Ms’]
 >> POP_ASSUM (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘args' = Ms'’ (fs o wrap o SYM)
 >> qabbrev_tac ‘m = LENGTH args'’
 >> T_TAC
 >> Cases_on ‘h < m’ >> simp []
 >> Cases_on ‘p = []’ >> fs []
 (* final stage *)
 >> FIRST_X_ASSUM MATCH_MP_TAC >> simp []
 >> CONJ_TAC (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC subterm_induction_lemma' \\
      qexistsl_tac [‘M’, ‘M0’,  ‘n’, ‘m’, ‘vs’, ‘M1’ ] >> simp [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC subterm_induction_lemma' \\
      qexistsl_tac [‘N’, ‘M0'’, ‘n’, ‘m’, ‘vs’, ‘M1'’] >> simp [] ]
QED

Theorem lameq_subterm_cong :
    !p X M N r. FINITE X /\
                FV M SUBSET X UNION RANK r /\
                FV N SUBSET X UNION RANK r /\
                M == N /\
                subterm X M p r <> NONE /\
                subterm X N p r <> NONE
            ==> subterm' X M p r == subterm' X N p r
Proof
    Q.X_GEN_TAC ‘p’
 >> Cases_on ‘p = []’ >- rw []
 >> POP_ASSUM MP_TAC
 >> Q.ID_SPEC_TAC ‘p’
 >> Induct_on ‘p’ >- rw []
 >> RW_TAC std_ss []
 >> reverse (Cases_on ‘solvable M’)
 >- (‘unsolvable N’ by METIS_TAC [lameq_solvable_cong] \\
     Cases_on ‘p’ >> fs [subterm_def])
 >> ‘solvable N’ by METIS_TAC [lameq_solvable_cong]
 >> Q.PAT_X_ASSUM ‘subterm X N (h::p) r <> NONE’ MP_TAC
 >> Q.PAT_X_ASSUM ‘subterm X M (h::p) r <> NONE’ MP_TAC
 >> RW_TAC std_ss [subterm_of_solvables]
 >> gs []
 >> Know ‘n = n' /\ vs = vs'’
 >- (reverse CONJ_ASM1_TAC >- rw [Abbr ‘vs’, Abbr ‘vs'’] \\
     qunabbrevl_tac [‘n’, ‘n'’, ‘M0’, ‘M0'’] \\
     MATCH_MP_TAC lameq_principle_hnf_size_eq' >> art [])
 (* clean up now duplicated abbreviations: n' and vs' *)
 >> qunabbrevl_tac [‘n'’, ‘vs'’]
 >> DISCH_THEN (rfs o wrap o GSYM)
 (* applying lameq_principle_hnf_thm' *)
 >> MP_TAC (Q.SPECL [‘r’, ‘X’, ‘M’, ‘N’, ‘M0’, ‘M0'’, ‘n’, ‘vs’, ‘M1’, ‘M1'’]
                     lameq_principle_hnf_thm') >> simp []
 >> RW_TAC std_ss [Abbr ‘m’, Abbr ‘m'’]
 (* preparing for hnf_children_FV_SUBSET *)
 >> qabbrev_tac ‘n = LAMl_size M0'’
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0) /\ DISJOINT (set vs) (FV M0')’
      by METIS_TAC [subterm_disjoint_lemma']
 (* NOTE: the next two HNF_TAC will refine M1 and M1' *)
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> Q_TAC (HNF_TAC (“M0':term”, “vs :string list”,
                    “y' :string”, “args':term list”)) ‘M1'’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 (* refine P1 and Q1 again for clear assumptions using them *)
 >> qunabbrevl_tac [‘M1’, ‘M1'’]
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> qabbrev_tac ‘M1' = principle_hnf (M0' @* MAP VAR vs)’
 >> ‘args = Ms’ by rw [Abbr ‘Ms’]
 >> POP_ASSUM (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘args' = Ms'’ (fs o wrap o SYM)
 >> qabbrev_tac ‘m = LENGTH args'’
 >> T_TAC
 >> Cases_on ‘p = []’ >> fs []
 (* final stage *)
 >> FIRST_X_ASSUM MATCH_MP_TAC >> simp []
 >> CONJ_TAC (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC subterm_induction_lemma' \\
      qexistsl_tac [‘M’, ‘M0’,  ‘n’, ‘m’, ‘vs’, ‘M1’ ] >> simp [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC subterm_induction_lemma' \\
      qexistsl_tac [‘N’, ‘M0'’, ‘n’, ‘m’, ‘vs’, ‘M1'’] >> simp [] ]
QED

(*****************************************************************************)
(*   ‘subterm X M p r’ w.r.t. different X and r                              *)
(*****************************************************************************)

(* NOTE: cf. subterm_fresh_tpm_cong for the easier case of fresh tpm *)
Theorem subterm_tpm_lemma :
    !X Y p M pi r r'. FINITE X /\ FINITE Y /\
         FV M SUBSET X UNION RANK r /\
         FV (tpm pi M) SUBSET Y UNION RANK r' /\
         set (MAP FST pi) SUBSET RANK r /\
         set (MAP SND pi) SUBSET RANK r' /\ r <= r'
     ==> (subterm X M p r = NONE <=>
          subterm Y (tpm pi M) p r' = NONE) /\
         (subterm X M p r <> NONE ==>
          ?pi'. tpm pi' (subterm' X M p r) = subterm' Y (tpm pi M) p r')
Proof
    qx_genl_tac [‘X’, ‘Y’]
 >> Induct_on ‘p’
 >- (rw [] >> Q.EXISTS_TAC ‘pi’ >> rw [])
 (* stage work *)
 >> rpt GEN_TAC >> STRIP_TAC
 >> reverse (Cases_on ‘solvable M’)
 >- (‘unsolvable (tpm pi M)’ by PROVE_TAC [solvable_tpm] \\
     simp [subterm_def])
 >> ‘solvable (tpm pi M)’ by PROVE_TAC [solvable_tpm]
 >> UNBETA_TAC [subterm_alt] “subterm X M (h::p) r”
 (* preparing for expanding ‘subterm' Y (tpm pi M) (h::p)’ *)
 >> qabbrev_tac ‘M0' = principle_hnf (tpm pi M)’
 >> Know ‘M0' = tpm pi M0’
 >- (qunabbrevl_tac [‘M0’, ‘M0'’] \\
     MATCH_MP_TAC principle_hnf_tpm' >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘m' = hnf_children_size M0'’
 >> ‘m' = m’ by rw [Abbr ‘m’, Abbr ‘m'’, hnf_children_size_tpm]
 >> qabbrev_tac ‘n' = LAMl_size M0'’
 >> ‘n' = n’ by rw [Abbr ‘n’, Abbr ‘n'’, LAMl_size_tpm]
 (* special case *)
 >> reverse (Cases_on ‘h < m’) >- simp [subterm_alt]
 (* stage work, now h < m *)
 >> simp [] (* eliminate ‘h < m’ in the goal *)
 >> UNBETA_TAC [subterm_alt] “subterm Y (tpm pi M) (h::p) r'”
 >> Q.PAT_X_ASSUM ‘tpm pi M0 = principle_hnf (tpm pi M)’ (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘n  = n'’  (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘n  = n''’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘m' = m''’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘m  = m'’  (fs o wrap o SYM)
 (* stage work *)
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M)’ by METIS_TAC [subterm_disjoint_lemma]
 >> qunabbrev_tac ‘vs'’
 >> Q_TAC (RNEWS_TAC (“vs' :string list”, “r' :num”, “n :num”)) ‘Y’
 (* vs1 is a permutated version of vs', to be used as first principles *)
 >> qabbrev_tac ‘vs1 = listpm string_pmact (REVERSE pi) vs'’
 >> ‘ALL_DISTINCT vs1’ by rw [Abbr ‘vs1’]
 (* rewriting inside the abbreviation of M1' *)
 >> Know ‘tpm pi M0 @* MAP VAR vs' = tpm pi (M0 @* MAP VAR vs1)’
 >- (rw [Abbr ‘vs1’, tpm_appstar] \\
     Suff ‘listpm term_pmact pi (MAP VAR (listpm string_pmact (REVERSE pi) vs')) =
           MAP VAR vs'’ >- rw [] \\
     rw [LIST_EQ_REWRITE, EL_MAP])
 >> DISCH_THEN (fs o wrap)
 (* prove that ‘M0 @* MAP VAR vs1’ correctly denude M0 *)
 >> Know ‘DISJOINT (set vs1) (FV M)’
 >- (rw [Abbr ‘vs1’, DISJOINT_ALT', MEM_listpm] \\
     Suff ‘DISJOINT (set vs') (FV (tpm pi M))’
     >- rw [DISJOINT_ALT', FV_tpm] \\
     MATCH_MP_TAC subterm_disjoint_lemma \\
     qabbrev_tac ‘n = LENGTH vs'’ \\
     qexistsl_tac [‘Y’, ‘r'’, ‘n’] >> simp [] \\
     rw [Abbr ‘M0’, principle_hnf_tpm'])
 >> DISCH_TAC
 >> ‘LENGTH vs1 = n’ by rw [Abbr ‘vs1’, LENGTH_listpm]
 (* stage work, now defining vs2 manually by primitives *)
 >> qabbrev_tac ‘Z = X UNION Y UNION set vs UNION set vs1’
 >> qabbrev_tac ‘z = SUC (string_width Z)’
 (* NOTE: vs is in rank r; vs1 seems also in the same rank *)
 >> qabbrev_tac ‘vs2 = alloc r z (z + n)’
 (* properties of vs2 *)
 >> Know ‘DISJOINT (set vs2) Z’
 >- (rw [Abbr ‘vs2’, Abbr ‘z’, DISJOINT_ALT', alloc_def, MEM_MAP] \\
     ONCE_REWRITE_TAC [TAUT ‘~P \/ Q \/ ~R <=> P /\ R ==> Q’] \\
     STRIP_TAC \\
    ‘FINITE Z’ by rw [Abbr ‘Z’] \\
     MP_TAC (Q.SPECL [‘x’, ‘Z’] string_width_thm) >> rw [])
 >> qunabbrev_tac ‘Z’
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [DISJOINT_UNION']))
 >> qabbrev_tac ‘Z = X UNION Y UNION set vs UNION set vs1’
 >> Know ‘DISJOINT (set vs2) (FV M)’
 >- (Q.PAT_X_ASSUM ‘FV M SUBSET X UNION RANK r’ MP_TAC \\
     rw [DISJOINT_ALT'] \\
     Know ‘x IN X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
     rw [IN_UNION]
     >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs2) X’ MP_TAC \\
         rw [DISJOINT_ALT']) \\
     Q.PAT_X_ASSUM ‘x IN FV M’ K_TAC \\
     Q.PAT_X_ASSUM ‘x IN RANK r’ MP_TAC \\
     Suff ‘DISJOINT (RANK r) (set vs2)’ >- rw [DISJOINT_ALT] \\
     qunabbrev_tac ‘vs2’ \\
     rw [DISJOINT_ALT, RANK, alloc_def, MEM_MAP] \\
     rw [n2s_11])
 >> DISCH_TAC
 >> ‘ALL_DISTINCT vs2 /\ LENGTH vs2 = n’ by rw [Abbr ‘vs2’, alloc_thm]
 (* stage work *)
 >> Know ‘DISJOINT (set vs2) (FV M0)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘FV M’ >> art [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘M2 = principle_hnf (M0 @* MAP VAR vs2)’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs2 :string list”,
                    “y :string”, “args :term list”)) ‘M2’
 >> ‘TAKE n vs2 = vs2’ by rw [TAKE_LENGTH_ID_rwt]
 >> POP_ASSUM (rfs o wrap)
 >> ‘hnf M2’ by rw [hnf_appstar]
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs2) (FV M0)’ K_TAC
 >> Know ‘DISJOINT (set vs)  (FV M2) /\
          DISJOINT (set vs1) (FV M2)’
 >- (CONJ_TAC (* 2 subgoals, same tactics *) \\
     (MATCH_MP_TAC DISJOINT_SUBSET \\
      Q.EXISTS_TAC ‘FV M0 UNION set vs2’ \\
      CONJ_TAC >- (Q.PAT_X_ASSUM ‘M0 = LAMl vs2 (VAR y @* args)’ K_TAC \\
                   reverse (rw [DISJOINT_UNION'])
                   >- rw [Once DISJOINT_SYM] \\
                   MATCH_MP_TAC DISJOINT_SUBSET \\
                   Q.EXISTS_TAC ‘FV M’ >> art [] \\
                   qunabbrev_tac ‘M0’ \\
                   MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) \\
     ‘FV M0 UNION set vs2 = FV (M0 @* MAP VAR vs2)’ by rw [] >> POP_ORW \\
      qunabbrev_tac ‘M2’ \\
      MATCH_MP_TAC principle_hnf_FV_SUBSET' \\
      Know ‘solvable (VAR y @* args)’
      >- (rw [solvable_iff_has_hnf] \\
          MATCH_MP_TAC hnf_has_hnf \\
          rw [hnf_appstar]) >> DISCH_TAC \\
      Suff ‘M0 @* MAP VAR vs2 == VAR y @* args’
      >- PROVE_TAC [lameq_solvable_cong] \\
      rw []))
 >> STRIP_TAC
 (* rewriting M1 and M1' (much harder) by tpm of M2 *)
 >> Know ‘M1 = tpm (ZIP (vs2,vs)) M2’
 >- (simp [Abbr ‘M1’] \\
     MATCH_MP_TAC principle_hnf_tpm_reduce' \\
     Q.PAT_X_ASSUM ‘M2 = VAR y @* args’
        (ONCE_REWRITE_TAC o wrap o SYM) >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘p1 = ZIP (vs2,vs)’
 >> Know ‘M1' = tpm pi (principle_hnf (M0 @* MAP VAR vs1))’
 >- (qunabbrev_tac ‘M1'’ \\
     MATCH_MP_TAC principle_hnf_tpm >> art [] \\
     REWRITE_TAC [has_hnf_thm] \\
     Q.EXISTS_TAC ‘fromPairs vs2 (MAP VAR vs1) ' (VAR y @* args)’ \\
     CONJ_TAC
     >- (MATCH_MP_TAC hreduce_LAMl_appstar \\
         rw [EVERY_MEM, MEM_MAP] >> rw [] \\
         Q.PAT_X_ASSUM ‘DISJOINT (set vs2) (set vs1)’ MP_TAC \\
         rw [DISJOINT_ALT']) \\
    ‘FDOM (fromPairs vs2 (MAP VAR vs1)) = set vs2’ by rw [FDOM_fromPairs] \\
     Cases_on ‘MEM y vs2’
     >- (simp [ssub_thm, ssub_appstar, hnf_appstar] \\
         fs [MEM_EL] >> rename1 ‘i < LENGTH vs2’ \\
         Know ‘fromPairs vs2 (MAP VAR vs1) ' (EL i vs2) = EL i (MAP VAR vs1)’
         >- (MATCH_MP_TAC fromPairs_FAPPLY_EL >> rw []) >> Rewr' \\
         rw [EL_MAP]) \\
     simp [ssub_thm, ssub_appstar, hnf_appstar])
 >> DISCH_TAC
 >> Know ‘M1' = tpm pi (tpm (ZIP (vs2,vs1)) M2)’
 >- (POP_ORW >> simp [] \\
     MATCH_MP_TAC principle_hnf_tpm_reduce' \\
     Q.PAT_X_ASSUM ‘M2 = VAR y @* args’
        (ONCE_REWRITE_TAC o wrap o SYM) >> art [])
 >> POP_ASSUM K_TAC (* M1' = ... (already used) *)
 >> REWRITE_TAC [GSYM pmact_decompose]
 >> qabbrev_tac ‘p2 = pi ++ ZIP (vs2,vs1)’
 >> DISCH_TAC (* M1' = tpm p2 M2 *)
 (* applying hnf_children_tpm *)
 >> Know ‘Ms = MAP (tpm p1) args’
 >- (simp [Abbr ‘Ms’] \\
    ‘hnf_children M2 = args’ by rw [hnf_children_hnf] \\
     Q.PAT_X_ASSUM ‘M2 = VAR y @* args’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     rw [hnf_children_tpm])
 >> Rewr'
 >> Know ‘Ms' = MAP (tpm p2) args’
 >- (simp [Abbr ‘Ms'’] \\
    ‘hnf_children M2 = args’ by rw [hnf_children_hnf] \\
     Q.PAT_X_ASSUM ‘M2 = VAR y @* args’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     rw [hnf_children_tpm])
 >> Rewr'
 >> ‘LENGTH args = m’ by rw [Abbr ‘m’]
 >> simp [EL_MAP]
 >> qabbrev_tac ‘N = EL h args’
 >> qabbrev_tac ‘pi' = p2 ++ REVERSE p1’
 (* final stage *)
 >> Know ‘tpm p2 N = tpm pi' (tpm p1 N)’
 >- rw [Abbr ‘pi'’, pmact_decompose]
 >> Rewr'
 >> qabbrev_tac ‘N' = tpm p1 N’ >> T_TAC
 (* finally, using IH in a bulk way *)
 >> FIRST_X_ASSUM MATCH_MP_TAC
 (* extra goal no.1 (easy) *)
 >> CONJ_TAC
 >- (simp [Abbr ‘N'’, SUBSET_DEF, FV_tpm] \\
     rpt STRIP_TAC \\
     Know ‘FV N SUBSET FV M2’
     >- (qunabbrev_tac ‘N’ \\
         irule hnf_children_FV_SUBSET >> rw []) >> DISCH_TAC \\
     qabbrev_tac ‘x' = lswapstr (REVERSE p1) x’ \\
    ‘x' IN FV M2’ by METIS_TAC [SUBSET_DEF] \\
     Know ‘FV M2 SUBSET FV (M0 @* MAP VAR vs2)’
     >- (‘solvable M2’ by rw [solvable_iff_has_hnf, hnf_has_hnf] \\
         ‘M0 @* MAP VAR vs2 == M2’ by rw [] \\
         qunabbrev_tac ‘M2’ \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' \\
         PROVE_TAC [lameq_solvable_cong]) \\
    ‘FV (M0 @* MAP VAR vs2) = FV M0 UNION set vs2’ by rw [] >> POP_ORW \\
     DISCH_TAC \\
     Know ‘FV M0 UNION set vs2 SUBSET FV M UNION set vs2’
     >- (Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) \\
     DISCH_TAC \\
    ‘x' IN FV M UNION set vs2’ by METIS_TAC [SUBSET_TRANS, SUBSET_DEF] \\
    ‘x = lswapstr p1 x'’ by rw [Abbr ‘x'’] >> POP_ORW \\
     Suff ‘lswapstr p1 x' IN FV M UNION set vs’
     >- (Suff ‘FV M UNION set vs SUBSET X UNION RANK (SUC r)’
         >- SET_TAC [] \\
         simp [UNION_SUBSET] \\
         CONJ_TAC >- (MATCH_MP_TAC SUBSET_TRANS \\
                      Q.EXISTS_TAC ‘X UNION RANK r’ >> art [] \\
                      Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
                      MATCH_MP_TAC RANK_MONO >> rw []) \\
         MATCH_MP_TAC SUBSET_TRANS \\
         Q.EXISTS_TAC ‘RANK (SUC r)’ >> simp [] \\
         qunabbrev_tac ‘vs’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw []) \\
     MP_TAC (Q.SPECL [‘REVERSE p1’, ‘x'’, ‘FV M UNION set vs’]
                     (GSYM ssetpm_IN)) \\
     SIMP_TAC list_ss [pmact_UNION] \\
     Suff ‘x' IN ssetpm (REVERSE p1) (FV M) \/
           x' IN ssetpm (REVERSE p1) (set vs)’ >- simp [] \\
     Know ‘ssetpm (REVERSE p1) (FV M) = FV M’
     >- (irule ssetpm_unchanged \\
         simp [Abbr ‘p1’, REVERSE_ZIP, MAP_ZIP]) >> Rewr' \\
     Q.PAT_X_ASSUM ‘x' IN FV M UNION set vs2’ MP_TAC \\
     rw [IN_UNION] >- (DISJ1_TAC >> art []) \\
     DISJ2_TAC \\
     qunabbrev_tac ‘p1’ \\
     MATCH_MP_TAC MEM_lswapstr >> rw [])
  (* extra goal no.2 (hard) *)
 >> CONJ_TAC
 >- (simp [Abbr ‘N'’, FV_tpm, SUBSET_DEF] \\
     simp [GSYM lswapstr_append, GSYM REVERSE_APPEND] \\
     Q.X_GEN_TAC ‘x’ \\
     qabbrev_tac ‘x' = lswapstr (REVERSE (pi' ++ p1)) x’ \\
     qabbrev_tac ‘p3 = pi' ++ p1’ \\
    ‘x = lswapstr p3 x'’ by rw [Abbr ‘x'’] >> POP_ORW \\
     Know ‘FV N SUBSET FV M2’
     >- (qunabbrev_tac ‘N’ \\
         irule hnf_children_FV_SUBSET >> rw []) >> DISCH_TAC \\
     DISCH_TAC (* x' IN FV N *) \\
    ‘x' IN FV M2’ by METIS_TAC [SUBSET_DEF] \\
     Know ‘FV M2 SUBSET FV (M0 @* MAP VAR vs2)’
     >- (‘solvable M2’ by rw [solvable_iff_has_hnf, hnf_has_hnf] \\
         ‘M0 @* MAP VAR vs2 == M2’ by rw [] \\
         qunabbrev_tac ‘M2’ \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' \\
         PROVE_TAC [lameq_solvable_cong]) \\
    ‘FV (M0 @* MAP VAR vs2) = FV M0 UNION set vs2’ by rw [] >> POP_ORW \\
     DISCH_TAC \\
     Know ‘FV M0 UNION set vs2 SUBSET FV M UNION set vs2’
     >- (Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) \\
     DISCH_TAC \\
     Q.PAT_X_ASSUM ‘FV (tpm pi M) SUBSET Y UNION RANK r'’ MP_TAC \\
     simp [FV_tpm, SUBSET_DEF] \\
     DISCH_TAC \\
  (* NOTE: current relations of permutations:

     p1 = ZIP (vs2,vs)
     p2 = pi ++ ZIP (vs2,vs1)
     pi' = p2 ++ REVERSE p1
     p3 = pi' ++ p1 = p2 ++ REVERSE p1 ++ p1 == p2
     p4 = REVERSE pi ++ p3
     p4 = REVERSE pi ++ pi ++ ZIP (vs2,vs1) == ZIP (vs2,vs1)
   *)
    ‘p3 == p2’ by rw [Abbr ‘p3’, Abbr ‘pi'’, permof_inverse_append] \\
     qabbrev_tac ‘p4 = REVERSE pi ++ p3’ \\
     Know ‘p4 == ZIP (vs2,vs1)’
     >- (qunabbrev_tac ‘p4’ \\
         MATCH_MP_TAC (GEN_ALL permeq_trans) \\
         Q.EXISTS_TAC ‘REVERSE pi ++ p2’ \\
         CONJ_TAC
         >- (MATCH_MP_TAC app_permeq_monotone >> rw []) \\
         rw [Abbr ‘p2’, APPEND_ASSOC] \\
         MATCH_MP_TAC (GEN_ALL permeq_trans) \\
         Q.EXISTS_TAC ‘[] ++ ZIP (vs2,vs1)’ \\
         CONJ_TAC
         >- (MATCH_MP_TAC app_permeq_monotone >> rw [permof_inverse]) \\
         rw []) >> DISCH_TAC \\
    ‘x' IN FV M UNION set vs2’ by METIS_TAC [SUBSET_TRANS, SUBSET_DEF] \\
     Q.PAT_X_ASSUM ‘FV N SUBSET FV M2’ K_TAC \\
     Q.PAT_X_ASSUM ‘x' IN FV N’ K_TAC \\
     Q.PAT_X_ASSUM ‘x' IN FV M2’ K_TAC \\
     qunabbrev_tac ‘N’ \\
  (* stage work *)
     POP_ASSUM MP_TAC >> REWRITE_TAC [IN_UNION] \\
     STRIP_TAC (* x' IN FV M *)
     >- (Q.PAT_X_ASSUM ‘!x. lswapstr (REVERSE pi) x IN FV M ==> P’
           (MP_TAC o Q.SPEC ‘lswapstr p3 x'’) \\
         simp [GSYM pmact_append, IN_UNION] \\
         Suff ‘lswapstr p4 x' IN FV M’
         >- (rw [] >- art [] \\
             DISJ2_TAC \\
             Know ‘RANK r' SUBSET RANK (SUC r')’ >- rw [RANK_MONO] \\
             rw [SUBSET_DEF]) \\
         Know ‘lswapstr p4 x' = lswapstr (ZIP (vs2,vs1)) x'’
         >- (Q.PAT_X_ASSUM ‘p4 == ZIP (vs2,vs1)’ MP_TAC \\
             rw [permeq_thm]) >> Rewr' \\
         MP_TAC (Q.SPECL [‘REVERSE (ZIP (vs2,vs1))’, ‘x'’, ‘FV M’]
                         (GSYM ssetpm_IN)) \\
         SIMP_TAC list_ss [] >> DISCH_THEN K_TAC \\
         qabbrev_tac ‘p5 = REVERSE (ZIP (vs2,vs1))’ \\
         Suff ‘ssetpm p5 (FV M) = FV M’ >- (Rewr' >> art []) \\
         MATCH_MP_TAC ssetpm_unchanged \\
         simp [Abbr ‘p5’, MAP_REVERSE, MAP_ZIP]) \\
  (* remaining goal: MEM x' vs2 *)
     DISJ2_TAC \\
     Know ‘lswapstr p3 x' = lswapstr p2 x'’
     >- (Q.PAT_X_ASSUM ‘p3 == p2’ MP_TAC \\
         rw [permeq_thm]) >> Rewr' \\
     Q.PAT_X_ASSUM ‘!x. lswapstr (REVERSE pi) x IN FV M ==> P’ K_TAC \\
     simp [Abbr ‘p2’, pmact_append] \\
     POP_ASSUM MP_TAC (* MEM x' vs2 *) \\
     simp [MEM_EL] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘i’ STRIP_ASSUME_TAC) \\
     POP_ORW (* ‘EL i vs2’ in the goal *) \\
     Know ‘lswapstr (ZIP (vs2,vs1)) (EL i vs2) = EL i vs1’
     >- (MATCH_MP_TAC lswapstr_apply_EL >> rw []) >> Rewr' \\
     simp [Abbr ‘vs1’] \\
     qabbrev_tac ‘vs1 = listpm string_pmact (REVERSE pi) vs'’ \\
     MP_TAC (Q.SPECL [‘r'’, ‘SUC r'’, ‘n’, ‘Y’] RNEWS_SUBSET_RANK) \\
     rw [SUBSET_DEF] \\
     POP_ASSUM MATCH_MP_TAC >> rw [EL_MEM])
 (* final goals *)
 >> simp [Abbr ‘pi'’, MAP_APPEND, MAP_REVERSE, Abbr ‘p2’, Abbr ‘p1’, MAP_ZIP]
 >> Know ‘set (MAP FST pi) SUBSET RANK (SUC r)’
 >- (MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘RANK r’ >> rw [RANK_MONO])
 >> Rewr
 >> Know ‘set (MAP SND pi) SUBSET RANK (SUC r')’
 >- (MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘RANK r'’ >> rw [RANK_MONO])
 >> Rewr
 >> Know ‘set vs2 SUBSET RANK (SUC r)’
 >- (qunabbrev_tac ‘vs2’ \\
     MATCH_MP_TAC alloc_SUBSET_RANK >> rw [])
 >> Rewr
 (* NOTE: This proof requires that ‘r <= r'’ !!! *)
 >> Know ‘set vs SUBSET RANK (SUC r')’
 >- (MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘RANK (SUC r)’ \\
     reverse CONJ_TAC >- (MATCH_MP_TAC RANK_MONO >> rw []) \\
     qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw [])
 >> Rewr
 (* final goal: set vs1 SUBSET RANK r' *)
 >> simp [SUBSET_DEF, Abbr ‘vs1’, MEM_listpm, MEM_EL]
 >> rpt STRIP_TAC
 >> rename1 ‘i < n’
 >> qabbrev_tac ‘x' = EL i vs'’
 >> ‘x = lswapstr (REVERSE pi) x'’ by rw []
 >> POP_ORW
 >> Q.PAT_X_ASSUM ‘lswapstr pi x = x'’ K_TAC
 >> Know ‘x' IN ROW r'’
 >- (MP_TAC (Q.SPECL [‘r'’, ‘n’, ‘Y’] RNEWS_SUBSET_ROW) \\
     simp [SUBSET_DEF] >> DISCH_THEN MATCH_MP_TAC \\
     rw [Abbr ‘x'’, EL_MEM])
 >> DISCH_TAC
 (* NOTE: x' is in rank r', while pi is either < r <= r' or < r', thus
    either key or value of pi is in rank < r'. Thus it works.
  *)
 >> Suff ‘lswapstr (REVERSE pi) x' = x'’
 >- (Rewr' \\
     MP_TAC (Q.SPECL [‘r'’, ‘SUC r'’, ‘n’, ‘Y’] RNEWS_SUBSET_RANK) \\
     simp [SUBSET_DEF] \\
     DISCH_THEN MATCH_MP_TAC \\
     rw [Abbr ‘x'’, EL_MEM])
 (* applying lswapstr_unchanged' *)
 >> MATCH_MP_TAC lswapstr_unchanged'
 >> simp [MAP_REVERSE]
 >> CONJ_TAC (* 2 subgoals *)
 >| [ (* goal 1 (of 2): ~MEM x' (MAP FST pi) *)
      MP_TAC (Q.SPECL [‘r’, ‘r'’, ‘n’] RANK_ROW_DISJOINT) \\
      simp [DISJOINT_ALT] >> DISCH_TAC \\
      CCONTR_TAC >> METIS_TAC [SUBSET_DEF],
      (* goal 2 (of 2): ~MEM x' (MAP SND pi) *)
      MP_TAC (Q.SPECL [‘r'’, ‘r'’, ‘n’] RANK_ROW_DISJOINT) \\
      simp [DISJOINT_ALT] >> DISCH_TAC \\
      CCONTR_TAC >> METIS_TAC [SUBSET_DEF] ]
QED

Theorem FV_tpm_lemma :
    !X M pi r r'. FINITE X /\ FV M SUBSET X UNION RANK r /\
                  set (MAP FST pi) SUBSET X UNION RANK r /\
                  set (MAP SND pi) SUBSET X UNION RANK r' /\
                  r <= r'
              ==> FV (tpm pi M) SUBSET X UNION RANK r'
Proof
    rpt STRIP_TAC
 >> rw [FV_tpm, SUBSET_DEF]
 >> qabbrev_tac ‘v = lswapstr (REVERSE pi) x’
 >> ‘x = lswapstr pi v’ by rw [Abbr ‘v’]
 >> POP_ORW
 >> Q.PAT_X_ASSUM ‘set (MAP SND pi) SUBSET _’ MP_TAC
 >> Q.PAT_X_ASSUM ‘set (MAP FST pi) SUBSET _’ MP_TAC
 >> Know ‘v IN X UNION RANK r’ >- METIS_TAC [SUBSET_DEF]
 >> Q.PAT_X_ASSUM ‘r <= r'’ MP_TAC
 >> KILL_TAC
 >> Q.ID_SPEC_TAC ‘v’
 >> Induct_on ‘pi’
 >- (rw [] \\
     Suff ‘RANK r SUBSET RANK r'’ >- ASM_SET_TAC [] \\
     rw [RANK_MONO])
 >> simp [FORALL_PROD]
 >> qx_genl_tac [‘x’, ‘y’]
 >> rw [MAP]
 >> Q.PAT_X_ASSUM ‘!v. P’ (MP_TAC o Q.SPEC ‘v’)
 >> rw []
 >> qabbrev_tac ‘z = lswapstr pi v’
 >> rw [swapstr_def]
 >> Suff ‘RANK r SUBSET RANK r'’ >- ASM_SET_TAC []
 >> rw [RANK_MONO]
QED

Theorem FV_tpm_lemma' :
    !X M pi r r'. FINITE X /\ FV M SUBSET X UNION RANK r /\
                  set (MAP FST pi) SUBSET RANK r /\
                  set (MAP SND pi) SUBSET RANK r' /\
                  r <= r'
              ==> FV (tpm pi M) SUBSET X UNION RANK r'
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC FV_tpm_lemma
 >> Q.EXISTS_TAC ‘r’ >> art []
 >> ASM_SET_TAC []
QED

(* NOTE: M may contain free variables from xs, but after the fresh tpm
   there's no more xs variables, thus is disjoint with xs.
 *)
Theorem FV_renaming_disjoint :
    !xs ys M. ALL_DISTINCT xs /\ ALL_DISTINCT ys /\
              LENGTH xs = LENGTH ys /\
              DISJOINT (set xs) (set ys) /\
              DISJOINT (set ys) (FV M)
          ==> DISJOINT (FV (M ISUB ZIP (MAP VAR ys,xs))) (set xs)
Proof
    rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘ALL_DISTINCT xs’ MP_TAC
 >> Q.PAT_X_ASSUM ‘ALL_DISTINCT ys’ MP_TAC
 >> Q.PAT_X_ASSUM ‘DISJOINT (set xs) (set ys)’ MP_TAC
 >> Q.PAT_X_ASSUM ‘DISJOINT (set ys) (FV M)’ MP_TAC
 >> qabbrev_tac ‘pi = ZIP (xs,ys)’
 >> ‘xs = MAP FST pi /\ ys = MAP SND pi’ by rw [Abbr ‘pi’, MAP_ZIP]
 >> NTAC 2 POP_ORW
 >> KILL_TAC
 >> Q.ID_SPEC_TAC ‘M’
 >> Induct_on ‘pi’ >- rw []
 >> simp [FORALL_PROD]
 >> qx_genl_tac [‘x’, ‘y’, ‘M’]
 >> qabbrev_tac ‘xs = MAP FST pi’
 >> qabbrev_tac ‘ys = MAP SND pi’
 >> NTAC 4 STRIP_TAC
 >> CONJ_TAC
 >- (FIRST_X_ASSUM irule >> art [] \\
     simp [FV_SUB] \\
     Cases_on ‘x IN FV M’ >> simp [] \\
     MATCH_MP_TAC DISJOINT_SUBSET' \\
     Q.EXISTS_TAC ‘FV M’ >> simp [Once DISJOINT_SYM])
 (* stage work *)
 >> qabbrev_tac ‘sub = ZIP (MAP VAR ys,xs)’
 >> fs []
 >> qabbrev_tac ‘t = [VAR y/x] M’
 >> Know ‘FV (t ISUB sub) SUBSET FV t UNION FVS sub’
 >- rw [FV_ISUB_upperbound]
 >> ‘LENGTH ys = LENGTH xs’ by rw [Abbr ‘xs’, Abbr ‘ys’]
 >> Know ‘FVS sub = set ys’
 >- (rw [Abbr ‘sub’, FVS_ALT, Once EXTENSION] \\
     EQ_TAC >> rw []
     >- (rename1 ‘MEM z ys’ \\
         gvs [MEM_MAP] \\
         POP_ASSUM MP_TAC \\
         rw [MEM_ZIP, LENGTH_MAP] \\
         gvs [EL_MAP] \\
         simp [EL_MEM]) \\
     simp [MEM_MAP] \\
     rename1 ‘MEM z ys’ \\
     Q.EXISTS_TAC ‘FV (VAR z)’ >> simp [] \\
     fs [MEM_EL] \\
     Q.EXISTS_TAC ‘(VAR (EL n ys),EL n xs)’ >> simp [] \\
     Q.EXISTS_TAC ‘n’ >> simp [EL_ZIP, EL_MAP])
 >> Rewr'
 >> simp [Abbr ‘t’, FV_SUB]
 >> Cases_on ‘x IN FV M’ >> simp []
 >- (DISCH_TAC \\
     CCONTR_TAC >> fs [] \\
     Know ‘x IN {y} UNION (FV M DELETE x) UNION set ys’
     >- METIS_TAC [SUBSET_DEF] \\
     simp [IN_UNION])
 >> qabbrev_tac ‘t = [VAR y/x] M’
 >> DISCH_TAC
 >> CCONTR_TAC >> fs []
 >> Know ‘x IN FV M UNION set ys’ >- METIS_TAC [SUBSET_DEF]
 >> simp [IN_UNION]
QED

(* NOTE: M is disjoint with zs, and the tpm (not a fresh tpm) is irrelevant
   with zs, thus after the tpm the resulting term is still disjoint with zs.
 *)
Theorem FV_tpm_disjoint :
    !zs xs ys M. ALL_DISTINCT xs /\ ALL_DISTINCT ys /\
                 LENGTH xs = LENGTH ys /\
                 DISJOINT (set xs) (set ys) /\
                 DISJOINT (set xs) (set zs) /\
                 DISJOINT (set ys) (set zs) /\
                 DISJOINT (set zs) (FV M)
             ==> DISJOINT (set zs) (FV (tpm (ZIP (xs,ys)) M))
Proof
    rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘ALL_DISTINCT xs’ MP_TAC
 >> Q.PAT_X_ASSUM ‘ALL_DISTINCT ys’ MP_TAC
 >> Q.PAT_X_ASSUM ‘DISJOINT (set xs) (set ys)’ MP_TAC
 >> Q.PAT_X_ASSUM ‘DISJOINT (set ys) (set zs)’ MP_TAC
 >> Q.PAT_X_ASSUM ‘DISJOINT (set xs) (set zs)’ MP_TAC
 >> Q.PAT_X_ASSUM ‘DISJOINT (set zs) (FV M)’   MP_TAC
 >> qabbrev_tac ‘pi = ZIP (xs,ys)’
 >> ‘xs = MAP FST pi /\ ys = MAP SND pi’ by rw [Abbr ‘pi’, MAP_ZIP]
 >> NTAC 2 POP_ORW
 >> KILL_TAC
 >> Q.ID_SPEC_TAC ‘M’
 >> Induct_on ‘pi’ >- rw []
 >> simp [FORALL_PROD]
 >> qx_genl_tac [‘x’, ‘y’, ‘M’]
 >> qabbrev_tac ‘xs = MAP FST pi’
 >> qabbrev_tac ‘ys = MAP SND pi’
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!M. P’ (MP_TAC o Q.SPEC ‘M’) >> rw []
 >> simp [Once tpm_CONS]
 >> qabbrev_tac ‘t = tpm pi M’
 >> rw [DISJOINT_ALT', FV_tpm]
 >> rename1 ‘swapstr x y z IN FV t’
 >> Cases_on ‘x = z’ >> fs [swapstr_def]
 >> Cases_on ‘y = z’ >> fs []
 >> Q.PAT_X_ASSUM ‘DISJOINT (set zs) (FV t)’ MP_TAC
 >> rw [DISJOINT_ALT']
QED

(* In this special version, X = Y *)
Theorem subterm_tpm_lemma' :
    !X p M pi r r'.
         FINITE X /\ FV M SUBSET X UNION RANK r /\
         set (MAP FST pi) SUBSET RANK r /\
         set (MAP SND pi) SUBSET RANK r' /\ r <= r' ==>
        (subterm X M p r = NONE <=> subterm X (tpm pi M) p r' = NONE) /\
        (subterm X M p r <> NONE ==>
         ?pi'. tpm pi' (subterm' X M p r) = subterm' X (tpm pi M) p r')
Proof
    rpt GEN_TAC
 >> STRIP_TAC
 >> MATCH_MP_TAC subterm_tpm_lemma >> art []
 >> MATCH_MP_TAC FV_tpm_lemma'
 >> Q.EXISTS_TAC ‘r’ >> art []
QED

Theorem subterm_tpm_cong_lemma[local] :
    !X Y p M r r'. FINITE X /\ FINITE Y /\
         FV M SUBSET X UNION RANK r /\
         FV M SUBSET Y UNION RANK r' /\ r <= r'
     ==> (subterm X M p r = NONE <=> subterm Y M p r' = NONE) /\
         (subterm X M p r <> NONE ==>
          tpm_rel (subterm' X M p r) (subterm' Y M p r'))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘Y’, ‘p’, ‘M’, ‘[]’, ‘r’, ‘r'’] subterm_tpm_lemma)
 >> simp [tpm_rel_def]
QED

(* NOTE: ‘r <= r'’ is removed now. This is the final strong version. *)
Theorem subterm_tpm_cong :
    !X Y M p r r'. FINITE X /\ FINITE Y /\
         FV M SUBSET X UNION RANK r /\
         FV M SUBSET Y UNION RANK r'
     ==> (subterm X M p r = NONE <=> subterm Y M p r' = NONE) /\
         (subterm X M p r <> NONE ==>
          tpm_rel (subterm' X M p r) (subterm' Y M p r'))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘r <= r' \/ r' <= r’ by rw []
 >- METIS_TAC [subterm_tpm_cong_lemma]
 >> REWRITE_TAC [tpm_rel_alt]
 >> MP_TAC (Q.SPECL [‘Y’, ‘X’, ‘p’, ‘M’, ‘r'’, ‘r’] subterm_tpm_cong_lemma)
 >> simp [tpm_rel_def]
 >> METIS_TAC []
QED

Theorem subterm_solvable_cong :
    !X Y M p r r'. FINITE X /\ FINITE Y /\
         FV M SUBSET X UNION RANK r /\
         FV M SUBSET Y UNION RANK r' /\
         subterm X M p r <> NONE ==>
        (solvable (subterm' X M p r) <=> solvable (subterm' Y M p r'))
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘Y’, ‘M’, ‘p’, ‘r’, ‘r'’] subterm_tpm_cong)
 >> rw []
 >> fs [tpm_rel_alt, solvable_tpm]
QED

(* In this way, two such terms have the same ‘hnf_children_size o principle_hnf’,
   because head reductions are congruence w.r.t. tpm.
 *)
Theorem subterm_hnf_children_size_cong :
    !X Y M p r r'. FINITE X /\ FINITE Y /\
         FV M SUBSET X UNION RANK r /\
         FV M SUBSET Y UNION RANK r' /\
         subterm X M p r <> NONE /\ solvable (subterm' X M p r) ==>
         hnf_children_size (principle_hnf (subterm' X M p r)) =
         hnf_children_size (principle_hnf (subterm' Y M p r'))
Proof
    rpt STRIP_TAC
 >> ‘subterm Y M p r' <> NONE /\
     tpm_rel (subterm' X M p r) (subterm' Y M p r')’
       by METIS_TAC [subterm_tpm_cong]
 >> fs [tpm_rel_def]
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
 >> qabbrev_tac ‘N = subterm' X M p r’
 >> rw [principle_hnf_tpm']
QED

Theorem BT_tpm_lemma[local] :
    !X M pi r. FINITE X /\ FV M SUBSET X UNION RANK r /\
               set (MAP FST pi) SUBSET RANK r /\
               set (MAP SND pi) SUBSET RANK r
           ==> ltree_node (BT' X (tpm pi M) r) =
               ltree_node
                 (ltree_map (OPTION_MAP (λ(vs,y). (vs,lswapstr pi y))) (BT' X M r))
Proof
    rpt STRIP_TAC
 >> qmatch_abbrev_tac ‘ltree_node (BT' X (tpm pi M) r) =
                       ltree_node (ltree_map f (BT' X M r))’
 >> reverse (Cases_on ‘solvable M’)
 >- (‘unsolvable (tpm pi M)’ by rw [solvable_tpm] \\
     rw [BT_of_unsolvables, ltree_map, Abbr ‘f’])
 >> ‘solvable (tpm pi M)’ by rw [solvable_tpm]
 >> rw [BT_def, Once ltree_unfold, BT_generator_def]
 >> rw [BT_def, Once ltree_unfold, BT_generator_def, LMAP_fromList, ltree_map]
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> simp [principle_hnf_tpm']
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> Know ‘tpm pi M0 @* MAP VAR vs = tpm pi (M0 @* MAP VAR vs)’
 >- (simp [tpm_appstar] >> AP_TERM_TAC \\
     simp [Once LIST_EQ_REWRITE, EL_MAP] \\
     rpt STRIP_TAC \\
     MATCH_MP_TAC (GSYM lswapstr_unchanged') \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Know ‘DISJOINT (set (MAP FST pi)) (set (RNEWS r n X))’
       >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
           Q.EXISTS_TAC ‘RANK r’ >> art [] \\
           MATCH_MP_TAC DISJOINT_RANK_RNEWS' >> art []) \\
       rw [DISJOINT_ALT'] \\
       POP_ASSUM MATCH_MP_TAC >> rw [EL_MEM],
       (* goal 2 (of 2) *)
       Know ‘DISJOINT (set (MAP SND pi)) (set (RNEWS r n X))’
       >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
           Q.EXISTS_TAC ‘RANK r’ >> art [] \\
           MATCH_MP_TAC DISJOINT_RANK_RNEWS' >> art []) \\
       rw [DISJOINT_ALT'] \\
       POP_ASSUM MATCH_MP_TAC >> rw [EL_MEM] ])
 >> Rewr'
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw [] >> POP_ASSUM (rfs o wrap)
 >> Know ‘principle_hnf (tpm pi (LAMl vs (VAR y @* args) @* MAP VAR vs)) =
          tpm pi (principle_hnf (LAMl vs (VAR y @* args) @* MAP VAR vs))’
 >- (MATCH_MP_TAC principle_hnf_tpm' \\
    ‘LAMl vs (VAR y @* args) @* MAP VAR vs == VAR y @* args’
       by PROVE_TAC [lameq_LAMl_appstar_VAR] \\
     Suff ‘solvable (VAR y @* args)’ >- PROVE_TAC [lameq_solvable_cong] \\
     REWRITE_TAC [solvable_iff_has_hnf] \\
     MATCH_MP_TAC hnf_has_hnf >> simp [hnf_appstar])
 >> Rewr'
 >> simp [principle_hnf_beta_reduce, hnf_appstar, tpm_appstar]
 >> rw [Abbr ‘f’]
QED

Theorem BT_tpm_thm :
    !X M pi r. FINITE X /\ FV M SUBSET X UNION RANK r /\
               set (MAP FST pi) SUBSET RANK r /\
               set (MAP SND pi) SUBSET RANK r
           ==> BT' X (tpm pi M) r =
               ltree_map (OPTION_MAP (λ(vs,y). (vs,lswapstr pi y))) (BT' X M r)
Proof
    rpt STRIP_TAC
 >> qmatch_abbrev_tac ‘BT' X (tpm pi M) r = ltree_map f (BT' X M r)’
 >> rw [ltree_bisimulation]
 >> Q.EXISTS_TAC ‘\t1 t2. ?N q. FV N SUBSET X UNION RANK q /\ r <= q /\
                                t1 = BT' X (tpm pi N) q /\
                                t2 = ltree_map f (BT' X N q) /\
                                ltree_node t1 = ltree_node t2’
 >> rw []
 >- (qexistsl_tac [‘M’, ‘r’] >> rw [Abbr ‘f’] \\
     MATCH_MP_TAC BT_tpm_lemma >> art [])
 (* stage work *)
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> reverse (Cases_on ‘solvable N’)
 >- (‘unsolvable (tpm pi N)’ by rw [solvable_tpm] \\
     simp [BT_of_unsolvables, Abbr ‘f’] >> Rewr' \\
     rw [llist_rel_def, ltree_map])
 >> ‘solvable (tpm pi N)’ by rw [solvable_tpm]
 >> Q_TAC (UNBETA_TAC [BT_def, Once ltree_unfold, BT_generator_def]) ‘BT' X N q’
 >> Q_TAC (UNBETA_TAC [BT_def, Once ltree_unfold, BT_generator_def])
          ‘BT' X (tpm pi N) q’
 >> gs [Abbr ‘M0'’, principle_hnf_tpm']
 >> Rewr' (* this eliminates ‘a’ and ‘ts’, both used already *)
 >> Q.PAT_X_ASSUM ‘n = n'’ (fs o wrap o SYM)
 >> fs [Abbr ‘vs'’]
 >> Q.PAT_X_ASSUM ‘RNEWS q n X = vs’ (rfs o wrap o SYM)
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “q :num”, “n :num”)) ‘X’
 >> Know ‘tpm pi M0 @* MAP VAR vs = tpm pi (M0 @* MAP VAR vs)’
 >- (simp [tpm_appstar] >> AP_TERM_TAC \\
     simp [Once LIST_EQ_REWRITE, EL_MAP] \\
     rpt STRIP_TAC \\
     MATCH_MP_TAC (GSYM lswapstr_unchanged') \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Know ‘DISJOINT (set (MAP FST pi)) (set (RNEWS q n X))’
       >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
           Q.EXISTS_TAC ‘RANK q’ \\
           reverse CONJ_TAC
           >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘RANK r’ >> rw [RANK_MONO]) \\
           MATCH_MP_TAC DISJOINT_RANK_RNEWS' >> art []) \\
       rw [DISJOINT_ALT'] \\
       POP_ASSUM MATCH_MP_TAC >> rw [EL_MEM],
       (* goal 2 (of 2) *)
       Know ‘DISJOINT (set (MAP SND pi)) (set (RNEWS q n X))’
       >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
           Q.EXISTS_TAC ‘RANK q’ \\
           reverse CONJ_TAC
           >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘RANK r’ >> rw [RANK_MONO]) \\
           MATCH_MP_TAC DISJOINT_RANK_RNEWS' >> art []) \\
       rw [DISJOINT_ALT'] \\
       POP_ASSUM MATCH_MP_TAC >> rw [EL_MEM] ])
 >> DISCH_THEN (fs o wrap)
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> qunabbrevl_tac [‘y’, ‘y'’]
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw [] >> POP_ASSUM (rfs o wrap)
 >> simp [Abbr ‘M1'’, Abbr ‘Ms’, Abbr ‘Ms'’, Abbr ‘l’, Abbr ‘l'’]
 >> Know ‘principle_hnf (tpm pi (LAMl vs (VAR y @* args) @* MAP VAR vs)) =
          tpm pi (principle_hnf (LAMl vs (VAR y @* args) @* MAP VAR vs))’
 >- (MATCH_MP_TAC principle_hnf_tpm' \\
    ‘LAMl vs (VAR y @* args) @* MAP VAR vs == VAR y @* args’
       by PROVE_TAC [lameq_LAMl_appstar_VAR] \\
     Suff ‘solvable (VAR y @* args)’ >- PROVE_TAC [lameq_solvable_cong] \\
     REWRITE_TAC [solvable_iff_has_hnf] \\
     MATCH_MP_TAC hnf_has_hnf \\
     simp [hnf_appstar])
 >> Rewr'
 >> simp [principle_hnf_beta_reduce, hnf_appstar, tpm_appstar]
 >> simp [ltree_map, Abbr ‘f’, LMAP_fromList]
 >> Rewr' (* this eliminates ‘ts'’, already used *)
 (* stage work *)
 >> simp [llist_rel_def, LLENGTH_fromList, LNTH_fromList, EL_MAP]
 >> rpt STRIP_TAC
 >> qexistsl_tac [‘EL i args’, ‘SUC q’]
 >> simp [GSYM BT_def]
 >> CONJ_ASM1_TAC
 >- (MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘N’, ‘M0’, ‘n’, ‘LENGTH args’, ‘vs’, ‘M1’] >> rw [])
 >> MATCH_MP_TAC BT_tpm_lemma >> art []
 >> CONJ_TAC (* 2 subgoals, same tactics *)
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘RANK r’
 >> rw [RANK_MONO]
QED

(* tpm doesn't change ltree_paths

   NOTE: ‘FV (tpm pi M) SUBSET X UNION RANK r’ is derivable from other antecedents.
 *)
Theorem BT_ltree_paths_tpm :
    !X M pi r. FINITE X /\ FV M SUBSET X UNION RANK r /\
               set (MAP FST pi) SUBSET RANK r /\
               set (MAP SND pi) SUBSET RANK r
           ==> ltree_paths (BT' X M r) = ltree_paths (BT' X (tpm pi M) r)
Proof
    RW_TAC std_ss [BT_tpm_thm, ltree_paths_map_cong]
QED

(*---------------------------------------------------------------------------*
 *  Equivalent terms
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

(*---------------------------------------------------------------------------*
 *  Boehm transformations
 *---------------------------------------------------------------------------*)

(* Definition 10.3.3 (i) [1, p.246] *)
Type transform[pp] = “:(term -> term) list”

(* Definition 10.3.3 (ii) *)
Definition solving_transform_def :
    solving_transform (f :term -> term) <=>
      (?x. f = \p. p @@ VAR x) \/ (?x N. f = [N/x])
End

Theorem solving_transform_subst[simp] :
    solving_transform [N/x]
Proof
    rw [solving_transform_def]
 >> DISJ2_TAC >> qexistsl_tac [‘x’, ‘N’] >> rw []
QED

Theorem solving_transform_rightctxt[simp] :
    solving_transform (rightctxt (VAR x))
Proof
    rw [solving_transform_def, FUN_EQ_THM]
 >> DISJ1_TAC
 >> Q.EXISTS_TAC ‘x’ >> rw [rightctxt_thm]
QED

Theorem solving_transform_lameq :
    !f M N. solving_transform f /\ M == N ==> f M == f N
Proof
    rw [solving_transform_def, FUN_EQ_THM]
 >- rw [lameq_rules]
 >> rw [lameq_sub_cong]
QED

(* Definition 10.3.3 (iii)

   NOTE: "Boehm transform is a finite composition of solving transforms
        (including the identity as a composition of zero transforms).

   Here we just define "Boehm transform" as a list of solving transforms,
   thus always finite. The "composition" part depends on how this list is used.
 *)
Definition Boehm_transform_def :
    Boehm_transform pi = EVERY solving_transform pi
End

Theorem Boehm_transform_empty[simp] :
    Boehm_transform []
Proof
    rw [Boehm_transform_def]
QED

Theorem Boehm_transform_CONS[simp] :
    Boehm_transform (h::pi) <=> solving_transform h /\ Boehm_transform pi
Proof
    rw [Boehm_transform_def]
QED

Theorem Boehm_transform_SNOC[simp] :
    Boehm_transform (SNOC h pi) <=> Boehm_transform pi /\ solving_transform h
Proof
    rw [Boehm_transform_def, EVERY_SNOC]
QED

Theorem Boehm_transform_MAP_rightctxt_o_VAR[simp] :
    Boehm_transform (MAP (rightctxt o VAR) vs)
Proof
    rw [Boehm_transform_def, EVERY_MAP]
QED

(* ‘apply pi M’ (applying a Boehm transformation) means "M^{pi}" or "pi(M)"

   NOTE: ‘apply [f3;f2;f1] M = (f3 o f2 o f1) M = f3 (f2 (f1 M))’

   NOTE2: This function seems general: “:('a -> 'a) list -> 'a -> 'a”.
 *)
Definition apply_transform_def :
    apply_transform (pi :transform) = FOLDR $o I pi
End

Overload apply = “apply_transform”

(* NOTE: either FOLDL or FOLDR is correct (due to combinTheory.o_ASSOC),
         but FOLDR seems more natural requiring natural list induction in
         the next proof(s), while FOLDL would require SNOC_INDUCT.
 *)
Theorem apply_transform_alt :
    !pi. apply pi = FOLDL $o I pi
Proof
    REWRITE_TAC [apply_transform_def]
 >> LIST_INDUCT_TAC >> rw [FOLDL, FOLDR]
 >> KILL_TAC (* only FOLDL is left *)
 >> qid_spec_tac ‘pi’ >> SNOC_INDUCT_TAC
 >> rw [FOLDL_SNOC, FOLDL]
 >> POP_ASSUM (rw o wrap o SYM)
QED

Theorem apply_transform_rwts[simp] :
    (apply [] = I) /\
    (!f pi M. apply (f::pi) M = f (apply pi M)) /\
    (!f pi M. apply (SNOC f pi) M = apply pi (f M))
Proof
    NTAC 2 (CONJ_TAC >- rw [apply_transform_def, o_DEF])
 >> rw [apply_transform_alt, o_DEF, FOLDL_SNOC]
QED

(* Lemma 10.3.4 (i) [1, p.246] *)
Theorem Boehm_transform_lameq_ctxt :
    !pi. Boehm_transform pi ==> ?c. ctxt c /\ !M. apply pi M == c M
Proof
    Induct_on ‘pi’
 >> rw [Boehm_transform_def, apply_transform_def]
 >- (Q.EXISTS_TAC ‘\x. x’ >> rw [ctxt_rules, FOLDR])
 >> fs [GSYM Boehm_transform_def, apply_transform_def]
 >> fs [solving_transform_def]
 >- (Q.EXISTS_TAC ‘\y. c y @@ (\y. VAR x) y’ \\
     rw [ctxt_rules, FOLDR] \\
     MATCH_MP_TAC lameq_APPL >> art [])
 (* stage work *)
 >> Q.EXISTS_TAC ‘\y. (\z. LAM x (c z)) y @@ (\y. N) y’
 >> rw [ctxt_rules, constant_contexts_exist, FOLDR]
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘[N/x] (c M)’
 >> reverse CONJ_TAC >- rw [lameq_rules]
 >> irule lameq_sub_cong >> rw []
QED

(* Lemma 10.3.4 (ii) [1, p.246] *)
Theorem Boehm_transform_lameq_LAMl_appstar :
    !pi. Boehm_transform pi ==>
         ?c. ctxt c /\ (!M. apply pi M == c M) /\
             !vs. ALL_DISTINCT vs ==>
                  ?Ns. !M. FV M SUBSET (set vs) ==> c M == LAMl vs M @* Ns
Proof
    Induct_on ‘pi’
 >- (rw [] \\
     Q.EXISTS_TAC ‘\x. x’ >> rw [ctxt_rules] \\
     Q.EXISTS_TAC ‘MAP VAR vs’ >> rpt STRIP_TAC \\
     rw [Once lameq_SYM, lameq_LAMl_appstar_VAR])
 >> rw []
 >> Q.PAT_X_ASSUM ‘Boehm_transform pi ==> P’ MP_TAC
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [solving_transform_def] (* 2 subgoals *)
 (* goal 1 (of 2) *)
 >- (Q.EXISTS_TAC ‘\z. c z @@ (\z. VAR x) z’ \\
     rw [ctxt_rules, lameq_rules] \\
     Q.PAT_X_ASSUM ‘!vs. ALL_DISTINCT vs ==> P’ (drule_then STRIP_ASSUME_TAC) \\
     Q.EXISTS_TAC ‘SNOC (VAR x) Ns’ \\
     rw [appstar_SNOC, lameq_rules])
 (* goal 2 (of 2) *)
 >> rename1 ‘h = [P/y]’
 >> qabbrev_tac ‘c1 = \z. LAM y (c z)’
 >> ‘ctxt c1’ by rw [ctxt_rules, Abbr ‘c1’]
 >> Q.EXISTS_TAC ‘\z. c1 z @@ (\z. P) z’
 >> CONJ_TAC >- rw [ctxt_rules, constant_contexts_exist]
 >> CONJ_TAC
 >- (rw [Abbr ‘c1’] \\
     MATCH_MP_TAC lameq_TRANS >> Q.EXISTS_TAC ‘[P/y] (c M)’ \\
     rw [lameq_sub_cong, Once lameq_SYM, lameq_BETA])
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!vs. ALL_DISTINCT vs ==> _’ (drule_then STRIP_ASSUME_TAC)
 >> Q.EXISTS_TAC ‘MAP [P/y] Ns’
 >> rw [Abbr ‘c1’]
 >> Q.PAT_X_ASSUM ‘!M. FV M SUBSET set vs ==> _’ (drule_then STRIP_ASSUME_TAC)
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘[P/y] (c M)’ >> rw [lameq_BETA]
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘[P/y] (LAMl vs M @* Ns)’ >> rw [lameq_sub_cong]
 >> rw [appstar_SUB]
 >> Suff ‘[P/y] (LAMl vs M) = LAMl vs M’ >- rw []
 >> MATCH_MP_TAC lemma14b
 >> Suff ‘FV (LAMl vs M) = {}’ >- rw []
 >> rw [FV_LAMl]
 >> Q.PAT_X_ASSUM ‘FV M SUBSET (set vs)’ MP_TAC >> SET_TAC []
QED

(* An corollary of the above lemma with ‘xs = {}’ *)
Theorem Boehm_transform_lameq_appstar :
    !pi. Boehm_transform pi ==>
         ?Ns. !M. closed M ==> apply pi M == M @* Ns
Proof
    rpt STRIP_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP Boehm_transform_lameq_LAMl_appstar))
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘[]’))
 >> rw [closed_def]
 >> Q.EXISTS_TAC ‘Ns’
 >> RW_TAC (betafy (srw_ss())) []
QED

Theorem Boehm_apply_asmlam_cong :
    !pi M N. Boehm_transform pi /\ asmlam eqns M N ==>
             asmlam eqns (apply pi M) (apply pi N)
Proof
    SNOC_INDUCT_TAC >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> fs [solving_transform_def]
 >- rw [asmlam_rules]
 >> MATCH_MP_TAC asmlam_subst >> art []
QED

Theorem Boehm_apply_lameq_cong :
    !pi M N. Boehm_transform pi /\ M == N ==> apply pi M == apply pi N
Proof
    SNOC_INDUCT_TAC >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> MATCH_MP_TAC solving_transform_lameq >> art []
QED

Theorem Boehm_transform_APPEND :
    !p1 p2. Boehm_transform p1 /\ Boehm_transform p2 ==> Boehm_transform (p1 ++ p2)
Proof
    rw [Boehm_transform_def]
QED

Theorem Boehm_apply_APPEND :
    !p1 p2 M. apply (p1 ++ p2) M = apply p1 (apply p2 M)
Proof
    Q.X_GEN_TAC ‘p1’
 >> SNOC_INDUCT_TAC
 >> rw [APPEND_SNOC]
QED

Theorem Boehm_apply_SNOC_SUB :
    !(N :term) v p M. apply (SNOC [N/v] p) M = apply p ([N/v] M)
Proof
    rw [apply_transform_def, FOLDR_SNOC]
QED

Theorem Boehm_apply_MAP_rightctxt :
    !Ns t. apply (MAP rightctxt Ns) t = t @* (REVERSE Ns)
Proof
    Induct_on ‘Ns’ >> rw [rightctxt_thm]
 >> rw [GSYM SNOC_APPEND]
QED

Theorem Boehm_apply_MAP_rightctxt' :
    !Ns t. apply (MAP rightctxt (REVERSE Ns)) t = t @* Ns
Proof
    rpt GEN_TAC
 >> qabbrev_tac ‘Ns' = REVERSE Ns’
 >> ‘Ns = REVERSE Ns'’ by rw [Abbr ‘Ns'’, REVERSE_REVERSE]
 >> rw [Boehm_apply_MAP_rightctxt]
QED

(* NOTE: if M is solvable, ‘apply pi M’ may not be solvable. *)
Theorem Boehm_apply_unsolvable :
    !pi M. Boehm_transform pi /\ unsolvable M ==> unsolvable (apply pi M)
Proof
    SNOC_INDUCT_TAC >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> fs [solving_transform_def, solvable_iff_has_hnf] (* 2 subgaols *)
 >| [ (* goal 1 (of 2) *)
      CCONTR_TAC >> fs [] \\
      METIS_TAC [has_hnf_APP_E],
      (* goal 2 (of 2) *)
      CCONTR_TAC >> fs [] \\
      METIS_TAC [has_hnf_SUB_E] ]
QED

(* Definition 10.3.5 (ii) *)
Definition head_original_def :
    head_original M0 =
       let n = LAMl_size M0;
          vs = NEWS n (FV M0);
          M1 = principle_hnf (M0 @* MAP VAR vs)
        in
          EVERY (\e. hnf_headvar M1 # e) (hnf_children M1)
End

(* Definition 10.3.5 (iii)

   NOTE: The original definition uses ‘M == N’ in place of ‘M -h->* N’, but that
   is not enough for us, for the purposes of reduce ‘subterm X M p’ to
  ‘subterm X N p’, if only ‘M == N’ is known.
 *)
Definition is_ready_def :
    is_ready M <=> unsolvable M \/
                   ?N. M -h->* N /\ hnf N /\ ~is_abs N /\ head_original N
End

Definition is_ready'_def :
    is_ready' M <=> is_ready M /\ solvable M
End

(* NOTE: This alternative definition of ‘is_ready’ consumes ‘head_original’
         and eliminated the ‘principle_hnf’ inside it.
 *)
Theorem is_ready_alt :
    !M. is_ready M <=>
        unsolvable M \/ ?y Ns. M -h->* VAR y @* Ns /\ EVERY (\e. y # e) Ns
Proof
    Q.X_GEN_TAC ‘M’
 >> reverse EQ_TAC
 >- (rw [is_ready_def] >- art [] \\
     DISJ2_TAC >> Q.EXISTS_TAC ‘VAR y @* Ns’ >> art [] \\
     rw [head_original_def, hnf_appstar])
 (* stage work *)
 >> rw [is_ready_def] >- art []
 >> DISJ2_TAC
 >> qabbrev_tac ‘n = LAMl_size N’
 >> Q_TAC (NEWS_TAC (“vs :string list”, “n :num”)) ‘FV N’
 >> qabbrev_tac ‘M1 = principle_hnf (N @* MAP VAR vs)’
 >> ‘EVERY (\e. hnf_headvar M1 # e) (hnf_children M1)’
       by METIS_TAC [head_original_def]
 >> Know ‘?y args. N = LAMl (TAKE (LAMl_size N) vs) (VAR y @* args)’
 >- (Suff ‘ALL_DISTINCT vs /\ LAMl_size N <= LENGTH vs /\ DISJOINT (set vs) (FV N)’
     >- METIS_TAC [hnf_cases_shared] \\
     rw [Abbr ‘n’])
 >> ‘TAKE (LAMl_size N) vs = vs’ by rw [] >> POP_ORW
 >> STRIP_TAC
 >> Know ‘M1 = VAR y @* args’
 >- (rw [Abbr ‘M1’] \\
     MATCH_MP_TAC principle_hnf_beta_reduce >> rw [hnf_appstar])
 >> DISCH_THEN (fn th => fs [th, hnf_head_hnf, hnf_children_hnf])
 (* stage work *)
 >> qexistsl_tac [‘y’, ‘args’] >> art []
QED

Theorem is_ready_alt' :
    !M. is_ready' M <=> solvable M /\
                        ?y Ns. M -h->* VAR y @* Ns /\ EVERY (\e. y # e) Ns
Proof
 (* NOTE: this proof relies on the new [NOT_AND'] in boolSimps.BOOL_ss *)
    rw [is_ready'_def, is_ready_alt, RIGHT_AND_OVER_OR]
 >> REWRITE_TAC [Once CONJ_COMM]
QED

(* ‘subterm_width M p’ is the maximal number of children of all subterms of form
   ‘subterm X M q r’ such that ‘q <<= p’, irrelevant with particular X and r.

   NOTE: If the path is invalid or the subterms are all unsolvable, it gives 0.
 *)
Definition subterm_width_def[nocompute] :
    subterm_width M p =
    MAX_SET (IMAGE (\q. let N = subterm (FV M) M q 0 in
                        if N <> NONE /\ solvable (FST (THE N)) then
                           hnf_children_size (principle_hnf (FST (THE N)))
                        else 0) {q | q <<= p})
End

(* ‘subterm_length M p’ is the maximal length of LAMl binding list of subterms
   given by ‘subterm X M q r’ such that ‘q <<= p’, irrelevant with X and r.

   NOTE: The proof of subterm_length property is often dual of subterm_width.
 *)
Definition subterm_length_def[nocompute] :
    subterm_length M p =
    MAX_SET (IMAGE (\q. let N = subterm (FV M) M q 0 in
                        if N <> NONE /\ solvable (FST (THE N)) then
                           LAMl_size (principle_hnf (FST (THE N)))
                        else 0) {q | q <<= p})
End

Theorem subterm_width_nil :
    !M. subterm_width M [] = if solvable M then
                                hnf_children_size (principle_hnf M)
                             else 0
Proof
    rw [subterm_width_def]
QED

Theorem subterm_length_nil :
    !M. subterm_length M [] = if solvable M then
                                 LAMl_size (principle_hnf M)
                              else 0
Proof
    rw [subterm_length_def]
QED

Theorem subterm_width_inclusive :
    !M p q. q <<= p /\ subterm_width M p <= d ==> subterm_width M q <= d
Proof
    simp [subterm_width_def]
 >> rpt GEN_TAC
 >> qmatch_abbrev_tac ‘q <<= p /\ a <= d ==> b <= d’
 >> STRIP_TAC
 >> Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘a’
 >> POP_ASSUM (REWRITE_TAC o wrap)
 >> simp [Abbr ‘a’, Abbr ‘b’]
 >> MATCH_MP_TAC SUBSET_MAX_SET
 >> CONJ_TAC
 >- (MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 >> CONJ_TAC
 >- (MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 >> MATCH_MP_TAC IMAGE_SUBSET
 >> rw [SUBSET_DEF]
 >> Q_TAC (TRANS_TAC isPREFIX_TRANS) ‘q’ >> art []
QED

Theorem subterm_length_inclusive :
    !M p q. q <<= p /\ subterm_length M p <= d ==> subterm_length M q <= d
Proof
    simp [subterm_length_def]
 >> rpt GEN_TAC
 >> qmatch_abbrev_tac ‘q <<= p /\ a <= d ==> b <= d’
 >> STRIP_TAC
 >> Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘a’
 >> POP_ASSUM (REWRITE_TAC o wrap)
 >> simp [Abbr ‘a’, Abbr ‘b’]
 >> MATCH_MP_TAC SUBSET_MAX_SET
 >> CONJ_TAC
 >- (MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 >> CONJ_TAC
 >- (MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 >> MATCH_MP_TAC IMAGE_SUBSET
 >> rw [SUBSET_DEF]
 >> Q_TAC (TRANS_TAC isPREFIX_TRANS) ‘q’ >> art []
QED

Theorem subterm_width_thm :
    !X M p r.
       FINITE X /\ FV M SUBSET X UNION RANK r ==>
       subterm_width M p =
       MAX_SET (IMAGE (\q. let N = subterm X M q r in
                           if N <> NONE /\ solvable (FST (THE N)) then
                              hnf_children_size (principle_hnf (FST (THE N)))
                           else 0) {q | q <<= p})
Proof
    rw [subterm_width_def]
 >> AP_TERM_TAC
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC ‘q’ >> art [] \\
      MP_TAC (Q.SPECL [‘X’, ‘FV M’, ‘M’, ‘q’, ‘r’, ‘0’] subterm_tpm_cong) \\
      rw [tpm_rel_alt] >> gs [] \\
      simp [principle_hnf_tpm'],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC ‘q’ >> art [] \\
      MP_TAC (Q.SPECL [‘X’, ‘FV M’, ‘M’, ‘q’, ‘r’, ‘0’] subterm_tpm_cong) \\
      rw [tpm_rel_alt] >> gs [] \\
      simp [principle_hnf_tpm'] ]
QED

Theorem subterm_length_thm :
    !X M p r.
       FINITE X /\ FV M SUBSET X UNION RANK r ==>
       subterm_length M p =
       MAX_SET (IMAGE (\q. let N = subterm X M q r in
                           if N <> NONE /\ solvable (FST (THE N)) then
                              LAMl_size (principle_hnf (FST (THE N)))
                           else 0) {q | q <<= p})
Proof
    rw [subterm_length_def]
 >> AP_TERM_TAC
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC ‘q’ >> art [] \\
      MP_TAC (Q.SPECL [‘X’, ‘FV M’, ‘M’, ‘q’, ‘r’, ‘0’] subterm_tpm_cong) \\
      rw [tpm_rel_alt] >> gs [] \\
      simp [principle_hnf_tpm'],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC ‘q’ >> art [] \\
      MP_TAC (Q.SPECL [‘X’, ‘FV M’, ‘M’, ‘q’, ‘r’, ‘0’] subterm_tpm_cong) \\
      rw [tpm_rel_alt] >> gs [] \\
      simp [principle_hnf_tpm'] ]
QED

Theorem subterm_width_first :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\ solvable M
          ==> hnf_children_size (principle_hnf M) <= subterm_width M p
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘p’, ‘r’] subterm_width_thm)
 >> simp [] >> DISCH_THEN K_TAC
 >> irule MAX_SET_PROPERTY
 >> CONJ_TAC
 >- (MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 >> simp []
 >> Q.EXISTS_TAC ‘[]’ >> rw []
QED

Theorem subterm_length_first :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\ solvable M
          ==> LAMl_size (principle_hnf M) <= subterm_length M p
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘p’, ‘r’] subterm_length_thm)
 >> simp [] >> DISCH_THEN K_TAC
 >> irule MAX_SET_PROPERTY
 >> CONJ_TAC
 >- (MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 >> simp []
 >> Q.EXISTS_TAC ‘[]’ >> rw []
QED

Theorem subterm_width_last :
    !X M p q r.
       FINITE X /\ FV M SUBSET X UNION RANK r /\ q <<= p /\
       subterm X M q r <> NONE /\
       solvable (subterm' X M q r)
   ==> hnf_children_size (principle_hnf (subterm' X M q r)) <= subterm_width M p
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘p’, ‘r’] subterm_width_thm)
 >> simp [] >> DISCH_THEN K_TAC
 >> irule MAX_SET_PROPERTY
 >> CONJ_TAC
 >- (MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 >> simp []
 >> Q.EXISTS_TAC ‘q’ >> rw []
QED

Theorem subterm_length_last :
    !X M p q r.
       FINITE X /\ FV M SUBSET X UNION RANK r /\ q <<= p /\
       subterm X M q r <> NONE /\
       solvable (subterm' X M q r)
   ==> LAMl_size (principle_hnf (subterm' X M q r)) <= subterm_length M p
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘p’, ‘r’] subterm_length_thm)
 >> simp [] >> DISCH_THEN K_TAC
 >> irule MAX_SET_PROPERTY
 >> CONJ_TAC
 >- (MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 >> simp []
 >> Q.EXISTS_TAC ‘q’ >> rw []
QED

Theorem solvable_subst_permutator :
    !X M r P v d.
       FINITE X /\ FV M SUBSET X UNION RANK r /\
       v IN X UNION RANK r /\ P = permutator d /\
       solvable M /\ subterm_width M [] <= d
   ==> solvable ([P/v] M) /\ subterm_width ([P/v] M) [] <= d
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘P = permutator d’ (REWRITE_TAC o wrap)
 >> qabbrev_tac ‘P = permutator d’
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> ‘M0 == M’ by rw [Abbr ‘M0’, lameq_principle_hnf']
 >> ‘[P/v] M0 == [P/v] M’ by rw [lameq_sub_cong]
 >> ‘FV P = {}’ by rw [Abbr ‘P’, FV_permutator]
 >> ‘DISJOINT (set vs) (FV P)’ by rw [DISJOINT_ALT']
 >> Know ‘~MEM v vs’
 >- (Q.PAT_X_ASSUM ‘v IN X UNION RANK r’ MP_TAC \\
     rw [IN_UNION]
     >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) X’ MP_TAC \\
         rw [DISJOINT_ALT']) \\
     Suff ‘DISJOINT (RANK r) (set vs)’ >- rw [DISJOINT_ALT] \\
     qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC DISJOINT_RANK_RNEWS' >> art [])
 >> DISCH_TAC
 >> CONJ_ASM1_TAC
 >- (Suff ‘solvable ([P/v] M0)’ >- PROVE_TAC [lameq_solvable_cong] \\
     simp [LAMl_SUB, appstar_SUB] \\
     reverse (Cases_on ‘y = v’)
     >- (simp [SUB_THM, solvable_iff_has_hnf] \\
         MATCH_MP_TAC hnf_has_hnf >> rw [hnf_appstar]) \\
     simp [solvable_iff_has_hnf, has_hnf_thm] \\
     qabbrev_tac ‘args' = MAP [P/v] args’ \\
     qabbrev_tac ‘m = LENGTH args’ \\
    ‘LENGTH args' = m’ by rw [Abbr ‘args'’] \\
     Q.PAT_X_ASSUM ‘subterm_width M [] <= d’ MP_TAC \\
     rw [hnf_children_size_thm, subterm_width_nil] \\
  (* applying hreduce_permutator_thm *)
     MP_TAC (Q.SPECL [‘{}’, ‘d’, ‘args'’] hreduce_permutator_thm) \\
     rw [Abbr ‘P’] \\
     Q.EXISTS_TAC ‘LAMl xs (LAM y (VAR y @* args' @* MAP VAR xs))’ \\
     rw [hnf_appstar, hnf_thm])
 (* extra goal for induction *)
 >> Q.PAT_X_ASSUM ‘subterm_width M [] <= d’ MP_TAC
 >> simp [subterm_width_nil]
 >> DISCH_TAC
 (* applying principle_hnf_hreduce, hreduces_hnf_imp_principle_hnf, etc.

    M -h->* M0 = LAMl vs (VAR y @* args)
    [P/v] M -h->* [P/v] (LAMl vs (VAR y @* args))
  *)
 >> Know ‘[P/v] M -h->* [P/v] M0’
 >- (MATCH_MP_TAC hreduce_substitutive \\
     METIS_TAC [principle_hnf_thm'])
 >> simp [LAMl_SUB, appstar_SUB]
 >> reverse (Cases_on ‘y = v’)
 >- (simp [SUB_THM, solvable_iff_has_hnf] \\
     DISCH_TAC \\
     qabbrev_tac ‘args' = MAP [P/v] args’ \\
    ‘hnf (LAMl vs (VAR y @* args'))’ by rw [hnf_appstar] \\
    ‘principle_hnf ([P/v] M) = LAMl vs (VAR y @* args')’
       by METIS_TAC [principle_hnf_thm'] >> POP_ORW \\
     qabbrev_tac ‘m = LENGTH args’ \\
    ‘LENGTH args' = m’ by rw [Abbr ‘args'’] \\
     simp [])
 (* stage work *)
 >> simp []
 >> qabbrev_tac ‘args' = MAP [P/v] args’
 >> DISCH_TAC
 >> qabbrev_tac ‘m = LENGTH args’
 >> ‘LENGTH args' = m’ by rw [Abbr ‘args'’]
 >> MP_TAC (Q.SPECL [‘{}’, ‘d’, ‘args'’] hreduce_permutator_thm)
 >> simp []
 >> STRIP_TAC
 >> ‘LAMl vs (P @* args') -h->*
     LAMl vs (LAMl xs (LAM y' (VAR y' @* args' @* MAP VAR xs)))’
       by rw [hreduce_LAMl]
 >> Know ‘[P/v] M -h->* LAMl vs (LAMl xs (LAM y' (VAR y' @* args' @* MAP VAR xs)))’
 >- (MATCH_MP_TAC hreduce_TRANS \\
     Q.EXISTS_TAC ‘LAMl vs (P @* args')’ >> art [])
 >> REWRITE_TAC [GSYM LAMl_APPEND, GSYM appstar_APPEND, GSYM LAMl_SNOC]
 >> qabbrev_tac ‘ys = SNOC y' (vs ++ xs)’
 >> qabbrev_tac ‘args2 = args' ++ MAP VAR xs’
 >> DISCH_TAC
 >> ‘hnf (LAMl ys (VAR y' @* args2))’ by rw [hnf_appstar]
 >> ‘principle_hnf ([P/v] M) = LAMl ys (VAR y' @* args2)’
       by METIS_TAC [principle_hnf_thm']
 >> POP_ORW
 >> simp [Abbr ‘args2’]
QED

Theorem solvable_subst_permutator_cong :
    !X M r P v d.
       FINITE X /\ FV M SUBSET X UNION RANK r /\
       v IN X UNION RANK r /\ P = permutator d /\
       subterm_width M [] <= d ==>
      (solvable ([P/v] M) <=> solvable M)
Proof
    rpt STRIP_TAC
 >> EQ_TAC >- PROVE_TAC [unsolvable_subst]
 >> DISCH_TAC
 >> MATCH_MP_TAC (cj 1 solvable_subst_permutator)
 >> qexistsl_tac [‘X’, ‘r’, ‘d’] >> art []
QED

Theorem solvable_isub_permutator :
    !X r d ss M.
       FINITE X /\ FV M SUBSET X UNION RANK r /\
       DOM ss SUBSET X UNION RANK r /\
      (!P. MEM P (MAP FST ss) ==> P = permutator d) /\
       solvable M /\ subterm_width M [] <= d
   ==> solvable (M ISUB ss) /\
       subterm_width (M ISUB ss) [] <= d
Proof
    NTAC 3 GEN_TAC
 >> Induct_on ‘ss’ >- rw []
 >> simp [FORALL_PROD, DOM_DEF]
 >> qx_genl_tac [‘P’, ‘v’, ‘M’]
 >> STRIP_TAC
 >> qabbrev_tac ‘Q = permutator d’
 >> qabbrev_tac ‘N = [Q/v] M’
 >> FIRST_X_ASSUM MATCH_MP_TAC >> simp []
 >> CONJ_TAC
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M’ >> art [] \\
     simp [Abbr ‘N’, FV_SUB, Abbr ‘Q’, FV_permutator] \\
     SET_TAC [])
 >> qunabbrev_tac ‘N’
 >> MATCH_MP_TAC solvable_subst_permutator
 >> qexistsl_tac [‘X’, ‘r’] >> simp []
QED

Theorem solvable_isub_permutator_cong :
    !X M r ss d.
       FINITE X /\ FV M SUBSET X UNION RANK r /\
       subterm_width M [] <= d /\
       DOM ss SUBSET X UNION RANK r /\
      (!P. MEM P (MAP FST ss) ==> P = permutator d) ==>
      (solvable (M ISUB ss) <=> solvable M)
Proof
    rpt STRIP_TAC
 >> EQ_TAC >- METIS_TAC [unsolvable_ISUB]
 >> DISCH_TAC
 >> MATCH_MP_TAC (cj 1 solvable_isub_permutator)
 >> qexistsl_tac [‘X’, ‘r’, ‘d’] >> art []
QED

(* NOTE: This is the first of a series of lemmas of increasing permutators.
   In theory the proof works if each permutator is larger than the previous
   one, not necessary increased just by one (which is enough for now).

   In other words, ‘ss = GENLIST (\i. (permutator (d + i),y i)) k’ can be
   replaced by ‘ss = GENLIST (\i. (permutator (f i),y i)) k’ where ‘f’ is
   increasing (or non-decreasing).
 *)
Theorem solvable_isub_permutator_alt :
    !X r d y k ss M.
       FINITE X /\ FV M SUBSET X UNION RANK r /\
      (!i. i < k ==> y i IN X UNION RANK r) /\
       ss = GENLIST (\i. (permutator (d + i),y i)) k /\
       solvable M /\ subterm_width M [] <= d
   ==> solvable (M ISUB ss) /\
       subterm_width (M ISUB ss) [] <= d + k
Proof
    NTAC 4 GEN_TAC
 >> Induct_on ‘k’ >- rw []
 >> qx_genl_tac [‘ss'’, ‘M’]
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘ss' = _’ (REWRITE_TAC o wrap)
 >> SIMP_TAC std_ss [GENLIST, ISUB_SNOC]
 >> qabbrev_tac ‘P = \i. permutator (d + i)’ >> fs []
 >> qabbrev_tac ‘ss = GENLIST (\i. (P i,y i)) k’
 >> Q.PAT_X_ASSUM ‘!M'. FV M' SUBSET X UNION RANK r /\ _ ==> _’
      (MP_TAC o Q.SPEC ‘M’)
 >> simp []
 >> STRIP_TAC
 >> qabbrev_tac ‘N = M ISUB ss’
 >> qabbrev_tac ‘Q = P k’
 >> qabbrev_tac ‘v = y k’
 >> qabbrev_tac ‘w = d + k’
 >> MP_TAC (Q.SPECL [‘X’, ‘N’, ‘r’, ‘Q’, ‘v’, ‘w’] solvable_subst_permutator)
 >> simp [Abbr ‘Q’, Abbr ‘v’, Abbr ‘w’]
 >> impl_tac
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M’ >> art [] \\
     qunabbrev_tac ‘N’ \\
     MP_TAC (Q.SPECL [‘ss’, ‘M’] FV_ISUB_upperbound) \\
     Suff ‘FVS ss = {}’ >- simp [] \\
     simp [Abbr ‘ss’, FVS_ALT] \\
     Cases_on ‘k = 0’ >> simp [] \\
     DISJ2_TAC \\
     simp [MAP_GENLIST, LIST_TO_SET_GENLIST] \\
     simp [Abbr ‘P’, FV_permutator, o_DEF] \\
     simp [IMAGE_CONST])
 >> rw []
QED

Theorem subterm_width_induction_lemma :
    !X M h p r M0 n n' m vs' M1 Ms d.
         FINITE X /\ FV M SUBSET X UNION RANK r /\
         solvable M /\
         M0 = principle_hnf M /\
          n = LAMl_size M0 /\ n <= n' /\
          m = hnf_children_size M0 /\ h < m /\
        vs' = RNEWS r n' X /\
         M1 = principle_hnf (M0 @* MAP VAR vs') /\
         Ms = hnf_children M1 ==>
        (subterm_width M (h::p) <= d <=>
         m <= d /\ subterm_width (EL h Ms) p <= d)
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> qabbrev_tac ‘m = hnf_children_size M0’
 >> Q_TAC (RNEWS_TAC (“vs' :string list”, “r :num”, “n' :num”)) ‘X’
 >> ‘DISJOINT (set vs') (FV M0)’ by PROVE_TAC [subterm_disjoint_lemma']
 >> qabbrev_tac ‘M1' = principle_hnf (M0 @* MAP VAR vs')’
 >> qabbrev_tac ‘Ms = hnf_children M1'’
 (* applying subterm_width_thm *)
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::p’, ‘r’] subterm_width_thm) >> simp []
 >> DISCH_THEN K_TAC (* used already *)
 (* applying subterm_width_thm again *)
 >> MP_TAC (Q.SPECL [‘X’, ‘EL h Ms’, ‘p’, ‘SUC r’] subterm_width_thm)
 >> simp []
 >> impl_tac
 >- (MATCH_MP_TAC subterm_induction_lemma \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘n'’, ‘m’, ‘vs'’, ‘M1'’] >> simp [])
 >> Rewr'
 (* now decompose M0 in two ways (M1 and M1') *)
 >> ‘hnf M0’ by PROVE_TAC [hnf_principle_hnf']
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> ‘DISJOINT (set vs) (FV M0)’ by PROVE_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                     “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> Know ‘?y' args'. M0 = LAMl (TAKE n vs') (VAR y' @* args')’
 >- (qunabbrev_tac ‘n’ >> irule (iffLR hnf_cases_shared) \\
     Q.PAT_X_ASSUM ‘M0 = _’ K_TAC >> simp [])
 >> STRIP_TAC
 >> Know ‘solvable (M0 @* MAP VAR vs')’
 >- (MATCH_MP_TAC solvable_appstar \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘n'’] >> simp [])
 >> DISCH_TAC
 >> Know ‘vs <<= vs'’
 >- (qunabbrevl_tac [‘vs’, ‘vs'’] \\
     MATCH_MP_TAC RNEWS_prefix >> rw [])
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [IS_PREFIX_APPEND]))
 >> Know ‘TAKE n vs' = vs’
 >- (Q.PAT_X_ASSUM ‘LENGTH vs = n’ (REWRITE_TAC o wrap o SYM) \\
     simp [TAKE_LENGTH_APPEND])
 >> DISCH_THEN (rfs o wrap) >> T_TAC
 >> Q.PAT_X_ASSUM ‘y = y'’       (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘args = args'’ (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M0 = _’ (ASSUME_TAC o SYM)
 >> gs [MAP_APPEND, appstar_APPEND, LIST_TO_SET_APPEND, ALL_DISTINCT_APPEND]
 (* applying hreduce_BETA_extended *)
 >> Know ‘M0 @* MAP VAR vs @* MAP VAR l -h->* VAR y @* args @* MAP VAR l’
 >- (Q.PAT_X_ASSUM ‘_ = M0’ (REWRITE_TAC o wrap o SYM) \\
     REWRITE_TAC [hreduce_BETA_extended])
 >> DISCH_TAC
 >> Know ‘M1' = VAR y @* args @* MAP VAR l’
 >- (qunabbrev_tac ‘M1'’ \\
     simp [principle_hnf_thm', GSYM appstar_APPEND, hnf_appstar])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘M0 @* MAP VAR vs @* MAP VAR l -h->* _’ K_TAC
 (* stage work *)
 >> qmatch_abbrev_tac
     ‘MAX_SET (IMAGE f {q | q <<= h::p}) <= d <=>
      m <= d /\ MAX_SET (IMAGE g {q | q <<= p}) <= d’
 >> Know ‘IMAGE f {q | q <<= h::p} = m INSERT (IMAGE g {q | q <<= p})’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rw [Abbr ‘f’, Abbr ‘g’] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       rename1 ‘q <<= h::p’ \\
       Cases_on ‘q’ >> fs [] \\
       Cases_on ‘subterm X M (h::t) r = NONE’ >> fs []
       >- (Q.EXISTS_TAC ‘t’ >> art [] \\
           POP_ASSUM MP_TAC \\
           Q_TAC (UNBETA_TAC [subterm_of_solvables]) ‘subterm X M (h::t) r’ \\
           Suff ‘EL h Ms = EL h args’ >- rw [] \\
           simp [Abbr ‘Ms’, GSYM appstar_APPEND, Abbr ‘m’] \\
           MATCH_MP_TAC EL_APPEND1 >> art []) \\
       DISJ2_TAC \\
       Q.EXISTS_TAC ‘t’ >> art [] \\
       POP_ASSUM MP_TAC \\
       Q_TAC (UNBETA_TAC [subterm_of_solvables]) ‘subterm X M (h::t) r’ \\
       Suff ‘EL h Ms = EL h args’ >- rw [] \\
       simp [Abbr ‘Ms’, GSYM appstar_APPEND, Abbr ‘m’] \\
       MATCH_MP_TAC EL_APPEND1 >> art [],
       (* goal 2 (of 3) *)
       Q.EXISTS_TAC ‘[]’ >> rw [],
       (* goal 3 (of 3) *)
       rename1 ‘q <<= p’ \\
       Q.EXISTS_TAC ‘h::q’ >> simp [] \\
       Cases_on ‘subterm X M (h::q) r = NONE’ >> fs []
       >- (POP_ASSUM MP_TAC \\
           Q_TAC (UNBETA_TAC [subterm_of_solvables]) ‘subterm X M (h::q) r’ \\
           Suff ‘EL h Ms = EL h args’ >- rw [] \\
           simp [Abbr ‘Ms’, GSYM appstar_APPEND, Abbr ‘m’] \\
           MATCH_MP_TAC EL_APPEND1 >> art []) \\
       POP_ASSUM MP_TAC \\
       Q_TAC (UNBETA_TAC [subterm_of_solvables]) ‘subterm X M (h::q) r’ \\
       Suff ‘EL h Ms = EL h args’ >- rw [] \\
       simp [Abbr ‘Ms’, GSYM appstar_APPEND, Abbr ‘m’] \\
       MATCH_MP_TAC EL_APPEND1 >> art [] ])
 >> Rewr'
 >> qunabbrev_tac ‘f’
 >> qmatch_abbrev_tac ‘MAX_SET (m INSERT s) <= d <=> m <= d /\ MAX_SET s <= d’
 >> Suff ‘MAX_SET (m INSERT s) = MAX m (MAX_SET s)’
 >- (Rewr' >> rw [MAX_LE])
 >> Suff ‘FINITE s’ >- PROVE_TAC [MAX_SET_THM]
 >> qunabbrev_tac ‘s’
 >> MATCH_MP_TAC IMAGE_FINITE
 >> rw [FINITE_prefix]
QED

Theorem subterm_width_induction_lemma' :
    !X M h p r M0 n m vs M1 Ms d.
         FINITE X /\ FV M SUBSET X UNION RANK r /\
         h::p IN ltree_paths (BT' X M r) /\
         solvable M /\
         M0 = principle_hnf M /\
          n = LAMl_size M0 /\
          m = hnf_children_size M0 /\ h < m /\
         vs = RNEWS r n X /\
         M1 = principle_hnf (M0 @* MAP VAR vs) /\
         Ms = hnf_children M1 ==>
        (subterm_width M (h::p) <= d <=>
         m <= d /\ subterm_width (EL h Ms) p <= d)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC subterm_width_induction_lemma
 >> qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’, ‘n’, ‘vs’, ‘M1’] >> simp []
QED

(* NOTE: This is another induction lemma of subterm_width, which is more general
   but does not contain [subterm_width_induction_lemma].

   In this case, vs is NOT a prefix of vs' but actually disjoint with it.
   The proof becomes even harder, because ‘tpm’ is involved additionally.

   NOTE: ‘X’ is the usual excluded set for induction. ‘Y’ is a fixed variable set
   acting as ‘IMAGE FV (set Ms)’ if M is one of Ms.
 *)
Theorem subterm_width_induction_lemma_alt[local] :
    !X Y M h p r M0 n n' m vs' M1 Ms d.
         FINITE X /\ FV M SUBSET X UNION RANK r /\ 0 < r /\
         FINITE Y /\ FV M SUBSET Y /\
         M0 = principle_hnf M /\ solvable M /\
          n = LAMl_size M0 /\ n <= n' /\
          m = hnf_children_size M0 /\ h < m /\
        vs' = NEWS n' (X UNION Y) /\
         M1 = principle_hnf (M0 @* MAP VAR vs') /\
         Ms = hnf_children M1 ==>
        (subterm_width M (h::p) <= d <=>
         m <= d /\ subterm_width (EL h Ms) p <= d)
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> qabbrev_tac ‘m = hnf_children_size M0’
 >> Q_TAC (NEWS_TAC (“vs' :string list”, “n' :num”)) ‘X UNION Y’
 >> Know ‘DISJOINT (set vs') (FV M)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘Y’ >> art [])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set vs') (FV M0)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘FV M’ >> art [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘M1' = principle_hnf (M0 @* MAP VAR vs')’
 >> qabbrev_tac ‘Ms = hnf_children M1'’
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::p’, ‘r’] subterm_width_thm) >> simp []
 >> DISCH_THEN K_TAC (* used already *)
 >> ‘hnf M0’ by PROVE_TAC [hnf_principle_hnf']
 (* Define vs as prefix of vs' *)
 >> qabbrev_tac ‘vs = TAKE n vs'’
 >> ‘ALL_DISTINCT vs’
       by (qunabbrev_tac ‘vs’ >> MATCH_MP_TAC ALL_DISTINCT_TAKE >> art [])
 >> ‘LENGTH vs = n’
       by (qunabbrev_tac ‘vs’ >> MATCH_MP_TAC LENGTH_TAKE >> art [])
 (* Define zs as substitutions of vs *)
 >> Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n :num”)) ‘X’
 >> Know ‘DISJOINT (set zs) (set vs')’
 >- (qunabbrev_tac ‘zs’ \\
     MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘RANK r’ >> rw [DISJOINT_RNEWS_RANK'] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ \\
     CONJ_TAC >- rw [Abbr ‘vs'’, RNEWS_SUBSET_ROW] \\
     rw [ROW_SUBSET_RANK])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set zs) (set vs)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘set vs'’ >> art [] \\
     rw [Abbr ‘vs’, LIST_TO_SET_TAKE])
 >> DISCH_TAC
 (* now decompose M0 in two ways (to M1 and M1') *)
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR zs)’
 >> ‘DISJOINT (set zs) (FV M0)’ by PROVE_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “zs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n zs = zs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> Know ‘?y' args'. M0 = LAMl vs (VAR y' @* args')’
 >- (qunabbrevl_tac [‘n’, ‘vs’] >> irule (iffLR hnf_cases_shared) \\
     Q.PAT_X_ASSUM ‘M0 = _’ K_TAC \\
     simp [])
 >> STRIP_TAC (* this asserts y' and args' *)
 >> Know ‘vs <<= vs'’
 >- (simp [Abbr ‘vs’, IS_PREFIX_EQ_TAKE'] \\
     Q.EXISTS_TAC ‘n’ >> art [])
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [IS_PREFIX_APPEND]))
 >> qabbrev_tac ‘t = VAR y' @* args'’
 >> Know ‘principle_hnf (LAMl vs t @* MAP VAR zs) = tpm (ZIP (vs,zs)) t’
 >- (‘hnf t’ by rw [Abbr ‘t’, hnf_appstar] \\
     MATCH_MP_TAC principle_hnf_tpm_reduce' >> art [] \\
     CONJ_TAC >- rw [Once DISJOINT_SYM] \\
     MATCH_MP_TAC subterm_disjoint_lemma \\
     qexistsl_tac [‘X’, ‘r’, ‘n’] >> simp [] \\
     Know ‘FV M0 SUBSET X UNION RANK r’
     >- (Suff ‘FV M0 SUBSET FV M’ >- METIS_TAC [SUBSET_DEF] \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) \\
     Q.PAT_X_ASSUM ‘M0 = LAMl vs t’ (REWRITE_TAC o wrap) \\
     simp [FV_LAMl] \\
     Suff ‘set vs SUBSET RANK r’ >- SET_TAC [] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs'’ \\
     CONJ_TAC >- simp [LIST_TO_SET_APPEND] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ \\
     CONJ_TAC >- rw [Abbr ‘vs'’, RNEWS_SUBSET_ROW] \\
     rw [ROW_SUBSET_RANK])
 >> Q.PAT_ASSUM ‘M0 = LAMl vs t’ (REWRITE_TAC o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M0 = LAMl zs _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = VAR y @* _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M0 = LAMl vs t’ (ASSUME_TAC o SYM)
 >> simp [Abbr ‘t’, tpm_appstar]
 >> qabbrev_tac ‘pi = ZIP (vs,zs)’
 >> qabbrev_tac ‘y'' = lswapstr pi y'’
 >> qabbrev_tac ‘args'' = listpm term_pmact pi args'’
 >> DISCH_THEN (ASSUME_TAC o SYM) (* store M1 *)
 (* applying hreduce_BETA_extended *)
 >> Know ‘M0 @* MAP VAR vs @* MAP VAR l -h->* VAR y' @* args' @* MAP VAR l’
 >- (Q.PAT_X_ASSUM ‘LAMl vs _ = M0’ (REWRITE_TAC o wrap o SYM) \\
     REWRITE_TAC [hreduce_BETA_extended])
 >> DISCH_TAC
 >> Know ‘M1' = VAR y' @* args' @* MAP VAR l’
 >- (qunabbrev_tac ‘M1'’ \\
     MATCH_MP_TAC hreduces_hnf_imp_principle_hnf \\
     simp [appstar_APPEND] \\
     simp [GSYM appstar_APPEND, hnf_appstar])
 >> DISCH_THEN (ASSUME_TAC o SYM) (* store M1' *)
 >> Know ‘Ms = args' ++ MAP VAR l’
 >- (qunabbrev_tac ‘Ms’ \\
     POP_ASSUM (REWRITE_TAC o wrap o SYM) \\
     simp [GSYM appstar_APPEND])
 >> DISCH_THEN (ASSUME_TAC o SYM) (* store Ms *)
 >> Know ‘LENGTH args = m’
 >- (qunabbrev_tac ‘m’ \\
     Q.PAT_X_ASSUM ‘LAMl zs (VAR y @* args) = M0’ (REWRITE_TAC o wrap o SYM) \\
     simp [])
 >> DISCH_TAC
 >> Know ‘LENGTH args' = m’
 >- (qunabbrev_tac ‘m’ \\
     Q.PAT_X_ASSUM ‘LAMl vs (VAR y' @* args') = M0’ (REWRITE_TAC o wrap o SYM) \\
     simp [])
 >> DISCH_TAC
 (* applying subterm_width_thm again *)
 >> MP_TAC (Q.SPECL [‘X’, ‘EL h Ms’, ‘p’, ‘SUC r’] subterm_width_thm)
 >> simp []
 >> Know ‘FV (EL h Ms) SUBSET X UNION RANK (SUC r)’
 >- (Q.PAT_X_ASSUM ‘args' ++ MAP VAR l = Ms’ (REWRITE_TAC o wrap o SYM) \\
     Know ‘EL h (args' ++ MAP VAR l) = EL h args'’
     >- (MATCH_MP_TAC EL_APPEND1 >> art []) >> Rewr' \\
     Know ‘FV M0 SUBSET X UNION RANK r’
     >- (Suff ‘FV M0 SUBSET FV M’ >- METIS_TAC [SUBSET_TRANS] \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) \\
     Q.PAT_X_ASSUM ‘LAMl vs (VAR y' @* args') = M0’ (REWRITE_TAC o wrap o SYM) \\
     simp [FV_LAMl, FV_appstar] \\
     qabbrev_tac ‘s = BIGUNION (IMAGE FV (set args'))’ \\
     qabbrev_tac ‘t = FV (EL h args')’ \\
     Know ‘t SUBSET s’
     >- (rw [Abbr ‘t’, Abbr ‘s’, SUBSET_DEF] \\
         Q.EXISTS_TAC ‘FV (EL h args')’ >> art [] \\
         Q.EXISTS_TAC ‘EL h args'’ >> art [] \\
         rw [EL_MEM]) \\
     Suff ‘set vs SUBSET X UNION RANK r’
     >- (Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [RANK_MONO]) \\
     Suff ‘set vs SUBSET RANK r’ >- SET_TAC [] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs'’ \\
     CONJ_TAC >- simp [LIST_TO_SET_APPEND] \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ \\
     CONJ_TAC >- rw [Abbr ‘vs'’, RNEWS_SUBSET_ROW] \\
     rw [ROW_SUBSET_RANK])
 >> DISCH_TAC
 >> simp [] >> DISCH_THEN K_TAC
 >> Q.PAT_X_ASSUM ‘M0 @* MAP VAR vs @* MAP VAR l -h->* _’ K_TAC
  (* shared properties for the next ‘s = t’ subgoal *)
 >> Know ‘set (MAP FST pi) SUBSET RANK (SUC r) /\
          set (MAP SND pi) SUBSET RANK (SUC r)’
 >- (simp [Abbr ‘pi’, MAP_ZIP] \\
     reverse CONJ_TAC
     >- (qunabbrev_tac ‘zs’ \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW r’ \\
         simp [RNEWS_SUBSET_ROW, ROW_SUBSET_RANK]) \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs'’ \\
     CONJ_TAC >- simp [Abbr ‘vs'’] \\
     qunabbrev_tac ‘vs'’ \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ \\
     simp [RNEWS_SUBSET_ROW, ROW_SUBSET_RANK])
 >> STRIP_TAC
 (* stage work *)
 >> qmatch_abbrev_tac
     ‘MAX_SET (IMAGE f {q | q <<= h::p}) <= d <=>
      m <= d /\ MAX_SET (IMAGE g {q | q <<= p}) <= d’
 >> Know ‘IMAGE f {q | q <<= h::p} = m INSERT (IMAGE g {q | q <<= p})’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rw [Abbr ‘f’, Abbr ‘g’] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       rename1 ‘q <<= h::p’ \\
       Cases_on ‘q’ >> fs [] \\
       Cases_on ‘subterm X M (h::t) r = NONE’ >> fs []
       >- (DISJ2_TAC \\
           Q.EXISTS_TAC ‘t’ >> art [] \\
           POP_ASSUM MP_TAC \\
           Q_TAC (UNBETA_TAC [subterm_of_solvables]) ‘subterm X M (h::t) r’ \\
           simp [] \\
           Know ‘EL h (args' ++ MAP VAR l) = EL h args'’
           >- (MATCH_MP_TAC EL_APPEND1 >> art []) \\
           DISCH_THEN (fs o wrap) \\
           qabbrev_tac ‘N = EL h args'’ \\
           Know ‘EL h args = tpm pi N’
           >- (simp [Abbr ‘args’]) >> Rewr' \\
           Know ‘subterm X N t (SUC r) = NONE <=>
                 subterm X (tpm pi N) t (SUC r) = NONE’
           >- (MATCH_MP_TAC (cj 1 subterm_tpm_lemma') >> simp []) \\
           simp []) \\
       DISJ2_TAC >> Q.EXISTS_TAC ‘t’ >> art [] \\
       POP_ASSUM MP_TAC \\
       Q_TAC (UNBETA_TAC [subterm_of_solvables]) ‘subterm X M (h::t) r’ \\
       simp [] \\
       Know ‘EL h (args' ++ MAP VAR l) = EL h args'’
       >- (MATCH_MP_TAC EL_APPEND1 >> art []) \\
       DISCH_THEN (fs o wrap) \\
       qabbrev_tac ‘N = EL h args'’ \\
       Know ‘EL h args = tpm pi N’
       >- (simp [Abbr ‘args’]) >> Rewr' \\
       DISCH_TAC \\
       Know ‘subterm X N t (SUC r) = NONE <=>
             subterm X (tpm pi N) t (SUC r) = NONE’
       >- (MATCH_MP_TAC (cj 1 subterm_tpm_lemma') >> simp []) \\
       simp [] >> DISCH_TAC \\
       Know ‘?pi'. tpm pi' (subterm' X N t (SUC r)) =
                   subterm' X (tpm pi N) t (SUC r)’
       >- (irule (cj 2 subterm_tpm_lemma') >> simp []) >> STRIP_TAC \\
       POP_ASSUM (REWRITE_TAC o wrap o SYM) \\
       simp [solvable_tpm] \\
       Cases_on ‘solvable (subterm' X N t (SUC r))’ >> rw [] \\
       simp [principle_hnf_tpm'],
       (* goal 2 (of 3) *)
       Q.EXISTS_TAC ‘[]’ >> rw [],
       (* goal 3 (of 3) *)
       rename1 ‘q <<= p’ \\
       Q.EXISTS_TAC ‘h::q’ >> simp [] \\
       Know ‘EL h (args' ++ MAP VAR l) = EL h args'’
       >- (MATCH_MP_TAC EL_APPEND1 >> art []) \\
       DISCH_THEN (fs o wrap) \\
       Cases_on ‘subterm X M (h::q) r = NONE’ >> fs []
       >- (POP_ASSUM MP_TAC \\
           Q_TAC (UNBETA_TAC [subterm_of_solvables]) ‘subterm X M (h::q) r’ \\
           simp [] \\
           qabbrev_tac ‘N = EL h args'’ \\
           Know ‘EL h args = tpm pi N’
           >- (simp [Abbr ‘args’]) >> Rewr' \\
           Know ‘subterm X N q (SUC r) = NONE <=>
                 subterm X (tpm pi N) q (SUC r) = NONE’
           >- (MATCH_MP_TAC (cj 1 subterm_tpm_lemma') >> simp []) \\
           simp []) \\
       POP_ASSUM MP_TAC \\
       Q_TAC (UNBETA_TAC [subterm_of_solvables]) ‘subterm X M (h::q) r’ \\
       simp [] \\
       qabbrev_tac ‘N = EL h args'’ \\
       Know ‘EL h args = tpm pi N’
       >- (simp [Abbr ‘N’, Abbr ‘args’]) >> Rewr' \\
       DISCH_TAC \\
       Know ‘subterm X N q (SUC r) = NONE <=>
             subterm X (tpm pi N) q (SUC r) = NONE’
       >- (MATCH_MP_TAC (cj 1 subterm_tpm_lemma') >> simp []) \\
       simp [] >> DISCH_TAC \\
       Know ‘?pi'. tpm pi' (subterm' X N q (SUC r)) =
                   subterm' X (tpm pi N) q (SUC r)’
       >- (irule (cj 2 subterm_tpm_lemma') >> simp []) >> STRIP_TAC \\
       POP_ASSUM (REWRITE_TAC o wrap o SYM) \\
       simp [solvable_tpm] \\
       Cases_on ‘solvable (subterm' X N q (SUC r))’ >> rw [] \\
       simp [principle_hnf_tpm'] ])
 >> Rewr'
 >> qunabbrev_tac ‘f’
 >> qmatch_abbrev_tac ‘MAX_SET (m INSERT s) <= d <=> m <= d /\ MAX_SET s <= d’
 >> Suff ‘MAX_SET (m INSERT s) = MAX m (MAX_SET s)’
 >- (Rewr' >> rw [MAX_LE])
 >> Suff ‘FINITE s’ >- PROVE_TAC [MAX_SET_THM]
 >> qunabbrev_tac ‘s’
 >> MATCH_MP_TAC IMAGE_FINITE
 >> rw [FINITE_prefix]
QED

(* NOTE: v, P and d are fixed free variables here *)
Theorem subterm_subst_permutator_cong_lemma[local] :
    !X. FINITE X ==>
        !q M p r. q <<= p /\
                  FV M SUBSET X UNION RANK r /\
                  subterm X M p r <> NONE /\
                  subterm_width M p <= d /\
                  P = permutator d /\ v IN X UNION RANK r
              ==> subterm X ([P/v] M) q r <> NONE /\
                  subterm_width ([P/v] M) q <= d /\
                  subterm' X ([P/v] M) q r = [P/v] (subterm' X M q r)
Proof
    NTAC 2 STRIP_TAC
 (* NOTE: After the last modification of subterm_width_def, the base case is
    non-trivial now. *)
 >> Induct_on ‘q’
 >- (rw [] \\
     qabbrev_tac ‘P = permutator d’ \\
     Cases_on ‘solvable ([P/v] M)’ >> rw [subterm_width_def] \\
    ‘solvable M’ by PROVE_TAC [unsolvable_subst] \\
     qabbrev_tac ‘M0 = principle_hnf M’ \\
     qabbrev_tac ‘n = LAMl_size M0’ \\
     Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’ \\
    ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma'] \\
     qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’ \\
     Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                     “y :string”, “args :term list”)) ‘M1’ \\
    ‘TAKE n vs = vs’ by rw [] \\
     POP_ASSUM (rfs o wrap) \\
    ‘M -h->* M0’ by METIS_TAC [principle_hnf_thm'] \\
     Know ‘[P/v] M -h->* [P/v] M0’ >- PROVE_TAC [hreduce_substitutive] \\
    ‘DISJOINT (set vs) (FV P)’ by rw [DISJOINT_ALT', FV_permutator, Abbr ‘P’] \\
     Know ‘~MEM v vs’
     >- (Q.PAT_X_ASSUM ‘v IN X UNION RANK r’ MP_TAC \\
         rw [IN_UNION]
         >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) X’ MP_TAC \\
             rw [DISJOINT_ALT']) \\
         Suff ‘DISJOINT (RANK r) (set vs)’ >- rw [DISJOINT_ALT] \\
         qunabbrev_tac ‘vs’ \\
         MATCH_MP_TAC DISJOINT_RANK_RNEWS' >> art []) >> DISCH_TAC \\
     simp [LAMl_SUB, appstar_SUB] \\
     qabbrev_tac ‘args' = MAP [P/v] args’ \\
    ‘LENGTH args' = LENGTH args’ by rw [Abbr ‘args'’] \\
     Know ‘LENGTH args <= d’
     >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width M p’ >> art [] \\
        ‘LENGTH args = hnf_children_size (principle_hnf M)’ by rw [] \\
         POP_ORW \\
         MATCH_MP_TAC subterm_width_first \\
         qexistsl_tac [‘X’, ‘r’] >> art []) >> DISCH_TAC \\
     reverse (Cases_on ‘v = y’)
     >- (simp [] \\
         DISCH_TAC (* [P/v] M -h->* LAMl vs (VAR y @* args') *) \\
        ‘FV P = {}’ by rw [Abbr ‘P’, FV_permutator] \\
        ‘hnf (LAMl vs (VAR y @* args'))’ by rw [hnf_appstar] \\
        ‘principle_hnf ([P/v] M) = LAMl vs (VAR y @* args')’
           by METIS_TAC [principle_hnf_thm'] >> POP_ORW \\
         simp [hnf_children_size_LAMl]) \\
     simp [Abbr ‘P’] \\
     POP_ASSUM (fs o wrap o SYM) >> T_TAC \\
     DISCH_TAC (* [permutator d/y] M -h->* ... *) \\
     MP_TAC (Q.SPECL [‘set vs’, ‘d’, ‘args'’] hreduce_permutator_thm) \\
     simp [] \\
     STRIP_TAC (* this asserts new fresh lists to be renamed: ‘xs’ and ‘y’ *) \\
     Know ‘[permutator d/v] M -h->*
             LAMl vs (LAMl xs (LAM y (VAR y @* args' @* MAP VAR xs)))’
     >- (MATCH_MP_TAC hreduce_TRANS \\
         Q.EXISTS_TAC ‘LAMl vs (permutator d @* args')’ >> rw []) \\
     DISCH_TAC \\
    ‘hnf (LAMl vs (LAMl xs (LAM y (VAR y @* args' @* MAP VAR xs))))’
       by rw [hnf_LAMl, hnf_appstar] \\
     qabbrev_tac ‘P = permutator d’ \\
    ‘principle_hnf ([P/v] M) =
     LAMl vs (LAMl xs (LAM y (VAR y @* args' @* MAP VAR xs)))’
       by METIS_TAC [principle_hnf_thm'] >> POP_ORW \\
     simp [hnf_children_size_LAMl, GSYM appstar_APPEND])
 (* stage work *)
 >> rpt GEN_TAC >> STRIP_TAC
 >> ‘p IN ltree_paths (BT' X M r)’ by PROVE_TAC [subterm_imp_ltree_paths]
 (* re-define P as abbreviations *)
 >> Q.PAT_X_ASSUM ‘P = permutator d’ (FULL_SIMP_TAC std_ss o wrap)
 >> qabbrev_tac ‘P = permutator d’
 >> qabbrev_tac ‘Y = X UNION RANK r’
 >> Cases_on ‘p = []’ >- fs []
 (* common properties of ‘p’ (this requires ‘p <> []’) *)
 >> ‘(!q. q <<= p ==> subterm X M q r <> NONE) /\
     (!q. q <<= FRONT p ==> solvable (subterm' X M q r))’
       by PROVE_TAC [subterm_solvable_lemma]
 >> qabbrev_tac ‘w = subterm_width M p’
 (* decompose ‘p’ and eliminate ‘p <> []’ *)
 >> Cases_on ‘p’ >> fs []
 (* cleanup assumptions *)
 >> Q.PAT_X_ASSUM ‘h = h'’ (fs o wrap o SYM) >> T_TAC
 (* preparing for eliminating ‘subterm' X M (h::q)’ *)
 >> Know ‘solvable M’
 >- (Q.PAT_X_ASSUM ‘!q. q <<= FRONT (h::t) ==> solvable _’
       (MP_TAC o (Q.SPEC ‘[]’)) >> rw [])
 >> DISCH_TAC
 >> Know ‘subterm X M (h::q) r <> NONE’
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw [])
 >> UNBETA_TAC [subterm_of_solvables] “subterm X M (h::q) r”
 >> STRIP_TAC
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M)’ by METIS_TAC [subterm_disjoint_lemma]
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs) (FV M0)’ K_TAC
 >> ‘Ms = args’ by rw [Abbr ‘Ms’, hnf_children_hnf]
 >> POP_ASSUM (rfs o wrap)
 >> qunabbrev_tac ‘Ms’
 >> ‘LENGTH args = m’ by rw [Abbr ‘m’]
 >> Know ‘m <= w’
 >- (MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::t’, ‘r’] subterm_width_first) \\
     rw [Abbr ‘w’])
 >> DISCH_TAC
 (* KEY: some shared subgoals needed at the end, before rewriting ‘[P/v] M’:

    2. subterm X (EL h args) t (SUC r) <> NONE
    3. subterm_width (EL h args) t <= d

    NOTE: the last subgoal requires deep properties of ‘subterm_width’. The
    involved tactics are not to be repeated in other parts of this lemma.
  *)
 >> Know ‘subterm X (EL h args) t (SUC r) <> NONE /\
          subterm_width (EL h args) t <= d’
 >- (CONJ_ASM1_TAC (* subterm X (EL h args) t (SUC r) <> NONE *)
     >- (Q.PAT_X_ASSUM ‘!q. q <<= h::t ==> subterm X M q r <> NONE’
           (MP_TAC o (Q.SPEC ‘h::t’)) \\
         simp [subterm_of_solvables] >> fs []) \\
     Q.PAT_X_ASSUM ‘w <= d’ MP_TAC \\
     qunabbrev_tac ‘w’ \\
     Suff ‘subterm_width M (h::t) <= d <=>
           m <= d /\ subterm_width (EL h args) t <= d’ >- rw [] \\
  (* applying subterm_width_induction_lemma' *)
     MATCH_MP_TAC subterm_width_induction_lemma' \\
     qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’, ‘vs’, ‘M1’] >> simp [])
 >> STRIP_TAC
 >> Know ‘~MEM v vs’
 >- (Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
     rw [Abbr ‘Y’, IN_UNION]
     >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) X’ MP_TAC \\
         rw [DISJOINT_ALT']) \\
     Suff ‘DISJOINT (RANK r) (set vs)’ >- rw [DISJOINT_ALT] \\
     qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC DISJOINT_RANK_RNEWS' >> art [])
 >> DISCH_TAC
 (* NOTE: ‘[P/v] M’ is solvable iff ‘[P/v] M0’ is solvable, the latter is either
    already a hnf (v <> y), or can be head-reduced to a hnf (v = y).
  *)
 >> Know ‘solvable ([P/v] M)’
 >- (MATCH_MP_TAC (cj 1 solvable_subst_permutator) \\
     qexistsl_tac [‘X’, ‘r’, ‘d’] >> simp [subterm_width_nil])
 >> DISCH_TAC
 (* Now we need to know the exact form of ‘principle_hnf ([P/v] M)’.

    We know that ‘principle_hnf M = M0 = LAMl vs (VAR y @* args)’, which means
    that ‘M -h->* LAMl vs (VAR y @* args)’. Meanwhile, as -h->* is substitutive,
    thus ‘[P/v] M -h->* [P/v] LAMl vs (VAR y @* args)’. Depending on the nature
    of ‘v’, the ending term ‘[P/v] LAMl vs (VAR y @* args)’ may or may not be
    a hnf. But it has indeed a hnf, since ‘solvable ([P/v] M)’ has been proved.

    Case 1 (MEM v vs): Case unprovable (but is eliminated by adding ‘v IN X’)
    Case 2 (v <> y):   [P/v] LAMl vs (VAR y @* args) = LAMl vs (VAR y @* args')
    Case 3 (v = y):    [P/v] LAMl vs (VAR y @* args) = LAMl vs (P @* args'),
        where LAMl vs (P @* args') -h->*
              LAMl vs (LAMl xs (LAM z (VAR z @* args' @* MAP VAR xs))) =
              LAMl (vs ++ xs ++ [z]) (VAR z @* args' @* MAP VAR xs), a hnf

    Only Case 3 needs further head-reductions, but the final hnf is already clear
    when proving ‘solvable ([P/v] M)’. Easy.

    In all these cases, ‘h < hnf_children_size (principle_hnf ([P/v] M))’ holds:
    In Case 1 & 2, ‘hnf_children_size (principle_hnf ([P/v] M)) = LENGTH args’.
    In Case 3, ‘hnf_children_size (principle_hnf ([P/v] M)) >= LENGTH args’.
  *)
 >> ‘M -h->* M0’ by METIS_TAC [principle_hnf_thm']
 (* NOTE: we will need to further do head reductions on ‘[P/v] M0’ *)
 >> Know ‘[P/v] M -h->* [P/v] M0’ >- PROVE_TAC [hreduce_substitutive]
 >> ‘DISJOINT (set vs) (FV P)’ by rw [DISJOINT_ALT', FV_permutator, Abbr ‘P’]
 >> simp [LAMl_SUB, appstar_SUB]
  >> qabbrev_tac ‘args' = MAP [P/v] args’
 >> ‘LENGTH args' = LENGTH args’ by rw [Abbr ‘args'’]
 (* LHS rewriting of args', this will introduce M0' = principle_hnf ([P/v] M)
    and a new set of abbreviations (vs', n', ...).
  *)
 >> CONV_TAC (UNBETA_CONV “subterm X ([P/v] M) (h::q) r”)
 >> qmatch_abbrev_tac ‘f _’
 >> ASM_SIMP_TAC std_ss [subterm_of_solvables]
 >> BasicProvers.LET_ELIM_TAC
 >> Q.PAT_X_ASSUM ‘subterm X (EL h args) q (SUC r) <> NONE’ MP_TAC
 >> simp [Abbr ‘f’, hnf_children_hnf]
 >> DISCH_TAC (* subterm X (EL h args) q (SUC r) <> NONE *)
 >> Q.PAT_X_ASSUM ‘m = m’ K_TAC
 (* Case 2 (easy: vs = vs' /\ m = m') *)
 >> reverse (Cases_on ‘y = v’)
 >- (simp [LAMl_SUB, appstar_SUB] \\
     DISCH_TAC (* [P/v] M -h->* LAMl vs (VAR y @* args') *) \\
    ‘FV P = {}’ by rw [Abbr ‘P’, FV_permutator] \\
    ‘hnf (LAMl vs (VAR y @* args'))’ by rw [hnf_appstar] \\
    ‘M0' = LAMl vs (VAR y @* args')’ by METIS_TAC [principle_hnf_thm'] \\
    ‘n = n'’ by rw [Abbr ‘n'’] \\
     POP_ASSUM (rfs o wrap o SYM) >> T_TAC \\
     qunabbrev_tac ‘n'’ \\
     Q.PAT_X_ASSUM ‘vs = vs'’ (rfs o wrap o SYM) \\
    ‘hnf (LAMl vs (VAR y @* args))’ by rw [hnf_appstar] \\
     fs [Abbr ‘M1'’, principle_hnf_beta_reduce] \\
     Q.PAT_X_ASSUM ‘args' = Ms’ (fs o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘m' = m’ (fs o wrap o SYM) \\
     fs [Abbr ‘m'’] >> T_TAC \\
  (* applying subterm_width_induction_lemma' *)
     Know ‘subterm_width ([P/v] M) (h::q) <= d <=>
           m <= d /\ subterm_width (EL h args') q <= d’
     >- (MATCH_MP_TAC subterm_width_induction_lemma' \\
         qexistsl_tac [‘X’, ‘r’, ‘M0'’, ‘n’, ‘vs’, ‘VAR y @* args'’] \\
         simp [principle_hnf_beta_reduce] \\
         CONJ_TAC
         >- (rw [FV_SUB] \\
             MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M’ >> art [] \\
             SET_TAC []) \\
         fs [Abbr ‘m’, Abbr ‘args'’] \\
      (* remaining goal: h::q IN ltree_paths (BT' X ([P/v] M) r) *)
         MATCH_MP_TAC subterm_imp_ltree_paths >> art [] \\
         CONJ_TAC
         >- (rw [FV_SUB] \\
             MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M’ >> art [] \\
             SET_TAC []) \\
         Q_TAC (UNBETA_TAC [subterm_of_solvables]) ‘subterm X ([P/v] M) (h::q) r’ \\
         simp [principle_hnf_beta_reduce, EL_MAP] \\
         qabbrev_tac ‘N = EL h args’ \\
         Q.PAT_X_ASSUM ‘!M p r. _’ (MP_TAC o Q.SPECL [‘N’, ‘t’, ‘SUC r’]) \\
         simp [] \\
         Know ‘v IN X UNION RANK (SUC r)’
         >- (Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
             Suff ‘Y SUBSET X UNION RANK (SUC r)’ >- rw [SUBSET_DEF] \\
             qunabbrev_tac ‘Y’ \\
             Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
             rw [RANK_MONO]) >> Rewr \\
         Suff ‘FV N SUBSET X UNION RANK (SUC r)’ >- rw [] \\
         qunabbrev_tac ‘N’ \\
         MATCH_MP_TAC subterm_induction_lemma' \\
         qexistsl_tac [‘M’, ‘principle_hnf M’, ‘LENGTH vs’, ‘LENGTH args’,
                       ‘vs’, ‘M1’] \\
         simp [LAMl_size_hnf, Abbr ‘M1’, principle_hnf_beta_reduce]) >> Rewr' \\
  (* now applying IH *)
     fs [Abbr ‘m’, Abbr ‘args'’, EL_MAP] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘t’ >> simp [] \\
  (* extra goals *)
     reverse CONJ_TAC
     >- (Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
         qunabbrev_tac ‘Y’ >> simp [] \\
         Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [RANK_MONO]) \\
     qunabbrev_tac ‘Y’ \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘LENGTH args’, ‘vs’, ‘M1’] \\
     simp [principle_hnf_beta_reduce, LAMl_size_hnf, Abbr ‘M1’])
 (* Case 3 (hard, vs <<= vs' *)
 >> Q.PAT_X_ASSUM ‘y = v’ (fs o wrap o SYM)
 >> simp [Abbr ‘P’]
 >> DISCH_TAC (* [permutator d/y] M -h->* ... *)
 (* applying hreduce_permutator_thm with a suitable excluded list

    NOTE: ‘vs'’ is to be proved extending vs (vs' = vs ++ ys), and we will need
          DISJOINT (set (SNOC z xs)) (set ys), thus here ‘set vs'’ is used.
  *)
 >> MP_TAC (Q.SPECL [‘set vs'’, ‘d’, ‘args'’] hreduce_permutator_thm)
 >> simp []
 >> STRIP_TAC (* this asserts new fresh lists to be renamed: ‘xs’ and ‘z’ *)
 >> rename1 ‘ALL_DISTINCT (SNOC z xs)’
 (* calculating head reductions of ‘[permutator d/y] M’ *)
 >> Know ‘[permutator d/y] M -h->*
          LAMl vs (LAMl xs (LAM z (VAR z @* args' @* MAP VAR xs)))’
 >- (MATCH_MP_TAC hreduce_TRANS \\
     Q.EXISTS_TAC ‘LAMl vs (permutator d @* args')’ >> rw [])
 >> DISCH_TAC
 >> ‘hnf (LAMl vs (LAMl xs (LAM z (VAR z @* args' @* MAP VAR xs))))’
       by rw [hnf_LAMl, hnf_appstar]
 >> ‘M0' = LAMl vs (LAMl xs (LAM z (VAR z @* args' @* MAP VAR xs)))’
       by METIS_TAC [principle_hnf_thm']
 >> qabbrev_tac ‘P = permutator d’
 >> Q.PAT_X_ASSUM ‘P @* args' -h->* _’                 K_TAC
 >> Q.PAT_X_ASSUM ‘[P/y] M -h->* LAMl vs (P @* args')’ K_TAC
 >> Know ‘LENGTH Ms = hnf_children_size M0'’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC hnf_children_size_alt \\
     qabbrev_tac ‘M' = [P/y] M’ \\
     qexistsl_tac [‘X’, ‘M'’, ‘r’, ‘n'’, ‘vs'’, ‘M1'’] >> simp [] \\
     qunabbrevl_tac [‘M'’, ‘Y’] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘FV M’ >> art [] \\
     MATCH_MP_TAC FV_SUB_SUBSET \\
     rw [Abbr ‘P’, closed_permutator])
 >> DISCH_THEN (ASSUME_TAC o SYM)
 (* NOTE: this proof includes ‘m <= m'’ *)
 >> Know ‘h < m'’
 >- (MATCH_MP_TAC LESS_LESS_EQ_TRANS \\
     Q.EXISTS_TAC ‘m’ >> art [] \\
  (* below is the proof of ‘m <= m'’ *)
     qunabbrevl_tac [‘m’, ‘m'’] \\
     POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [GSYM appstar_APPEND])
 >> Rewr
 >> Q.PAT_X_ASSUM ‘M0 = _’          (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = _’          (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M0' = LAMl vs _’ (ASSUME_TAC o SYM)
 (* stage work *)
 >> Know ‘n' = n + LENGTH xs + 1’
 >- (qunabbrevl_tac [‘n’, ‘n'’] \\
     Q.PAT_X_ASSUM ‘_ = M0’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = M0'’ (REWRITE_TAC o wrap o SYM) \\
    ‘!t. LAMl vs (LAMl xs (LAM z t)) = LAMl (vs ++ xs ++ [z]) t’
        by rw [LAMl_APPEND] >> POP_ORW \\
     Q.PAT_X_ASSUM ‘_ = M1’  (REWRITE_TAC o wrap o SYM) \\
     simp [LAMl_size_LAMl])
 >> DISCH_TAC
 >> qunabbrev_tac ‘vs'’
 >> Q_TAC (RNEWS_TAC (“vs' :string list”, “r :num”, “n' :num”)) ‘X’
 (* applying NEWS_prefix !!! *)
 >> Know ‘vs <<= vs'’
 >- (qunabbrevl_tac [‘vs’, ‘vs'’] \\
     MATCH_MP_TAC RNEWS_prefix >> rw [])
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [IS_PREFIX_APPEND]))
 >> rename1 ‘vs' = vs ++ ys’ (* l -> ys *)
 (* stage work *)
 >> gs [MAP_APPEND, appstar_APPEND, LIST_TO_SET_APPEND, ALL_DISTINCT_APPEND]
 (* applying hreduce_BETA_extended *)
 >> Know ‘M0' @* MAP VAR vs @* MAP VAR ys -h->*
          LAMl xs (LAM z (VAR z @* args' @* MAP VAR xs)) @* MAP VAR ys’
 >- (Q.PAT_X_ASSUM ‘_ = M0'’ (REWRITE_TAC o wrap o SYM) \\
     REWRITE_TAC [hreduce_BETA_extended])
 >> REWRITE_TAC [GSYM LAMl_SNOC]
 >> DISCH_TAC
 (* applying hreduce_LAMl_appstar *)
 >> qabbrev_tac ‘xs' = SNOC z xs’
 >> qabbrev_tac ‘t' = VAR z @* args' @* MAP VAR xs’
 >> Know ‘LAMl xs' t' @* MAP VAR ys -h->* fromPairs xs' (MAP VAR ys) ' t'’
 >- (MATCH_MP_TAC hreduce_LAMl_appstar >> simp [Abbr ‘xs'’] \\
     rw [EVERY_MEM, MEM_MAP] >> REWRITE_TAC [FV_thm] \\
     MATCH_MP_TAC DISJOINT_SUBSET' \\
     Q.EXISTS_TAC ‘set ys’ >> art [] \\
     rw [SUBSET_DEF])
 >> ‘FDOM (fromPairs xs' (MAP VAR ys)) = set xs'’
       by rw [FDOM_fromPairs, Abbr ‘xs'’]
 >> ASM_SIMP_TAC std_ss [Abbr ‘t'’, ssub_appstar, Abbr ‘xs'’]
 >> qabbrev_tac ‘fm = fromPairs (SNOC z xs) (MAP VAR ys)’
 >> Know ‘MAP ($' fm) args' = args'’
 >- (simp [LIST_EQ_REWRITE, EL_MAP] \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     MATCH_MP_TAC ssub_14b' >> art [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> simp [MEM_EL] \\
     Q.EXISTS_TAC ‘i’ >> art [])
 >> Rewr'
 >> Know ‘?z'. fm ' (VAR z) = VAR z'’
 >- (simp [Abbr ‘fm’] \\
     qabbrev_tac ‘ls = SNOC z xs’ \\
     Know ‘z = LAST ls’ >- rw [Abbr ‘ls’, LAST_SNOC] \\
    ‘ls <> []’ by rw [Abbr ‘ls’] \\
     simp [LAST_EL] >> DISCH_THEN K_TAC \\
     qabbrev_tac ‘i = PRE (LENGTH ls)’ \\
     Q.EXISTS_TAC ‘EL i ys’ \\
    ‘i < LENGTH ys’ by rw [Abbr ‘i’, Abbr ‘ls’] \\
    ‘VAR (EL i ys) :term = EL i (MAP VAR ys)’ by rw [EL_MAP] >> POP_ORW \\
     MATCH_MP_TAC fromPairs_FAPPLY_EL \\
     simp [Abbr ‘i’, Abbr ‘ls’])
 >> STRIP_TAC >> POP_ORW
 >> qabbrev_tac ‘ls = MAP ($' fm) (MAP VAR xs)’ (* irrelevant list *)
 >> DISCH_TAC
 >> Know ‘M0' @* MAP VAR vs @* MAP VAR ys -h->* VAR z' @* (args' ++ ls)’
 >- (REWRITE_TAC [appstar_APPEND] \\
     PROVE_TAC [hreduce_TRANS])
 >> Q.PAT_X_ASSUM ‘M0' @* MAP VAR vs @* MAP VAR ys -h->* _’ K_TAC
 >> Q.PAT_X_ASSUM ‘_ -h->* VAR z' @* args' @* ls’           K_TAC
 >> DISCH_TAC
 >> ‘hnf (VAR z' @* (args' ++ ls))’ by rw [hnf_appstar]
 >> ‘has_hnf (M0' @* MAP VAR vs @* MAP VAR ys)’ by PROVE_TAC [has_hnf_thm]
 (* finall we got the explicit form of M1' *)
 >> ‘M1' = VAR z' @* (args' ++ ls)’ by METIS_TAC [principle_hnf_thm]
 >> Q.PAT_X_ASSUM ‘M0' @* MAP VAR vs @* MAP VAR ys -h->* _’ K_TAC
 (* applying subterm_width_induction_lemma again *)
 >> Know ‘subterm_width ([P/y] M) (h::q) <= d <=>
          m' <= d /\ subterm_width (EL h Ms) q <= d’
 >- (MATCH_MP_TAC subterm_width_induction_lemma' \\
     qexistsl_tac [‘X’, ‘r’, ‘M0'’, ‘n'’, ‘vs'’, ‘M1'’] \\
     simp [appstar_APPEND] \\
     CONJ_ASM1_TAC
     >- (rw [FV_SUB] >- rw [Abbr ‘P’, FV_permutator] \\
         MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M’ >> art [] \\
         SET_TAC []) \\
     reverse CONJ_TAC (* h < m' *)
     >- (MATCH_MP_TAC LESS_LESS_EQ_TRANS \\
         Q.EXISTS_TAC ‘m’ >> art [] \\
         simp [Abbr ‘m'’, Abbr ‘Ms’, hnf_children_hnf]) \\
     MATCH_MP_TAC subterm_imp_ltree_paths >> simp [] \\
     simp [subterm_of_solvables, appstar_APPEND] \\
     simp [GSYM appstar_APPEND, hnf_children_hnf] \\
     Know ‘EL h (args' ++ ls) = EL h args'’
     >- (MATCH_MP_TAC EL_APPEND1 >> rw [Abbr ‘args'’]) >> Rewr' \\
     ASM_SIMP_TAC list_ss [Abbr ‘args'’, EL_MAP] \\
     Q.PAT_X_ASSUM ‘!M p r. _’ (MP_TAC o Q.SPECL [‘EL h args’, ‘t’, ‘SUC r’]) \\
     simp [] \\
     Know ‘y IN X UNION RANK (SUC r)’
     >- (Q.PAT_X_ASSUM ‘y IN Y’ MP_TAC \\
         Suff ‘Y SUBSET X UNION RANK (SUC r)’ >- rw [SUBSET_DEF] \\
         qunabbrev_tac ‘Y’ \\
         Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [RANK_MONO]) >> Rewr \\
     Suff ‘FV (EL h args) SUBSET X UNION RANK (SUC r)’ >- rw [] \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] \\
     simp [LAMl_size_hnf, principle_hnf_beta_reduce] \\
     Q.PAT_X_ASSUM ‘LAMl vs M1 = M0’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘VAR y @* args = M1’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [hnf_children_appstar])
 >> Rewr'
 >> Know ‘EL h Ms = EL h args'’
 >- (simp [Abbr ‘Ms’, hnf_children_hnf] \\
     MATCH_MP_TAC EL_APPEND1 >> art [])
 >> Rewr'
 >> Know ‘m' <= d’
 >- (Q.PAT_X_ASSUM ‘hnf_children_size M0' = m'’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = M0'’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [hnf_children_size_appstar, GSYM appstar_APPEND])
 >> Rewr
 >> Q.PAT_X_ASSUM ‘LENGTH args' = m’ K_TAC
 >> simp [Abbr ‘args'’, EL_MAP]
 >> qabbrev_tac ‘N = EL h args’
 (* applying IH, finally *)
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘q’ >> simp []
 >> CONJ_TAC (* FV N SUBSET X UNION RANK (SUC r) *)
 >- (qunabbrev_tac ‘N’ \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
     Q.PAT_X_ASSUM ‘LAMl vs M1 = M0’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘VAR y @* args = M1’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [])
 >> reverse CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘y IN Y’ MP_TAC \\
     rw [Abbr ‘Y’, IN_UNION]
     >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) X’ MP_TAC \\
         rw [DISJOINT_ALT']) \\
     DISJ2_TAC \\
     POP_ASSUM MP_TAC \\
     Suff ‘RANK r SUBSET RANK (SUC r)’ >- rw [SUBSET_DEF] \\
     simp [RANK_MONO])
 (* final goal: subterm_width N q <= d *)
 >> Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘w’ >> art []
 >> qunabbrevl_tac [‘N’, ‘w’]
 (* applying subterm_width_thm *)
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::t’, ‘r’] subterm_width_thm)
 >> simp [] >> DISCH_THEN K_TAC
 (* applying subterm_width_thm again *)
 >> MP_TAC (Q.SPECL [‘X’, ‘EL h args’, ‘q’, ‘SUC r’] subterm_width_thm)
 >> Know ‘FV (EL h args) SUBSET X UNION RANK (SUC r)’
 >- (MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
     Q.PAT_X_ASSUM ‘LAMl vs M1 = M0’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘VAR y @* args = M1’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [])
 >> DISCH_TAC
 >> ‘q IN ltree_paths (BT' X (EL h args) (SUC r))’
      by PROVE_TAC [subterm_imp_ltree_paths]
 >> simp [] >> DISCH_THEN K_TAC
 (* applying SUBSET_MAX_SET *)
 >> MATCH_MP_TAC SUBSET_MAX_SET
 >> CONJ_TAC (* FINITE _ *)
 >- (MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 >> CONJ_TAC (* FINITE _ *)
 >- (MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 >> rw [SUBSET_DEF] (* this asserts q' <<= q *)
 >> Know ‘q' <<= t’
 >- (MATCH_MP_TAC IS_PREFIX_TRANS \\
     Q.EXISTS_TAC ‘q’ >> art [])
 >> DISCH_TAC
 >> Q.EXISTS_TAC ‘h::q'’ >> simp []
 >> Know ‘subterm X M (h::q') r <> NONE’
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> simp [])
 >> DISCH_TAC
 >> Know ‘subterm X (EL h args) q' (SUC r) <> NONE’
 >- (Cases_on ‘q = []’ >- fs [] \\
     irule (cj 1 subterm_solvable_lemma) >> simp [] \\
     Q.EXISTS_TAC ‘q’ >> art [])
 >> DISCH_TAC
 >> simp []
 >> Q_TAC (UNBETA_TAC [subterm_of_solvables]) ‘subterm' X M (h::q') r’
 >> simp []
QED

(* This theorem can be repeatedly applied for ‘M ISUB ss’ *)
Theorem subterm_subst_permutator_cong :
    !p X M r y P d. FINITE X /\ FV M SUBSET X UNION RANK r /\
                    subterm X M p r <> NONE /\
                    P = permutator d /\ y IN X UNION RANK r /\
                    subterm_width M p <= d
                ==> subterm X ([P/y] M) p r <> NONE /\
                    subterm_width ([P/y] M) p <= d /\
                    subterm' X ([P/y] M) p r = [P/y] (subterm' X M p r)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> irule subterm_subst_permutator_cong_lemma >> art []
 >> Q.EXISTS_TAC ‘p’ >> rw []
QED

(* NOTE: This reduced version is suitable for MATCH_MP_TAC later. *)
Theorem subterm_subst_permutator_cong'[local] :
    !p X M r y P d. FINITE X /\ FV M SUBSET X UNION RANK r /\
                    subterm X M p r <> NONE /\
                    P = permutator d /\ y IN X UNION RANK r /\
                    subterm_width M p <= d
                ==> subterm X ([P/y] M) p r <> NONE /\
                    subterm' X ([P/y] M) p r = [P/y] (subterm' X M p r)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘M’, ‘r’, ‘y’, ‘P’, ‘d’]
                    subterm_subst_permutator_cong)
 >> rw []
QED

Theorem subterm_isub_permutator_cong :
    !ys p X M r P d ss.
        FINITE X /\ FV M SUBSET X UNION RANK r /\
        subterm X M p r <> NONE /\
        P = permutator d /\
        subterm_width M p <= d /\
        (!y. MEM y ys ==> y IN X UNION RANK r) /\
        ss = MAP (\y. (P,y)) ys
    ==> subterm X (M ISUB ss) p r <> NONE /\
        subterm_width (M ISUB ss) p <= d /\
        subterm' X (M ISUB ss) p r = (subterm' X M p r) ISUB ss
Proof
    Induct_on ‘ys’ >- rw []
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> POP_ORW
 >> simp []
 >> Q.PAT_X_ASSUM ‘P = permutator d’ K_TAC
 >> qabbrev_tac ‘P = permutator d’
 >> qabbrev_tac ‘N = [P/h] M’
 >> qabbrev_tac ‘ss = MAP (\y. (P,y)) ys’
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘M’, ‘r’, ‘h’, ‘P’, ‘d’]
                    subterm_subst_permutator_cong)
 >> simp []
 >> STRIP_TAC
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘P’ >> simp []
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘FV M’ >> art []
 >> rw [FV_SUB, Abbr ‘N’]
 >> rw [Abbr ‘P’, FV_permutator]
QED

Theorem subterm_isub_permutator_cong_alt :
    !X p r d y k ss M.
        FINITE X /\ FV M SUBSET X UNION RANK r /\
       (!i. i < k ==> y i IN X UNION RANK r) /\
        ss = GENLIST (\i. (permutator (d + i),y i)) k /\
        subterm X M p r <> NONE /\
        subterm_width M p <= d
    ==> subterm X (M ISUB ss) p r <> NONE /\
        subterm_width (M ISUB ss) p <= d + k /\
        subterm' X (M ISUB ss) p r = (subterm' X M p r) ISUB ss
Proof
    qx_genl_tac [‘X’, ‘p’, ‘r’, ‘d’, ‘y’]
 >> Induct_on ‘k’ >- rw []
 >> qx_genl_tac [‘ss'’, ‘M’]
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘ss' = _’ (REWRITE_TAC o wrap)
 >> SIMP_TAC std_ss [GENLIST, ISUB_SNOC]
 >> qabbrev_tac ‘P = \i. permutator (d + i)’ >> fs []
 >> qabbrev_tac ‘ss = GENLIST (\i. (P i,y i)) k’
 >> Q.PAT_X_ASSUM ‘!M'. FV M' SUBSET X UNION RANK r /\ _ ==> _’
      (MP_TAC o Q.SPEC ‘M’)
 >> simp []
 >> STRIP_TAC
 >> qabbrev_tac ‘N = M ISUB ss’
 >> qabbrev_tac ‘Q = P k’
 >> qabbrev_tac ‘v = y k’
 >> qabbrev_tac ‘w = d + k’
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘N’, ‘r’, ‘v’, ‘Q’, ‘w’]
                    subterm_subst_permutator_cong)
 >> simp [Abbr ‘Q’, Abbr ‘v’, Abbr ‘w’]
 >> impl_tac
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M’ >> art [] \\
     qunabbrev_tac ‘N’ \\
     MP_TAC (Q.SPECL [‘ss’, ‘M’] FV_ISUB_upperbound) \\
     Suff ‘FVS ss = {}’ >- simp [] \\
     simp [Abbr ‘ss’, FVS_ALT] \\
     Cases_on ‘k = 0’ >> simp [] \\
     DISJ2_TAC \\
     simp [MAP_GENLIST, LIST_TO_SET_GENLIST] \\
     simp [Abbr ‘P’, FV_permutator, o_DEF] \\
     simp [IMAGE_CONST])
 >> rw []
QED

Theorem subterm_isub_permutator_cong_alt' :
    !X p r d y k ss M.
        FINITE X /\ FV M SUBSET X UNION RANK r /\
       (!i. i < k ==> y i IN X UNION RANK r) /\
        ss = GENLIST (\i. (permutator (d + i),y i)) k /\
        subterm X M p r <> NONE /\
        subterm_width M p <= d
    ==> subterm X (M ISUB ss) p r <> NONE /\
        subterm' X (M ISUB ss) p r = (subterm' X M p r) ISUB ss
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘p’, ‘r’, ‘d’, ‘y’, ‘k’, ‘ss’, ‘M’]
                    subterm_isub_permutator_cong_alt)
 >> simp []
QED

(* This theorem is similar with subterm_subst_permutator_cong_lemma. P is
   replaced by a fresh variable. The proof should be similar and simpler.
 *)
Theorem subterm_fresh_subst_cong_lemma[local] :
    !X. FINITE X ==>
        !q M p r. q <<= p /\
                  FV M SUBSET X UNION RANK r /\
                  subterm X M p r <> NONE /\
                  v  IN X UNION RANK r /\
                  v' IN X UNION RANK r /\ v' # M
              ==> subterm X ([VAR v'/v] M) q r <> NONE /\
                  subterm' X ([VAR v'/v] M) q r = [VAR v'/v] (subterm' X M q r)
Proof
    NTAC 2 STRIP_TAC
 >> Induct_on ‘q’ >- rw []
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> ‘p IN ltree_paths (BT' X M r)’ by PROVE_TAC [subterm_imp_ltree_paths]
 >> qabbrev_tac ‘P = VAR v'’
 >> qabbrev_tac ‘Y = X UNION RANK r’
 >> Cases_on ‘p = []’ >- fs []
 (* common properties of ‘p’ (this requires ‘p <> []’) *)
 >> ‘(!q. q <<= p ==> subterm X M q r <> NONE) /\
     (!q. q <<= FRONT p ==> solvable (subterm' X M q r))’
       by PROVE_TAC [subterm_solvable_lemma]
 (* decompose ‘p’ and eliminate ‘p <> []’ *)
 >> Cases_on ‘p’ >> fs [] >> T_TAC
 (* cleanup assumptions *)
 >> Q.PAT_X_ASSUM ‘h = h'’ (fs o wrap o SYM)
 (* preparing for eliminating ‘subterm' X M (h::q)’ *)
 >> Know ‘solvable M’
 >- (Q.PAT_X_ASSUM ‘!q. q <<= FRONT (h::t) ==> solvable _’
       (MP_TAC o (Q.SPEC ‘[]’)) >> rw [])
 >> DISCH_TAC
 >> Know ‘subterm X M (h::q) r <> NONE’
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw [])
 >> UNBETA_TAC [subterm_of_solvables] “subterm X M (h::q) r”
 >> STRIP_TAC
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M)’ by METIS_TAC [subterm_disjoint_lemma]
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs) (FV M0)’ K_TAC
 >> ‘Ms = args’ by rw [Abbr ‘Ms’, hnf_children_hnf]
 >> POP_ASSUM (rfs o wrap)
 >> qunabbrev_tac ‘Ms’
 >> ‘LENGTH args = m’ by rw [Abbr ‘m’]
 >> Know ‘subterm X (EL h args) t (SUC r) <> NONE’
 >- (Q.PAT_X_ASSUM ‘!q. q <<= h::t ==> subterm X M q r <> NONE’
       (MP_TAC o (Q.SPEC ‘h::t’)) \\
     simp [subterm_of_solvables] >> fs [])
 >> DISCH_TAC
 >> Know ‘~MEM v vs’
 >- (Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
     rw [Abbr ‘Y’, IN_UNION]
     >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) X’ MP_TAC \\
         rw [DISJOINT_ALT']) \\
     Suff ‘DISJOINT (RANK r) (set vs)’ >- rw [DISJOINT_ALT] \\
     qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC DISJOINT_RANK_RNEWS' >> art [])
 >> DISCH_TAC
 >> ‘solvable ([P/v] M)’ by simp [Abbr ‘P’, GSYM fresh_tpm_subst]
 >> ‘M -h->* M0’ by METIS_TAC [principle_hnf_thm']
 (* NOTE: we will need to further do head reductions on ‘[P/v] M0’ *)
 >> Know ‘[P/v] M -h->* [P/v] M0’ >- PROVE_TAC [hreduce_substitutive]
 >> Know ‘DISJOINT (set vs) (FV P)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘X UNION RANK r’ \\
     reverse CONJ_TAC >- simp [Abbr ‘P’] \\
     simp [Abbr ‘vs’, DISJOINT_UNION', DISJOINT_RNEWS_RANK'])
 >> DISCH_TAC
 >> simp [LAMl_SUB, appstar_SUB]
 >> qabbrev_tac ‘args' = MAP [P/v] args’
 >> ‘LENGTH args' = LENGTH args’ by rw [Abbr ‘args'’]
 (* LHS rewriting of args', this will introduce M0' = principle_hnf ([P/v] M)
    and a new set of abbreviations (vs', n', ...).
  *)
 >> CONV_TAC (UNBETA_CONV “subterm X ([P/v] M) (h::q) r”)
 >> qmatch_abbrev_tac ‘f _’
 >> ASM_SIMP_TAC std_ss [subterm_of_solvables]
 >> BasicProvers.LET_ELIM_TAC
 >> Q.PAT_X_ASSUM ‘subterm X (EL h args) q (SUC r) <> NONE’ MP_TAC
 >> simp [Abbr ‘f’, hnf_children_hnf]
 >> DISCH_TAC (* subterm X (EL h args) q (SUC r) <> NONE *)
 >> Q.PAT_X_ASSUM ‘m = m’ K_TAC
 >> reverse (Cases_on ‘y = v’)
 >- (simp [LAMl_SUB, appstar_SUB] \\
     DISCH_TAC (* [P/v] M -h->* LAMl vs (VAR y @* args') *) \\
    ‘hnf (LAMl vs (VAR y @* args'))’ by rw [hnf_appstar] \\
    ‘M0' = LAMl vs (VAR y @* args')’ by METIS_TAC [principle_hnf_thm'] \\
    ‘n = n'’ by rw [Abbr ‘n'’] \\
     POP_ASSUM (rfs o wrap o SYM) >> T_TAC \\
     qunabbrev_tac ‘n'’ \\
     Q.PAT_X_ASSUM ‘vs = vs'’ (rfs o wrap o SYM) \\
    ‘hnf (LAMl vs (VAR y @* args))’ by rw [hnf_appstar] \\
     fs [Abbr ‘M1'’, principle_hnf_beta_reduce] \\
     Q.PAT_X_ASSUM ‘args' = Ms’ (fs o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘m' = m’ (fs o wrap o SYM) \\
     fs [Abbr ‘m'’] >> T_TAC \\
  (* now applying IH *)
     fs [Abbr ‘m’, Abbr ‘args'’, EL_MAP] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘t’ >> simp [] \\
  (* extra goals *)
     CONJ_TAC (* FV (EL h args) SUBSET ... *)
     >- (qunabbrev_tac ‘Y’ \\
         MATCH_MP_TAC subterm_induction_lemma' \\
         qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘LENGTH args’, ‘vs’, ‘M1’] \\
         simp [principle_hnf_beta_reduce, LAMl_size_hnf, Abbr ‘M1’]) \\
     CONJ_TAC (* v IN X UNION RANK (SUC r) *)
     >- (Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
         qunabbrev_tac ‘Y’ >> simp [] \\
         Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [RANK_MONO]) \\
     CONJ_TAC (* v' IN RANK (SUC r) *)
     >- (Q.PAT_X_ASSUM ‘v' IN Y’ MP_TAC \\
         qunabbrev_tac ‘Y’ \\
         Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [RANK_MONO]) \\
  (* last goal: v' # EL h args *)
     Know ‘FV (EL h args) SUBSET FV M UNION set vs’
     >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M0 UNION set vs’ \\
         reverse CONJ_TAC
         >- (Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
             qunabbrev_tac ‘M0’ \\
             MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) \\
         simp [Abbr ‘M1’] \\
         simp [FV_LAMl, FV_appstar] \\
         rw [SUBSET_DEF, IN_UNION] \\
         DISJ1_TAC >> DISJ2_TAC \\
         Q.EXISTS_TAC ‘FV (EL h args)’ >> art [] \\
         Q.EXISTS_TAC ‘EL h args’ >> simp [EL_MEM]) >> DISCH_TAC \\
     CCONTR_TAC \\
     fs [SUBSET_DEF, IN_UNION] \\
     Q.PAT_X_ASSUM ‘!x. x IN FV (EL h args) ==> _’ (MP_TAC o Q.SPEC ‘v'’) \\
     simp [] \\
     Q.PAT_X_ASSUM ‘v' IN Y’ MP_TAC \\
     rw [IN_UNION, Abbr ‘Y’]
     >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) X’ MP_TAC \\
         rw [DISJOINT_ALT']) \\
     Suff ‘DISJOINT (RANK r) (set vs)’ >- rw [DISJOINT_ALT] \\
     qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC DISJOINT_RANK_RNEWS >> simp [])
 (* stage work *)
 >> Q.PAT_X_ASSUM ‘y = v’ (fs o wrap)
 >> simp [Abbr ‘P’]
 >> Know ‘LAMl vs (VAR v' @* args') = [VAR v'/v] M0’
 >- simp [LAMl_SUB, appstar_SUB]
 >> Rewr'
 (* This coincides with hreduce_substitutive *)
 >> DISCH_TAC
 >> Know ‘M0' = [VAR v'/v] M0’
 >- (qunabbrev_tac ‘M0'’ \\
     Know ‘principle_hnf ([VAR v'/v] M) = [VAR v'/v] M0 <=>
           [VAR v'/v] M -h->* [VAR v'/v] M0 /\ hnf ([VAR v'/v] M0)’
     >- (MATCH_MP_TAC principle_hnf_thm' \\
         simp [GSYM fresh_tpm_subst']) >> Rewr' \\
     simp [LAMl_SUB, appstar_SUB, hnf_appstar])
 >> simp [LAMl_SUB, appstar_SUB]
 >> DISCH_THEN (ASSUME_TAC o SYM)
 >> ‘n' = n’ by rw [Abbr ‘n'’]
 >> POP_ASSUM (fs o wrap)
 >> qunabbrev_tac ‘n'’
 (* stage work *)
 >> fs [Abbr ‘vs'’]
 (* applying principle_hnf_beta_reduce *)
 >> Know ‘M1' = VAR v' @* args'’
 >- (qunabbrev_tac ‘M1'’ \\
     POP_ASSUM (REWRITE_TAC o wrap o SYM) \\
     simp [] \\
     MATCH_MP_TAC principle_hnf_beta_reduce \\
     simp [hnf_appstar])
 >> DISCH_THEN (ASSUME_TAC o SYM)
 >> ‘Ms = args'’ by rw [Abbr ‘Ms’]
 >> ‘m' = m’ by rw [Abbr ‘m'’]
 >> simp [Abbr ‘args'’, EL_MAP]
 (* applying IH *)
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘q’
 >> simp []
 >> CONJ_TAC (* FV (EL h args) SUBSET ... *)
 >- (qunabbrev_tac ‘Y’ \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] \\
     simp [])
 >> CONJ_TAC (* v IN X UNION RANK (SUC r) *)
 >- (Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
     qunabbrev_tac ‘Y’ >> simp [] \\
     Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
     rw [RANK_MONO])
 >> CONJ_TAC (* v' IN RANK (SUC r) *)
 >- (Q.PAT_X_ASSUM ‘v' IN Y’ MP_TAC \\
     qunabbrev_tac ‘Y’ \\
     Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
     rw [RANK_MONO])
 (* last goal: v' # EL h args *)
 >> Know ‘FV (EL h args) SUBSET FV M UNION set vs’
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M0 UNION set vs’ \\
     reverse CONJ_TAC
     >- (Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) \\
     simp [Abbr ‘M1’] \\
     simp [FV_LAMl, FV_appstar] \\
     rw [SUBSET_DEF, IN_UNION] \\
     DISJ1_TAC >> DISJ2_TAC \\
     Q.EXISTS_TAC ‘FV (EL h args)’ >> art [] \\
     Q.EXISTS_TAC ‘EL h args’ >> fs [EL_MEM])
 >> DISCH_TAC
 >> CCONTR_TAC
 >> fs [SUBSET_DEF, IN_UNION]
 >> Q.PAT_X_ASSUM ‘!x. x IN FV (EL h args) ==> _’ (MP_TAC o Q.SPEC ‘v'’)
 >> simp []
QED

Theorem subterm_fresh_subst_cong :
    !p X M r v v'. FINITE X /\ FV M SUBSET X UNION RANK r /\
                   subterm X M p r <> NONE /\
                   v  IN X UNION RANK r /\
                   v' IN X UNION RANK r /\ v' # M
               ==> subterm X ([VAR v'/v] M) p r <> NONE /\
                   subterm' X ([VAR v'/v] M) p r = [VAR v'/v] (subterm' X M p r)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> irule subterm_fresh_subst_cong_lemma >> art []
 >> Q.EXISTS_TAC ‘p’ >> rw []
QED

(* NOTE: ‘ltree_paths (BT' X M r) SUBSET ltree_paths (BT' X ([P/v] M) r)’ doesn't
         hold. Instead, we need to consider certain p and ‘d <= subterm_width M p’.
         This theorem holds even when M is not solvable.
 *)
Theorem subterm_width_subst_permutator_cong :
    !X P d v p M r.
         FINITE X /\ FV M SUBSET X UNION RANK r /\ v IN X UNION RANK r /\
         P = permutator d /\ subterm_width M p <= d /\
         p IN ltree_paths (BT' X M r) ==>
         p IN ltree_paths (BT' X ([P/v] M) r) /\
         subterm_width ([P/v] M) p <= d
Proof
    simp [ltree_paths_def]
 >> NTAC 4 GEN_TAC
 >> Induct_on ‘p’
 >- (rw [ltree_lookup] \\
     qabbrev_tac ‘P = permutator d’ \\
     MATCH_MP_TAC (cj 2 subterm_subst_permutator_cong) \\
     qexistsl_tac [‘X’, ‘r’] >> simp [])
 >> rpt GEN_TAC >> STRIP_TAC
 >> qabbrev_tac ‘P = permutator d’
 >> ‘h::p IN ltree_paths (BT' X M r)’ by rw [ltree_paths_def]
 >> Q.PAT_X_ASSUM ‘ltree_lookup (BT' X M r) (h::p) <> NONE’ MP_TAC
 >> qabbrev_tac ‘Y = X UNION RANK r’
 >> reverse (Cases_on ‘solvable M’)
 >- simp [BT_def, BT_generator_def, Once ltree_unfold, ltree_lookup_def]
 >> DISCH_TAC
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M)’ by METIS_TAC [subterm_disjoint_lemma]
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs) (FV M0)’ K_TAC
 >> Know ‘~MEM v vs’
 >- (Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
     rw [Abbr ‘Y’, IN_UNION]
     >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) X’ MP_TAC \\
         rw [DISJOINT_ALT']) \\
     Suff ‘DISJOINT (RANK r) (set vs)’ >- rw [DISJOINT_ALT] \\
     qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC DISJOINT_RANK_RNEWS' >> art [])
 >> DISCH_TAC
 >> Know ‘solvable ([P/v] M)’
 >- (MATCH_MP_TAC (cj 1 solvable_subst_permutator) \\
     qexistsl_tac [‘X’, ‘r’, ‘d’] >> simp [subterm_width_nil] \\
     MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::p’, ‘r’] subterm_width_first) \\
     simp [ltree_paths_def])
 >> DISCH_TAC
 >> ‘M -h->* M0’ by METIS_TAC [principle_hnf_thm']
 >> Know ‘[P/v] M -h->* [P/v] M0’ >- PROVE_TAC [hreduce_substitutive]
 >> ‘DISJOINT (set vs) (FV P)’ by rw [DISJOINT_ALT', FV_permutator, Abbr ‘P’]
 >> simp [LAMl_SUB, appstar_SUB]
 >> POP_ASSUM K_TAC (* DISJOINT (set vs) (FV P) *)
 >> qabbrev_tac ‘args' = MAP [P/v] args’
 >> qabbrev_tac ‘m = LENGTH args’
 >> ‘LENGTH args' = m’ by rw [Abbr ‘args'’, Abbr ‘m’]
 >> DISCH_TAC
 >> Know ‘!i. i < m ==> FV (EL i args') SUBSET FV (EL i args)’
 >- (rw [Abbr ‘m’, Abbr ‘args'’, EL_MAP] \\
     qabbrev_tac ‘N = EL i args’ \\
     simp [FV_SUB] \\
    ‘FV P = {}’ by rw [Abbr ‘P’, FV_permutator] \\
     simp [] \\
     Cases_on ‘v IN FV N’ >> SET_TAC [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘ltree_lookup (BT' X M r) (h::p) <> NONE’
      (MP_TAC o REWRITE_RULE [BT_def, BT_generator_def, ltree_unfold])
 >> simp [principle_hnf_beta_reduce, hnf_appstar, LMAP_fromList,
          ltree_lookup_def, LNTH_fromList]
 >> Cases_on ‘h < m’ >> simp [EL_MAP, GSYM BT_def]
 >> DISCH_TAC
 >> Know ‘subterm_width M (h::p) <= d <=>
          m <= d /\ subterm_width (EL h args) p <= d’
 >- (MATCH_MP_TAC subterm_width_induction_lemma' \\
     qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’, ‘vs’, ‘M1’] >> simp [])
 >> DISCH_THEN (rfs o wrap)
 >> qabbrev_tac ‘N = EL h args’
 (* stage work *)
 >> reverse (Cases_on ‘y = v’)
 >- (Q.PAT_X_ASSUM ‘[P/v] M -h->* _’ MP_TAC \\
     simp [] >> DISCH_TAC \\
     qabbrev_tac ‘M0' = LAMl vs (VAR y @* args')’ \\
    ‘hnf M0'’ by rw [hnf_appstar, Abbr ‘M0'’] \\
    ‘principle_hnf ([P/v] M) = M0'’ by METIS_TAC [principle_hnf_thm'] \\
     Q.PAT_X_ASSUM ‘hnf M0'’ K_TAC \\
     Q.PAT_X_ASSUM ‘M0 = LAMl vs (VAR y @* args)’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘M1 = VAR y @* args’ (ASSUME_TAC o SYM) \\
    ‘hnf_children M1 = args’ by rw [hnf_children_hnf] \\
    ‘LAMl_size M0' = n’ by rw [Abbr ‘M0'’, LAMl_size_hnf] \\
    ‘principle_hnf (M0' @* MAP VAR vs) = VAR y @* args'’
       by rw [Abbr ‘M0'’, principle_hnf_beta_reduce, hnf_appstar] \\
     STRONG_CONJ_TAC
     >- (simp [BT_def, BT_generator_def, Once ltree_unfold, ltree_lookup_def,
               LNTH_fromList, EL_MAP] \\
         simp [GSYM BT_def, EL_MAP, Abbr ‘args'’] \\
         FIRST_X_ASSUM (MATCH_MP_TAC o cj 1) >> art [] \\
         CONJ_TAC
         >- (qunabbrev_tac ‘N’ \\
             MATCH_MP_TAC subterm_induction_lemma' \\
             qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
             Q.PAT_X_ASSUM ‘_ = M0’ (REWRITE_TAC o wrap o SYM) \\
             simp []) \\
         Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
         qunabbrev_tac ‘Y’ \\
         Suff ‘X UNION RANK r SUBSET X UNION (RANK (SUC r))’
         >- METIS_TAC [SUBSET_DEF] \\
         Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [RANK_MONO]) >> DISCH_TAC \\
     Know ‘subterm_width ([P/v] M) (h::p) <= d <=>
           m <= d /\ subterm_width (EL h args') p <= d’
     >- (MATCH_MP_TAC subterm_width_induction_lemma' \\
         qexistsl_tac [‘X’, ‘r’, ‘M0'’, ‘n’, ‘vs’, ‘VAR y @* args'’] \\
         simp [principle_hnf_beta_reduce, ltree_paths_def] \\
         CONJ_TAC
         >- (rw [FV_SUB, Abbr ‘P’, FV_permutator] \\
             MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M’ >> art [] \\
             SET_TAC []) \\
         fs [Abbr ‘m’, Abbr ‘args'’, Abbr ‘M0'’]) >> Rewr' \\
     simp [Abbr ‘args'’, EL_MAP] \\
     FIRST_X_ASSUM (MATCH_MP_TAC o cj 2) >> art [] \\
     Q.EXISTS_TAC ‘SUC r’ >> art [] \\
     CONJ_TAC
     >- (qunabbrev_tac ‘N’ \\
         MATCH_MP_TAC subterm_induction_lemma' \\
         qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
         Q.PAT_X_ASSUM ‘_ = M0’ (REWRITE_TAC o wrap o SYM) \\
         simp []) \\
     Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
     qunabbrev_tac ‘Y’ \\
     Suff ‘X UNION RANK r SUBSET X UNION (RANK (SUC r))’
     >- METIS_TAC [SUBSET_DEF] \\
     Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
     rw [RANK_MONO])
 (* stage work *)
 >> POP_ASSUM (rfs o wrap o SYM) (* [P/y] from now on *)
 >> Q.PAT_X_ASSUM ‘[P/y] M -h->* _’ MP_TAC
 >> simp [Abbr ‘P’]
 >> DISCH_TAC (* [permutator d/v] M -h->* ... *)
 (* NOTE: New frash variables xs and y will be asserted here:

    P @* args' -h->* LAMl xs (LAM z (VAR z @* args' @* MAP VAR xs)),

    thus ‘principle_hnf ([P/y] M) = LAMl (vs ++ xs ++ [z]) (VAR z @* ...)’

    Here LENGTH xs = d - m. Let n' be the LAMl_size of the above hnf.
  *)
 >> qabbrev_tac ‘n' = n + (d - m) + 1’
 >> Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n' :num”)) ‘X’
 >> MP_TAC (Q.SPECL [‘set zs’, ‘d’, ‘args'’] hreduce_permutator_thm)
 >> impl_tac >- rpt (rw [])
 >> REWRITE_TAC [DISJOINT_UNION]
 >> STRIP_TAC
 >> rename1 ‘ALL_DISTINCT (SNOC z xs)’ (* y' -> z *)
 >> qabbrev_tac ‘P = permutator d’
 >> Know ‘LAMl vs (P @* args') -h->*
          LAMl vs (LAMl xs (LAM z (VAR z @* args' @* MAP VAR xs)))’
 >- (rw [hreduce_LAMl])
 >> qmatch_abbrev_tac ‘LAMl vs (P @* args') -h->* t ==> _’
 >> DISCH_TAC
 >> ‘hnf t’ by rw [Abbr ‘t’, hnf_appstar, hnf_LAMl]
 >> ‘[P/y] M -h->* t’ by PROVE_TAC [hreduce_TRANS]
 >> ‘principle_hnf ([P/y] M) = t’ by METIS_TAC [principle_hnf_thm']
 (* cleanup *)
 >> Q.PAT_X_ASSUM ‘P @* args' -h->* _’      K_TAC
 >> Q.PAT_X_ASSUM ‘LAMl vs _ -h->* t’       K_TAC
 >> Q.PAT_X_ASSUM ‘[P/y] M -h->* LAMl vs _’ K_TAC
 >> Q.PAT_X_ASSUM ‘[P/y] M -h->* t’         K_TAC
 >> Q.PAT_X_ASSUM ‘hnf t’                   K_TAC
 >> qunabbrev_tac ‘t’
 (* stage work *)
 >> POP_ASSUM MP_TAC
 >> ‘!t. LAMl vs (LAMl xs (LAM z t)) = LAMl (vs ++ (SNOC z xs)) t’
       by rw [LAMl_APPEND]
 >> POP_ORW
 >> REWRITE_TAC [GSYM appstar_APPEND]
 >> qabbrev_tac ‘args'' = args' ++ MAP VAR xs’
 >> ‘LENGTH args'' = d’ by rw [Abbr ‘args''’]
 >> qabbrev_tac ‘xs' = SNOC z xs’
 >> ‘LENGTH xs' = d - m + 1’ by rw [Abbr ‘xs'’]
 >> qabbrev_tac ‘vs' = vs ++ xs'’
 >> DISCH_TAC (* principle_hnf ([P/y] M) = ... *)
 >> Know ‘LENGTH vs' = n'’
 >- (qunabbrevl_tac [‘n’, ‘n'’, ‘vs'’, ‘xs'’] \\
     Q.PAT_X_ASSUM ‘M0 = _’  (REWRITE_TAC o wrap) \\
     simp [LAMl_size_LAMl])
 >> DISCH_TAC
  (* applying NEWS_prefix *)
 >> Know ‘vs <<= zs’
 >- (qunabbrevl_tac [‘vs’, ‘zs’] \\
     MATCH_MP_TAC RNEWS_prefix >> rw [Abbr ‘n'’])
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [IS_PREFIX_APPEND]))
 >> rename1 ‘zs = vs ++ ys'’ (* l -> ys' *)
 >> Know ‘LENGTH ys' = d - m + 1’
 >- (Know ‘LENGTH zs = LENGTH (vs ++ ys')’ >- POP_ASSUM (REWRITE_TAC o wrap) \\
     simp [Abbr ‘n'’])
 >> DISCH_TAC
 >> Know ‘!N. MEM N args' ==> DISJOINT (FV N) (set ys')’
 >- (Q.X_GEN_TAC ‘x’ \\
     simp [MEM_EL] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘i’ STRIP_ASSUME_TAC) \\
     POP_ORW \\
     MATCH_MP_TAC DISJOINT_SUBSET' \\
     Q.EXISTS_TAC ‘FV (EL i args)’ >> simp [] \\
  (* applying FV_subterm_lemma *)
     Know ‘FV (EL i args) SUBSET FV M UNION set vs’
     >- (MATCH_MP_TAC FV_subterm_lemma \\
         qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’, ‘m’, ‘M1’] >> simp []) \\
     DISCH_TAC \\
     MATCH_MP_TAC DISJOINT_SUBSET' \\
     Q.EXISTS_TAC ‘FV M UNION set vs’ >> art [] \\
     MATCH_MP_TAC DISJOINT_SUBSET' \\
     Q.EXISTS_TAC ‘X UNION RANK r UNION set vs’ \\
     reverse CONJ_TAC >- ASM_SET_TAC [] \\
     simp [DISJOINT_ALT'] \\
     rpt CONJ_TAC
     >- (NTAC 2 STRIP_TAC \\
         Q.PAT_X_ASSUM ‘DISJOINT (set zs) X’ MP_TAC \\
         rw [DISJOINT_ALT])
     >- (NTAC 2 STRIP_TAC \\
         MP_TAC (Q.SPECL [‘r’, ‘n'’, ‘X’] DISJOINT_RANK_RNEWS') \\
         rw [DISJOINT_ALT', IN_UNION]) \\
     Q.PAT_X_ASSUM ‘ALL_DISTINCT zs’ MP_TAC \\
     rw [ALL_DISTINCT_APPEND] >> METIS_TAC [])
 >> DISCH_TAC
 >> qabbrev_tac ‘t = VAR z @* args''’
 >> ‘hnf t’ by rw [Abbr ‘t’, hnf_appstar]
 >> qabbrev_tac ‘M0' = LAMl vs' t’
 >> ‘LAMl_size M0' = n'’ by rw [Abbr ‘M0'’, Abbr ‘t’]
 >> qabbrev_tac ‘M1' = principle_hnf (M0' @* MAP VAR zs)’
 >> Know ‘M1' = tpm (ZIP (xs',ys')) t’
 >- (simp [Abbr ‘M0'’, Abbr ‘M1'’, Abbr ‘vs'’, GSYM APPEND_ASSOC, appstar_APPEND,
           LAMl_APPEND] \\
     Know ‘principle_hnf (LAMl vs (LAMl xs' t) @* MAP VAR vs @* MAP VAR ys') =
           principle_hnf (LAMl xs' t @* MAP VAR ys')’
     >- (MATCH_MP_TAC principle_hnf_hreduce \\
         simp [hreduce_BETA_extended]) >> Rewr' \\
     MATCH_MP_TAC principle_hnf_tpm_reduce' >> art [] \\
     CONJ_TAC >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT zs’ MP_TAC \\
                  Q.PAT_X_ASSUM ‘zs = vs ++ ys'’ (ONCE_REWRITE_TAC o wrap) \\
                  simp [ALL_DISTINCT_APPEND]) \\
     CONJ_ASM1_TAC
     >- (ONCE_REWRITE_TAC [DISJOINT_SYM] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set zs’ >> art [] \\
         rw [LIST_TO_SET_APPEND]) \\
     simp [Abbr ‘t’, Abbr ‘args''’, FV_appstar] \\
     CONJ_TAC (* ~MEM z ys' *)
     >- (POP_ASSUM MP_TAC \\
         rw [DISJOINT_ALT, Abbr ‘xs'’]) \\
     reverse CONJ_TAC (* MAP VAR xs *)
     >- (Q.PAT_X_ASSUM ‘DISJOINT (set xs') (set ys')’ MP_TAC \\
         rw [Abbr ‘xs'’, DISJOINT_ALT]) \\
     Q.X_GEN_TAC ‘s’ >> simp [MEM_MAP] \\
     rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘s = FV x’ (REWRITE_TAC o wrap) \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘zs = vs ++ ys'’ (ASSUME_TAC o SYM)
 (* stage work *)
 >> STRONG_CONJ_TAC
 >- (simp [BT_def, BT_generator_def, Once ltree_unfold, ltree_lookup_def,
           LNTH_fromList, EL_MAP] \\
     REWRITE_TAC [GSYM BT_def] \\
     simp [hnf_children_tpm, EL_MAP] \\
     simp [Abbr ‘t’, hnf_children_hnf] \\
     Know ‘h < LENGTH args''’
     >- (Q_TAC (TRANS_TAC LESS_LESS_EQ_TRANS) ‘m’ >> art [] \\
         rw [Abbr ‘args''’]) >> Rewr \\
    ‘EL h args'' = EL h args'’ by rw [Abbr ‘args''’, EL_APPEND1] \\
     POP_ORW \\
     Know ‘tpm (ZIP (xs',ys')) (EL h args') = EL h args'’
     >- (MATCH_MP_TAC tpm_unchanged >> simp [MAP_ZIP] \\
         ONCE_REWRITE_TAC [DISJOINT_SYM] \\
         CONJ_TAC \\ (* 2 subgoals, same tactics *)
         FIRST_X_ASSUM MATCH_MP_TAC >> simp [EL_MEM]) >> Rewr' \\
     simp [Abbr ‘args'’, EL_MAP] \\
     FIRST_X_ASSUM (MATCH_MP_TAC o cj 1) >> art [] \\
     qunabbrev_tac ‘Y’ \\
     reverse CONJ_TAC
     >- (Q.PAT_X_ASSUM ‘y IN X UNION RANK r’ MP_TAC \\
         Suff ‘X UNION RANK r SUBSET X UNION RANK (SUC r)’
         >- (REWRITE_TAC [SUBSET_DEF] \\
             DISCH_THEN (REWRITE_TAC o wrap)) \\
         Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [RANK_MONO]) \\
     qunabbrev_tac ‘N’ \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [])
 >> DISCH_TAC
 (* extra goal for subterm_width *)
 >> qabbrev_tac ‘pi = ZIP (xs',ys')’
 >> Q.PAT_X_ASSUM ‘hnf t’ K_TAC
 >> rfs [Abbr ‘t’, tpm_appstar]
 >> qabbrev_tac ‘Ms = listpm term_pmact pi args''’
 >> Know ‘subterm_width ([P/y] M) (h::p) <= d <=>
          d <= d /\ subterm_width (EL h Ms) p <= d’
 >- (MATCH_MP_TAC subterm_width_induction_lemma' \\
     qexistsl_tac [‘X’, ‘r’, ‘M0'’, ‘n'’, ‘zs’, ‘M1'’] \\
     simp [principle_hnf_beta_reduce, ltree_paths_def] \\
     CONJ_TAC
     >- (rw [FV_SUB, Abbr ‘P’, FV_permutator] \\
         MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M’ >> art [] \\
         SET_TAC []) \\
     simp [Abbr ‘M0'’])
 >> Rewr'
 >> simp [Abbr ‘Ms’, EL_MAP]
 >> ‘EL h args'' = EL h args'’ by rw [Abbr ‘args''’, EL_APPEND1]
 >> POP_ORW
 >> qunabbrev_tac ‘pi’
 >> Know ‘tpm (ZIP (xs',ys')) (EL h args') = EL h args'’
 >- (MATCH_MP_TAC tpm_unchanged >> simp [MAP_ZIP] \\
     ONCE_REWRITE_TAC [DISJOINT_SYM] \\
     CONJ_TAC \\ (* 2 subgoals, same tactics *)
     FIRST_X_ASSUM MATCH_MP_TAC >> simp [EL_MEM])
 >> Rewr'
 >> simp [Abbr ‘args'’, EL_MAP]
 >> FIRST_X_ASSUM (MATCH_MP_TAC o cj 2) >> art []
 >> Q.EXISTS_TAC ‘SUC r’ >> art []
 >> CONJ_TAC
 >- (qunabbrev_tac ‘N’ \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [])
 >> Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC
 >> qunabbrev_tac ‘Y’
 >> Suff ‘X UNION RANK r SUBSET X UNION (RANK (SUC r))’
 >- METIS_TAC [SUBSET_DEF]
 >> Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC []
 >> rw [RANK_MONO]
QED

Theorem subterm_width_isub_permutator_cong :
    !ys p X M r P d ss.
        FINITE X /\ FV M SUBSET X UNION RANK r /\
        P = permutator d /\
       (!y. MEM y ys ==> y IN X UNION RANK r) /\
        ss = MAP (\y. (P,y)) ys /\
        p IN ltree_paths (BT' X M r) /\
        subterm_width M p <= d
    ==> p IN ltree_paths (BT' X (M ISUB ss) r) /\
        subterm_width (M ISUB ss) p <= d
Proof
    Induct_on ‘ys’ >- rw []
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘ss = _’ (REWRITE_TAC o wrap)
 >> simp []
 >> Q.PAT_X_ASSUM ‘P = permutator d’ K_TAC
 >> qabbrev_tac ‘P = permutator d’
 >> qabbrev_tac ‘N = [P/h] M’
 >> qabbrev_tac ‘ss = MAP (\y. (P,y)) ys’
 >> MP_TAC (Q.SPECL [‘X’, ‘P’, ‘d’, ‘h’, ‘p’, ‘M’, ‘r’]
                    subterm_width_subst_permutator_cong)
 >> simp []
 >> STRIP_TAC
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘P’ >> simp []
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M’ >> art []
 >> rw [FV_SUB, Abbr ‘N’]
 >> rw [Abbr ‘P’, FV_permutator]
QED

Theorem subterm_width_isub_permutator_cong_alt :
    !X p r d y k ss M.
        FINITE X /\ FV M SUBSET X UNION RANK r /\
       (!i. i < k ==> y i IN X UNION RANK r) /\
        ss = GENLIST (\i. (permutator (d + i),y i)) k /\
        p IN ltree_paths (BT' X M r) /\
        subterm_width M p <= d
    ==> p IN ltree_paths (BT' X (M ISUB ss) r) /\
        subterm_width (M ISUB ss) p <= d + k
Proof
    qx_genl_tac [‘X’, ‘p’, ‘r’, ‘d’, ‘y’]
 >> Induct_on ‘k’ >- rw []
 >> qx_genl_tac [‘ss'’, ‘M’]
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘ss' = _’ (REWRITE_TAC o wrap)
 >> SIMP_TAC std_ss [GENLIST, ISUB_SNOC]
 >> qabbrev_tac ‘P = \i. permutator (d + i)’ >> fs []
 >> qabbrev_tac ‘ss = GENLIST (\i. (P i,y i)) k’
 >> Q.PAT_X_ASSUM ‘!M'. FV M' SUBSET X UNION RANK r /\ _ ==> _’
      (MP_TAC o Q.SPEC ‘M’)
 >> simp []
 >> STRIP_TAC
 >> qabbrev_tac ‘N = M ISUB ss’
 >> qabbrev_tac ‘Q = P k’
 >> qabbrev_tac ‘v = y k’
 >> qabbrev_tac ‘w = d + k’
 >> MP_TAC (Q.SPECL [‘X’, ‘Q’, ‘w’, ‘v’, ‘p’, ‘N’, ‘r’]
                    subterm_width_subst_permutator_cong)
 >> simp [Abbr ‘Q’, Abbr ‘v’, Abbr ‘w’]
 >> impl_tac
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M’ >> art [] \\
     qunabbrev_tac ‘N’ \\
     MP_TAC (Q.SPECL [‘ss’, ‘M’] FV_ISUB_upperbound) \\
     Suff ‘FVS ss = {}’ >- simp [] \\
     simp [Abbr ‘ss’, FVS_ALT] \\
     Cases_on ‘k = 0’ >> simp [] \\
     DISJ2_TAC \\
     simp [MAP_GENLIST, LIST_TO_SET_GENLIST] \\
     simp [Abbr ‘P’, FV_permutator, o_DEF] \\
     simp [IMAGE_CONST])
 >> rw []
QED

(* This theorem is based on FV_subterm_lemma

   NOTE: If initially ‘FV M SUBSET X UNION RANK r’ and ‘v # M’ but
  ‘v IN RANK r’, each deeper subterm only adds FV from ROW r onwards,
   thus ‘v # subterm X M p r’ still holds.
 *)
Theorem FV_subterm_thm :
    !X v p M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
                subterm X M p r <> NONE /\
                v # M /\ v IN X UNION RANK r ==> v # (subterm' X M p r)
Proof
    NTAC 2 GEN_TAC
 >> Induct_on ‘p’ >- rw []
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> Know ‘(!q. q <<= h::p ==> subterm X M q r <> NONE) /\
          (!q. q <<= FRONT (h::p) ==> solvable (subterm' X M q r))’
 >- (MATCH_MP_TAC subterm_solvable_lemma >> simp [])
 >> STRIP_TAC
 >> Know ‘solvable M’
 >- (Q.PAT_X_ASSUM ‘!q. q <<= FRONT (h::p) ==> solvable _’
       (MP_TAC o (Q.SPEC ‘[]’)) >> rw [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘subterm X M (h::p) r <> NONE’ MP_TAC
 >> Q_TAC (UNBETA_TAC [subterm_alt]) ‘subterm X M (h::p) r’
 >> STRIP_TAC
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> CONJ_TAC
 >- (MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [])
 >> reverse CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘v IN X UNION RANK r’ MP_TAC \\
     Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
     rw [RANK_MONO])
 >> Know ‘LENGTH Ms = m’
 >- (simp [Once EQ_SYM_EQ, Abbr ‘m’] \\
     MATCH_MP_TAC hnf_children_size_alt \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘vs’, ‘M1’] >> simp [])
 >> DISCH_TAC
 (* applying FV_subterm_lemma *)
 >> Know ‘FV (EL h Ms) SUBSET FV M UNION set vs’
 >- (MATCH_MP_TAC FV_subterm_lemma \\
     qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’, ‘m’, ‘M1’] >> simp [])
 >> DISCH_TAC
 >> STRIP_TAC
 >> Know ‘v IN FV M UNION set vs’ >- METIS_TAC [SUBSET_DEF]
 >> rw [IN_UNION]
 >> Q.PAT_X_ASSUM ‘v IN X UNION RANK r’ MP_TAC
 >> rw [IN_UNION]
 >- (qunabbrev_tac ‘vs’ \\
     Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’ \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs) X’ MP_TAC \\
     rw [DISJOINT_ALT'])
 >> Suff ‘DISJOINT (RANK r) (set vs)’ >- rw [DISJOINT_ALT]
 >> qunabbrev_tac ‘vs’
 >> MATCH_MP_TAC DISJOINT_RANK_RNEWS >> simp []
QED

Theorem subterm_once_fresh_tpm_cong[local] :
    !p X M r v v'. FINITE X /\ FV M SUBSET X UNION RANK r /\
                   subterm X M p r <> NONE /\
                   v  IN X UNION RANK r /\
                   v' IN X UNION RANK r /\ v' # M
               ==> subterm X (tpm [(v,v')] M) p r <> NONE /\
                   subterm' X (tpm [(v,v')] M) p r = tpm [(v,v')] (subterm' X M p r)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Know ‘v' # subterm' X M p r’
 >- (MATCH_MP_TAC FV_subterm_thm >> art [])
 >> DISCH_TAC
 >> simp [fresh_tpm_subst']
 >> MATCH_MP_TAC subterm_fresh_subst_cong >> art []
QED

Theorem subterm_fresh_tpm_cong_lemma[local] :
    !pi X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
                 subterm X M p r <> NONE /\
                 set (MAP FST pi) SUBSET X UNION RANK r /\
                 set (MAP SND pi) SUBSET X UNION RANK r /\
                 ALL_DISTINCT (MAP FST pi) /\
                 ALL_DISTINCT (MAP SND pi) /\
                 DISJOINT (set (MAP FST pi)) (set (MAP SND pi)) /\
                 DISJOINT (set (MAP SND pi)) (FV M)
             ==> subterm X (tpm pi M) p r <> NONE /\
                 subterm' X (tpm pi M) p r = tpm pi (subterm' X M p r)
Proof
    Induct_on ‘pi’ >- rw []
 >> simp [FORALL_PROD]
 >> qx_genl_tac [‘u’, ‘v’]
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> ‘!t. tpm ((u,v)::pi) t = tpm [(u,v)] (tpm pi t)’ by rw [Once tpm_CONS]
 >> POP_ORW
 >> qabbrev_tac ‘N = tpm pi M’
 (* applying IH *)
 >> Q.PAT_X_ASSUM ‘!X M p r. P’ (MP_TAC o Q.SPECL [‘X’, ‘M’, ‘p’, ‘r’])
 >> simp []
 >> STRIP_TAC
 >> POP_ASSUM (REWRITE_TAC o wrap o SYM)
 >> MATCH_MP_TAC subterm_once_fresh_tpm_cong
 >> simp []
 >> qabbrev_tac ‘vs  = MAP FST pi’
 >> qabbrev_tac ‘vs' = MAP SND pi’
 >> ‘LENGTH vs' = LENGTH vs’ by rw [Abbr ‘vs’, Abbr ‘vs'’]
 >> CONJ_TAC
 >- (simp [Abbr ‘N’, SUBSET_DEF, FV_tpm] \\
     rpt STRIP_TAC \\
     qabbrev_tac ‘y = lswapstr (REVERSE pi) x’ \\
    ‘x = lswapstr pi y’ by rw [Abbr ‘y’] >> POP_ORW \\
     Know ‘pi = ZIP (vs,vs')’
     >- (simp [Abbr ‘vs’, Abbr ‘vs'’, LIST_EQ_REWRITE] \\
         rw [EL_ZIP, EL_MAP]) >> Rewr' \\
     Cases_on ‘MEM y vs’
     >- (Suff ‘lswapstr (ZIP (vs,vs')) y IN set vs'’ >- ASM_SET_TAC [] \\
         MATCH_MP_TAC MEM_lswapstr >> simp []) \\
     Cases_on ‘MEM y vs'’
     >- (Suff ‘lswapstr (ZIP (vs,vs')) y IN set vs’ >- ASM_SET_TAC [] \\
         MATCH_MP_TAC MEM_lswapstr' >> simp []) \\
     Suff ‘lswapstr (ZIP (vs,vs')) y = y’ >- ASM_SET_TAC [] \\
     MATCH_MP_TAC lswapstr_unchanged' \\
     simp [MAP_ZIP])
 >> simp [Abbr ‘N’]
 >> Suff ‘lswapstr (REVERSE pi) v = v’ >- rw []
 >> MATCH_MP_TAC lswapstr_unchanged'
 >> simp [MAP_REVERSE, MEM_REVERSE]
QED

Theorem subterm_fresh_tpm_cong :
    !pi X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
                 set (MAP FST pi) SUBSET X UNION RANK r /\
                 set (MAP SND pi) SUBSET X UNION RANK r /\
                 ALL_DISTINCT (MAP FST pi) /\
                 ALL_DISTINCT (MAP SND pi) /\
                 DISJOINT (set (MAP FST pi)) (set (MAP SND pi)) /\
                 DISJOINT (set (MAP SND pi)) (FV M)
            ==> (subterm X M p r = NONE <=> subterm X (tpm pi M) p r = NONE) /\
                (subterm X M p r <> NONE ==>
                 subterm' X (tpm pi M) p r = tpm pi (subterm' X M p r))
Proof
    reverse (rpt STRIP_TAC)
 >- (MATCH_MP_TAC (cj 2 subterm_fresh_tpm_cong_lemma) >> art [])
 >> reverse EQ_TAC
 >- (CCONTR_TAC >> fs [] \\
     Q.PAT_X_ASSUM ‘subterm X (tpm pi M) p r = NONE’ MP_TAC \\
     simp [] \\
     MATCH_MP_TAC (cj 1 subterm_fresh_tpm_cong_lemma) >> art [])
(* stage work *)
 >> CCONTR_TAC >> fs []
 >> qabbrev_tac ‘N = tpm pi M’
 >> Q.PAT_X_ASSUM ‘subterm X M p r = NONE’ MP_TAC
 >> ‘M = tpm (REVERSE pi) N’ by rw [Abbr ‘N’]
 >> simp []
 >> qabbrev_tac ‘xs = MAP FST pi’
 >> qabbrev_tac ‘ys = MAP SND pi’
 >> ‘LENGTH ys = LENGTH xs’ by rw [Abbr ‘xs’, Abbr ‘ys’]
 >> Know ‘pi = ZIP (xs,ys)’
 >- (rw [Abbr ‘xs’, Abbr ‘ys’, ZIP_MAP] \\
     rw [LIST_EQ_REWRITE, EL_MAP])
 >> DISCH_TAC
 >> simp [REVERSE_ZIP]
 >> qabbrev_tac ‘xs' = REVERSE xs’
 >> qabbrev_tac ‘ys' = REVERSE ys’
 >> ‘LENGTH ys' = LENGTH xs'’ by rw [Abbr ‘xs'’, Abbr ‘ys'’]
 (* applying pmact_flip_args_all *)
 >> ‘tpm (ZIP (xs',ys')) N = tpm (ZIP (ys',xs')) N’ by rw [pmact_flip_args_all]
 >> POP_ORW
 >> qabbrev_tac ‘pi' = ZIP (ys',xs')’
 >> MATCH_MP_TAC (cj 1 subterm_fresh_tpm_cong_lemma)
 >> simp [Abbr ‘pi'’, MAP_ZIP]
 (* applying FV_tpm_lemma *)
 >> CONJ_TAC
 >- (qunabbrev_tac ‘N’ \\
     MATCH_MP_TAC FV_tpm_lemma \\
     Q.EXISTS_TAC ‘r’ >> simp [MAP_ZIP] \\
     ASM_SET_TAC [])
 >> CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘set ys SUBSET X UNION RANK r’ MP_TAC \\
     rw [SUBSET_DEF, Abbr ‘ys'’])
 >> CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘set xs SUBSET X UNION RANK r’ MP_TAC \\
     rw [SUBSET_DEF, Abbr ‘xs'’])
 >> CONJ_TAC >- rw [ALL_DISTINCT_REVERSE, Abbr ‘ys'’]
 >> CONJ_TAC >- rw [ALL_DISTINCT_REVERSE, Abbr ‘xs'’]
 >> CONJ_TAC
 >- (rw [DISJOINT_ALT', Abbr ‘xs'’] \\
     Suff ‘DISJOINT (set xs) (set ys')’ >- rw [DISJOINT_ALT] \\
     rw [DISJOINT_ALT', Abbr ‘ys'’] \\
     Q.PAT_X_ASSUM ‘DISJOINT (set xs) (set ys)’ MP_TAC \\
     rw [DISJOINT_ALT'])
 (* stage work *)
 >> Suff ‘DISJOINT (set xs) (FV N)’
 >- rw [DISJOINT_ALT, Abbr ‘xs'’]
 >> POP_ASSUM K_TAC
 >> qunabbrevl_tac [‘xs'’, ‘ys'’]
 >> simp [Abbr ‘N’]
 >> POP_ASSUM K_TAC (* pi = ZIP (xs,ys) *)
 >> ONCE_REWRITE_TAC [DISJOINT_SYM]
 >> Know ‘tpm (ZIP (xs,ys)) M = M ISUB ZIP (MAP VAR ys,xs)’
 >- (MATCH_MP_TAC fresh_tpm_isub' >> art [])
 >> Rewr'
 >> MATCH_MP_TAC FV_renaming_disjoint >> art []
QED

(* Lemma 10.3.6 (ii) [1, p.247]:

   NOTE: The construction of ‘pi’ needs a fixed ltree path ‘p’, so that we can
   collect the maximum number of children in all nodes along ‘p’.  In another
   word, there exists no universal ‘pi’ for which the conclusion holds for
   arbitrary ‘p’.

   NOTE: Added ‘subterm X M p <> NONE’ to antecedents so that ‘subterm' X M p’
   is defined/specified. ‘subterm X (apply pi M) p <> NONE’ can be derived.

   NOTE: ‘p <> []’ must be added into antecedents, otherwise the statement
   becomes:

   [...] |- !X M. ?pi. Boehm_transform pi /\ is_ready (apply pi M) /\
                       ?fm. apply pi M == fm ' M

   which is impossible if M is not already "is_ready".

   NOTE: Added ‘p IN ltree_paths (BT X (apply pi M))’ into conclusions for the
   needs in the user theorem.

   NOTE: Extended the conclusion with ‘!q. q <<= p /\ q <> []’

   NOTE: ‘FV (apply pi M) SUBSET X UNION RANK (SUC r)’ is added into the
   conclusions for the needs of Boehm_out_lemma.
 *)
Theorem Boehm_transform_exists_lemma :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              p <> [] /\ subterm X M p r <> NONE ==>
       ?pi. Boehm_transform pi /\ is_ready' (apply pi M) /\
            FV (apply pi M) SUBSET X UNION RANK (SUC r) /\
            ?v P. closed P /\
              !q. q <<= p /\ q <> [] ==>
                  subterm X (apply pi M) q r <> NONE /\
                  subterm' X (apply pi M) q r = [P/v] (subterm' X M q r)
Proof
    rpt STRIP_TAC
 >> ‘p IN ltree_paths (BT' X M r)’ by PROVE_TAC [subterm_imp_ltree_paths]
 >> ‘(!q. q <<= p ==> subterm X M q r <> NONE) /\
      !q. q <<= FRONT p ==> solvable (subterm' X M q r)’
       by (MATCH_MP_TAC subterm_solvable_lemma >> art [])
 >> Know ‘solvable M’
 >- (POP_ASSUM (MP_TAC o Q.SPEC ‘[]’) >> rw [])
 >> DISCH_TAC
 (* M0 is now meaningful since M is solvable *)
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> ‘hnf M0’ by PROVE_TAC [hnf_principle_hnf']
 >> qabbrev_tac ‘n = LAMl_size M0’
 (* NOTE: here the excluded list must contain ‘FV M’. Just ‘FV M0’ doesn't
          work later, when calling the important [principle_hnf_denude_thm].
          This is conflicting with BT_generator_def and subterm_def.
  *)
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M)’ by METIS_TAC [subterm_disjoint_lemma]
 >> Know ‘?y args. M0 = LAMl (TAKE n vs) (VAR y @* args)’
 >- (qunabbrev_tac ‘n’ \\
    ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma'] \\
     irule (iffLR hnf_cases_shared) >> rw [] \\
     MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘FV M’ >> art [] \\
     qunabbrev_tac ‘M0’ >> MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> STRIP_TAC
 (* eliminate ‘TAKE n vs’ *)
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (REV_FULL_SIMP_TAC std_ss o wrap)
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> Know ‘M1 = VAR y @* args’
 >- (qunabbrev_tac ‘M1’ >> POP_ORW \\
     MATCH_MP_TAC principle_hnf_beta_reduce >> rw [hnf_appstar])
 >> DISCH_TAC
 >> qabbrev_tac ‘m = LENGTH args’
 (* using ‘subterm_width’ and applying subterm_width_thm *)
 >> qabbrev_tac ‘d = subterm_width M p’
 >> Know ‘m <= d’
 >- (MP_TAC (Q.SPECL [‘X’, ‘M’, ‘p’, ‘r’] subterm_width_first) \\
     rw [Abbr ‘d’])
 >> DISCH_TAC
 (* p1 is the first Boehm transformation for removing abstractions of M0 *)
 >> qabbrev_tac ‘p1 = MAP rightctxt (REVERSE (MAP VAR vs))’
 >> ‘Boehm_transform p1’ by rw [Abbr ‘p1’, MAP_MAP_o, GSYM MAP_REVERSE]
 >> ‘apply p1 M0 == M1’  by rw [Abbr ‘p1’, Boehm_apply_MAP_rightctxt']
 (* stage work (all correct until here)

    Now we define the permutator P (and then p2). This requires q + 1 fresh
    variables. The excluded list is at least X and FV M, and then ‘vs’.
    But since P is a closed term, these fresh variables seem irrelevant...
  *)
 >> qabbrev_tac ‘P = permutator d’
 >> ‘closed P’ by rw [Abbr ‘P’, closed_permutator]
 >> qabbrev_tac ‘p2 = [[P/y]]’
 >> ‘Boehm_transform p2’ by rw [Abbr ‘p2’]
 >> ‘apply p2 M1 = P @* MAP [P/y] args’ by rw [Abbr ‘p2’, appstar_SUB]
 >> qabbrev_tac ‘args' = MAP [P/y] args’
 >> Know ‘!i. i < m ==> FV (EL i args') SUBSET FV (EL i args)’
 >- (rw [Abbr ‘args'’, EL_MAP, FV_SUB] \\
     fs [closed_def])
 >> DISCH_TAC
 >> ‘LENGTH args' = m’ by rw [Abbr ‘args'’, Abbr ‘m’]
 (* NOTE: Z contains ‘vs’ in addition to X and FV M *)
 >> qabbrev_tac ‘Z = X UNION FV M UNION set vs’
 >> ‘FINITE Z’ by (rw [Abbr ‘Z’] >> rw [])
 >> Know ‘solvable (M0 @* MAP VAR vs)’
 >- (MATCH_MP_TAC solvable_appstar' \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’] >> simp [])
 >> DISCH_TAC
 >> Know ‘FV M1 SUBSET Z’
 >- (MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘FV M0 UNION set vs’ \\
     reverse CONJ_TAC
     >- (qunabbrev_tac ‘Z’ \\
         Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) \\
     ‘FV M0 UNION set vs = FV (M0 @* MAP VAR vs)’ by rw [FV_appstar_MAP_VAR] \\
      POP_ORW \\
      qunabbrev_tac ‘M1’ \\
      MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘z = SUC (string_width Z)’
 >> qabbrev_tac ‘l = alloc r z (z + d - m + 1)’
 >> Know ‘ALL_DISTINCT l /\ LENGTH l = d - m + 1’
 >- rw [Abbr ‘l’, alloc_thm]
 >> STRIP_TAC
 >> Know ‘DISJOINT (set l) Z’
 >- (rw [Abbr ‘l’, Abbr ‘z’, DISJOINT_ALT', alloc_def, MEM_MAP] \\
     ONCE_REWRITE_TAC [TAUT ‘~P \/ Q \/ ~R <=> P /\ R ==> Q’] \\
     STRIP_TAC \\
    ‘FINITE Z’ by rw [Abbr ‘Z’] \\
     MP_TAC (Q.SPECL [‘x’, ‘Z’] string_width_thm) >> rw [])
 >> DISCH_TAC
 (* now recover the old definition of Y *)
 >> Know ‘DISJOINT (set l) (FV M1)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘Z’ >> art [])
 >> ASM_REWRITE_TAC [FV_appstar, FV_thm]
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [DISJOINT_UNION']))
 >> Q.PAT_X_ASSUM ‘DISJOINT (set l) {y}’ (* ~MEM y l *)
       (STRIP_ASSUME_TAC o (SIMP_RULE (srw_ss()) [DISJOINT_ALT']))
 >> ‘l <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> qabbrev_tac ‘as = FRONT l’
 >> ‘LENGTH as = d - m’ by rw [Abbr ‘as’, LENGTH_FRONT]
 >> qabbrev_tac ‘b = LAST l’
 >> Know ‘l = SNOC b as’
 >- (ASM_SIMP_TAC std_ss [Abbr ‘as’, Abbr ‘b’, SNOC_LAST_FRONT])
 >> DISCH_TAC
 >> qabbrev_tac ‘p3 = MAP rightctxt (REVERSE (MAP VAR l))’
 >> ‘Boehm_transform p3’ by rw [Abbr ‘p3’, MAP_MAP_o, GSYM MAP_REVERSE]
 (* applying permutator_thm *)
 >> Know ‘apply p3 (P @* args') == VAR b @* args' @* MAP VAR as’
 >- (simp [Abbr ‘p3’, Abbr ‘P’, rightctxt_thm, MAP_SNOC,
           Boehm_apply_MAP_rightctxt'] \\
     REWRITE_TAC [GSYM appstar_APPEND, APPEND_ASSOC] \\
     MATCH_MP_TAC permutator_thm >> rw [])
 >> DISCH_TAC
 (* pre-final stage *)
 >> Q.EXISTS_TAC ‘p3 ++ p2 ++ p1’
 >> CONJ_ASM1_TAC
 >- (MATCH_MP_TAC Boehm_transform_APPEND >> art [] \\
     MATCH_MP_TAC Boehm_transform_APPEND >> art [])
 >> Know ‘apply (p3 ++ p2 ++ p1) M == VAR b @* args' @* MAP VAR as’
 >- (MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘apply (p3 ++ p2 ++ p1) M0’ \\
     CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong \\
                  CONJ_TAC >- art [] \\
                  qunabbrev_tac ‘M0’ \\
                  MATCH_MP_TAC lameq_SYM \\
                  MATCH_MP_TAC lameq_principle_hnf' >> art []) \\
     ONCE_REWRITE_TAC [Boehm_apply_APPEND] \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘apply (p3 ++ p2) M1’ \\
     CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> art [] \\
                  MATCH_MP_TAC Boehm_transform_APPEND >> art []) \\
     ONCE_REWRITE_TAC [Boehm_apply_APPEND] \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘apply p3 (P @* args')’ >> art [] \\
     MATCH_MP_TAC Boehm_apply_lameq_cong >> rw [])
 >> DISCH_TAC
 (* stage work *)
 >> Know ‘principle_hnf (apply (p3 ++ p2 ++ p1) M) = VAR b @* args' @* MAP VAR as’
 >- (Q.PAT_X_ASSUM ‘Boehm_transform (p3 ++ p2 ++ p1)’ K_TAC \\
     Q.PAT_X_ASSUM ‘Boehm_transform p1’               K_TAC \\
     Q.PAT_X_ASSUM ‘Boehm_transform p2’               K_TAC \\
     Q.PAT_X_ASSUM ‘Boehm_transform p3’               K_TAC \\
     Q.PAT_X_ASSUM ‘apply p1 M0 == M1’                K_TAC \\
     Q.PAT_X_ASSUM ‘apply p2 M1 = P @* args'’         K_TAC \\
     Q.PAT_X_ASSUM ‘apply p3 (P @* args') == _’       K_TAC \\
  (* preparing for principle_hnf_denude_thm *)
     Q.PAT_X_ASSUM ‘apply (p3 ++ p2 ++ p1) M == _’ MP_TAC \\
     simp [Boehm_apply_APPEND, Abbr ‘p1’, Abbr ‘p2’, Abbr ‘p3’,
           Boehm_apply_MAP_rightctxt'] \\
     Know ‘[P/y] (M @* MAP VAR vs) @* MAP VAR (SNOC b as) =
           [P/y] (M @* MAP VAR vs @* MAP VAR (SNOC b as))’
     >- (simp [appstar_SUB] \\
         Suff ‘MAP [P/y] (MAP VAR (SNOC b as)) = MAP VAR (SNOC b as)’ >- Rewr \\
         Q.PAT_X_ASSUM ‘l = SNOC b as’ (ONCE_REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘LENGTH l = d - m + 1’ K_TAC \\
         rw [LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC lemma14b \\
         REWRITE_TAC [FV_thm, IN_SING] \\
         Q.PAT_X_ASSUM ‘~MEM y l’ MP_TAC \\
         rw [MEM_EL] >> METIS_TAC []) >> Rewr' \\
     DISCH_TAC (* [P/y] ... == ... *) \\
  (* applying principle_hnf_permutator *)
     Know ‘VAR b @* args' @* MAP VAR as =
           principle_hnf ([P/y] (VAR y @* args @* MAP VAR (SNOC b as)))’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         simp [appstar_SUB, appstar_SNOC, MAP_SNOC] \\
         Know ‘MAP [P/y] (MAP VAR as) = MAP VAR as’
         >- (Q.PAT_X_ASSUM ‘LENGTH as = _’ K_TAC \\
             rw [LIST_EQ_REWRITE, EL_MAP] \\
             MATCH_MP_TAC lemma14b >> rw [] \\
             Q.PAT_X_ASSUM ‘~MEM y (SNOC b as)’ MP_TAC \\
             rw [MEM_EL] >> PROVE_TAC []) >> Rewr' \\
         Know ‘[P/y] (VAR b) = VAR b’
         >- (MATCH_MP_TAC lemma14b >> fs [MEM_SNOC, IN_UNION]) >> Rewr' \\
         simp [Abbr ‘P’, GSYM appstar_APPEND] \\
         MATCH_MP_TAC principle_hnf_permutator >> rw []) >> Rewr' \\
  (* applying principle_hnf_SUB_cong *)
     MATCH_MP_TAC principle_hnf_SUB_cong \\
     CONJ_TAC (* has_hnf #1 *)
     >- (simp [GSYM solvable_iff_has_hnf, GSYM appstar_APPEND] \\
        ‘M0 == M’ by rw [lameq_principle_hnf', Abbr ‘M0’] \\
        ‘M0 @* (MAP VAR vs ++ MAP VAR (SNOC b as)) ==
          M @* (MAP VAR vs ++ MAP VAR (SNOC b as))’ by rw [lameq_appstar_cong] \\
         Suff ‘solvable (M0 @* (MAP VAR vs ++ MAP VAR (SNOC b as)))’
         >- PROVE_TAC [lameq_solvable_cong] \\
         NTAC 2 (POP_ASSUM K_TAC) \\
         REWRITE_TAC [appstar_APPEND] \\
         qabbrev_tac ‘M0' = M0 @* MAP VAR vs’ \\
        ‘M0' == M1’ by rw [Abbr ‘M0'’] \\
        ‘M0' @* MAP VAR (SNOC b as) == M1 @* MAP VAR (SNOC b as)’
           by rw [lameq_appstar_cong] \\
         Suff ‘solvable (M1 @* MAP VAR (SNOC b as))’
         >- PROVE_TAC [lameq_solvable_cong] \\
         REWRITE_TAC [solvable_iff_has_hnf] \\
         MATCH_MP_TAC hnf_has_hnf >> rw [hnf_appstar]) \\
     CONJ_TAC (* has_hnf #2 *)
     >- (REWRITE_TAC [GSYM solvable_iff_has_hnf] \\
         Suff ‘solvable (VAR b @* args' @* MAP VAR as)’
         >- PROVE_TAC [lameq_solvable_cong] \\
         REWRITE_TAC [solvable_iff_has_hnf] \\
         MATCH_MP_TAC hnf_has_hnf >> rw [hnf_appstar]) \\
     CONJ_TAC (* has_hnf # 3 *)
     >- (simp [appstar_SUB, MAP_SNOC] \\
         Know ‘MAP [P/y] (MAP VAR as) = MAP VAR as’
         >- (Q.PAT_X_ASSUM ‘LENGTH as = _’ K_TAC \\
             rw [LIST_EQ_REWRITE, EL_MAP] \\
             MATCH_MP_TAC lemma14b >> rw [] \\
             Q.PAT_X_ASSUM ‘~MEM y (SNOC b as)’ MP_TAC \\
             rw [MEM_EL] >> PROVE_TAC []) >> Rewr' \\
         Know ‘[P/y] (VAR b) = VAR b’
         >- (MATCH_MP_TAC lemma14b >> fs [MEM_SNOC, IN_UNION]) >> Rewr' \\
         simp [Abbr ‘P’, GSYM appstar_APPEND] \\
         REWRITE_TAC [GSYM solvable_iff_has_hnf] \\
         Know ‘permutator d @* (args' ++ MAP VAR as) @@ VAR b ==
               VAR b @* (args' ++ MAP VAR as)’
         >- (MATCH_MP_TAC permutator_thm >> rw []) >> DISCH_TAC \\
         Suff ‘solvable (VAR b @* (args' ++ MAP VAR as))’
         >- PROVE_TAC [lameq_solvable_cong] \\
         REWRITE_TAC [solvable_iff_has_hnf] \\
         MATCH_MP_TAC hnf_has_hnf >> rw [hnf_appstar]) \\
  (* applying the celebrating principle_hnf_denude_thm

     NOTE: here ‘DISJOINT (set vs) (FV M)’ is required, and this means that
          ‘vs’ must exclude ‘FV M’ instead of just ‘FV M0’.
   *)
     MATCH_MP_TAC principle_hnf_denude_thm >> rw [])
 >> DISCH_TAC
 >> simp [is_ready'_def, GSYM CONJ_ASSOC]
 (* extra subgoal: solvable (apply (p3 ++ p2 ++ p1) M) *)
 >> ONCE_REWRITE_TAC [TAUT ‘P /\ Q /\ R <=> Q /\ P /\ R’]
 >> CONJ_ASM1_TAC
 >- (Suff ‘solvable (VAR b @* args' @* MAP VAR as)’
     >- PROVE_TAC [lameq_solvable_cong] \\
     REWRITE_TAC [solvable_iff_has_hnf] \\
     MATCH_MP_TAC hnf_has_hnf >> rw [hnf_appstar])
 (* applying is_ready_alt *)
 >> CONJ_TAC
 >- (simp [is_ready_alt] \\
     qexistsl_tac [‘b’, ‘args' ++ MAP VAR as’] \\
     CONJ_TAC
     >- (MP_TAC (Q.SPEC ‘VAR b @* args' @* MAP VAR as’
                   (MATCH_MP principle_hnf_thm'
                             (ASSUME “solvable (apply (p3 ++ p2 ++ p1) M)”))) \\
         simp [appstar_APPEND]) \\
     simp [] (* now two EVERY *) \\
     reverse CONJ_TAC
     >- (rw [EVERY_MEM, Abbr ‘b’, Abbr ‘as’, MEM_MAP] >> rw [FV_thm] \\
         Q.PAT_X_ASSUM ‘ALL_DISTINCT l’ MP_TAC \\
         Q.PAT_X_ASSUM ‘l = SNOC (LAST l) (FRONT l)’ (ONCE_REWRITE_TAC o wrap) \\
         rw [ALL_DISTINCT_SNOC] >> PROVE_TAC []) \\
     rw [EVERY_MEM, MEM_MAP] \\
     qabbrev_tac ‘Y = BIGUNION (IMAGE FV (set args))’ \\
     rfs [LIST_TO_SET_SNOC] \\
     Suff ‘FV e SUBSET Y’ >- METIS_TAC [SUBSET_DEF] \\
     qunabbrev_tac ‘Y’ \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘BIGUNION (IMAGE FV (set args'))’ \\
     reverse CONJ_TAC
     >- (rw [SUBSET_DEF, IN_BIGUNION_IMAGE, MEM_EL] \\
         Q.EXISTS_TAC ‘EL n args’ \\
         CONJ_TAC >- (Q.EXISTS_TAC ‘n’ >> art []) \\
         POP_ASSUM MP_TAC \\
         Suff ‘FV (EL n args') SUBSET FV (EL n args)’ >- METIS_TAC [SUBSET_DEF] \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     rw [SUBSET_DEF, IN_BIGUNION_IMAGE] \\
     Q.EXISTS_TAC ‘e’ >> art [])
 (* extra goal *)
 >> CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘apply (p3 ++ p2 ++ p1) M == _’ K_TAC \\
     Q.PAT_X_ASSUM ‘principle_hnf (apply (p3 ++ p2 ++ p1) M) = _’ K_TAC \\
     Q.PAT_X_ASSUM ‘apply p3 (P @* args') == _’ K_TAC \\
     rpt (Q.PAT_X_ASSUM ‘Boehm_transform _’ K_TAC) \\
     Q.PAT_X_ASSUM ‘solvable (apply (p3 ++ p2 ++ p1) M)’ K_TAC \\
     simp [Boehm_apply_APPEND, Abbr ‘p1’, Abbr ‘p2’, Abbr ‘p3’,
           Boehm_apply_MAP_rightctxt'] \\
     POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
     reverse CONJ_TAC
     >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW r’ \\
         rw [Abbr ‘l’, alloc_SUBSET_ROW] \\
         Suff ‘ROW r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [ROW_SUBSET_RANK]) \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘FV (M @* MAP VAR vs)’ \\
     CONJ_TAC >- (MATCH_MP_TAC FV_SUB_SUBSET >> art []) \\
     simp [FV_appstar] \\
     reverse CONJ_TAC
     >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW r’ \\
         rw [Abbr ‘vs’, RNEWS_SUBSET_ROW] \\
         Suff ‘ROW r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [ROW_SUBSET_RANK]) \\
     Q_TAC (TRANS_TAC SUBSET_TRANS) ‘X UNION RANK r’ >> art [] \\
     Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
     rw [RANK_MONO])
 (* stage work, there's the textbook choice of y and P *)
 >> qabbrev_tac ‘pi = p3 ++ p2 ++ p1’
 >> qexistsl_tac [‘y’, ‘P’] >> art []
 >> NTAC 2 STRIP_TAC (* push ‘q <<= p’ to assumptions *)
 (* RHS rewriting from M to M0 *)
 >> Know ‘subterm X M0 q r = subterm X M q r’
 >- (qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC subterm_of_principle_hnf >> art [])
 >> DISCH_THEN (ONCE_REWRITE_TAC o wrap o SYM)
 (* LHS rewriting from M to M0 *)
 >> Know ‘subterm X (apply pi M) q r =
          subterm X (VAR b @* args' @* MAP VAR as) q r’
 >- (Q.PAT_X_ASSUM ‘_ = VAR b @* args' @* MAP VAR as’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     qabbrev_tac ‘t = apply pi M’ \\
     ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC subterm_of_principle_hnf >> art [])
 >> Rewr'
 (* stage cleanups *)
 >> Q.PAT_X_ASSUM ‘solvable (apply pi M)’          K_TAC
 >> Q.PAT_X_ASSUM ‘principle_hnf (apply pi M) = _’ K_TAC
 >> Q.PAT_X_ASSUM ‘apply pi M == _’                K_TAC
 >> Q.PAT_X_ASSUM ‘Boehm_transform pi’             K_TAC
 (* stage work, now ‘M’ is eliminated from both sides! *)
 >> Cases_on ‘q’ >- FULL_SIMP_TAC std_ss [] (* this asserts q = h::t *)
 >> Know ‘h < m’
 >- (Cases_on ‘p’ >> fs [] \\
     Q.PAT_X_ASSUM ‘h = h'’ (fs o wrap o SYM) \\
     Know ‘subterm X M (h::t) r <> NONE’
     >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw []) \\
     CONV_TAC (UNBETA_CONV “subterm X M (h::t) r”) \\
     qmatch_abbrev_tac ‘f _’ \\
     RW_TAC bool_ss [subterm_of_solvables] \\
     simp [Abbr ‘f’])
 >> DISCH_TAC
 (* applying subterm_of_absfree_hnf *)
 >> MP_TAC (Q.SPECL [‘X’, ‘VAR b @* args' @* MAP VAR as’, ‘h’, ‘t’, ‘r’]
                    subterm_of_absfree_hnf)
 >> simp [hnf_appstar, GSYM appstar_APPEND, hnf_children_appstar]
 >> DISCH_THEN K_TAC (* already used *)
 (* eliminating ‘MAP VAR as’ *)
 >> Know ‘EL h (args' ++ MAP VAR as) = EL h args'’
 >- (MATCH_MP_TAC EL_APPEND1 >> rw [])
 >> Rewr'
 (* eliminating ‘vs’

    NOTE: ‘subterm Y’ changed to ‘subterm Z’ at next level. There's no
    flexibility here on the choice of excluded variabes.
  *)
 >> Know ‘subterm X (LAMl vs (VAR y @* args)) (h::t) r =
          subterm X (EL h args) t (SUC r)’
 >- (MP_TAC (Q.SPECL [‘X’, ‘LAMl vs (VAR y @* args)’, ‘h’, ‘t’, ‘r’]
                     subterm_of_hnf) \\
     simp [hnf_LAMl, hnf_appstar] \\
     DISCH_THEN K_TAC (* already used *) \\
     Q.PAT_X_ASSUM ‘M0 = LAMl vs (VAR y @* args)’ (REWRITE_TAC o wrap o SYM) \\
     simp [hnf_children_hnf])
 >> Rewr'
 (* Now: subterm' Z (EL h args') t == [P/y] (subterm' Z (EL h args) t)

    First of all, those assumptions about p1,p2,p3 are no more needed.
  *)
 >> qunabbrev_tac ‘pi’
 >> Q.PAT_X_ASSUM ‘Boehm_transform p1’             K_TAC
 >> Q.PAT_X_ASSUM ‘apply p1 M0 == M1’              K_TAC
 >> qunabbrev_tac ‘p1’
 >> Q.PAT_X_ASSUM ‘Boehm_transform p2’             K_TAC
 >> Q.PAT_X_ASSUM ‘apply p2 M1 = P @* args'’       K_TAC
 >> qunabbrev_tac ‘p2’
 >> Q.PAT_X_ASSUM ‘Boehm_transform p3’             K_TAC
 >> Q.PAT_X_ASSUM ‘apply p3 (P @* args') == _’     K_TAC
 >> qunabbrev_tac ‘p3’
 >> Q.PAT_X_ASSUM ‘h::t <> []’                     K_TAC
 >> qabbrev_tac ‘N  = EL h args’
 >> qabbrev_tac ‘N' = EL h args'’
 (* eliminating N' *)
 >> ‘N' = [P/y] N’ by simp [EL_MAP, Abbr ‘m’, Abbr ‘N’, Abbr ‘N'’, Abbr ‘args'’]
 >> POP_ORW
 >> qunabbrev_tac ‘N'’
 (* cleanup args' *)
 >> Q.PAT_X_ASSUM
      ‘!i. i < m ==>
           FV (EL i args') SUBSET FV (EL i args)’  K_TAC
 >> Q.PAT_X_ASSUM ‘LENGTH args' = m’               K_TAC
 >> qunabbrev_tac ‘args'’
 (* cleanup l, as and b *)
 >> Q.PAT_X_ASSUM ‘ALL_DISTINCT l’                 K_TAC
 >> NTAC 2 (Q.PAT_X_ASSUM ‘DISJOINT (set l) _’     K_TAC)
 >> Q.PAT_X_ASSUM ‘LENGTH l = q - m + 1’           K_TAC
 >> Q.PAT_X_ASSUM ‘l <> []’                        K_TAC
 >> Q.PAT_X_ASSUM ‘l = SNOC b as’                  K_TAC
 >> Q.PAT_X_ASSUM ‘~MEM y l’                       K_TAC
 >> Q.PAT_X_ASSUM ‘LENGTH as = q - m’              K_TAC
 >> qunabbrevl_tac [‘l’, ‘as’, ‘b’]
 (* applying subterm_headvar_lemma *)
 >> Know ‘hnf_headvar M1 IN X UNION RANK (SUC r)’
 >- (MATCH_MP_TAC subterm_headvar_lemma \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘vs’] >> simp [])
 >> ASM_SIMP_TAC std_ss [hnf_head_hnf, THE_VAR_thm]
 >> DISCH_TAC (* y IN X UNION RANK (SUC r) *)
 (* applying subterm_subst_permutator_cong *)
 >> MATCH_MP_TAC subterm_subst_permutator_cong'
 >> Q.EXISTS_TAC ‘d’
 >> simp [Abbr ‘P’]
 >> CONJ_TAC
 >- (qunabbrev_tac ‘N’ >> MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [])
 (* stage work *)
 >> CONJ_ASM1_TAC (* subterm Z N t <> NONE *)
 >- (Q.PAT_X_ASSUM ‘!q. q <<= p ==> subterm X M q r <> NONE’
       (MP_TAC o Q.SPEC ‘h::t’) \\
     Q.PAT_X_ASSUM ‘M0 = _’ K_TAC \\
     simp [subterm_of_solvables])
 (* final goal: subterm_width (EL h args) t <= d *)
 >> qunabbrev_tac ‘d’
 (* applying subterm_width_thm *)
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘p’, ‘r’] subterm_width_thm)
 >> simp [] >> DISCH_THEN K_TAC
 (* applying subterm_width_thm again *)
 >> MP_TAC (Q.SPECL [‘X’, ‘N’, ‘t’, ‘SUC r’] subterm_width_thm)
 >> Know ‘FV N SUBSET X UNION RANK (SUC r)’
 >- (qunabbrev_tac ‘N’ \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [])
 >> DISCH_TAC
 >> ‘t IN ltree_paths (BT' X N (SUC r))’
       by PROVE_TAC [subterm_imp_ltree_paths]
 >> simp [] >> DISCH_THEN K_TAC
 (* applying SUBSET_MAX_SET *)
 >> MATCH_MP_TAC SUBSET_MAX_SET
 >> CONJ_TAC
 >- (MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 >> CONJ_TAC
 >- (MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 (* final goal *)
 >> ‘hnf_children_size M0 = m’ by rw [Abbr ‘m’]
 >> Q.PAT_X_ASSUM ‘M0 = _’ K_TAC
 >> rw [SUBSET_DEF] (* this asserts q <<= t *)
 >> Know ‘h::q <<= p’
 >- (MATCH_MP_TAC IS_PREFIX_TRANS \\
     Q.EXISTS_TAC ‘h::t’ >> simp [])
 >> DISCH_TAC
 >> Q.EXISTS_TAC ‘h::q’ >> simp []
 >> Know ‘subterm X M (h::q) r <> NONE’
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> simp [])
 >> Know ‘subterm X N q (SUC r) <> NONE’
 >- (Cases_on ‘t = []’ >- fs [] \\
     irule (cj 1 subterm_solvable_lemma) >> simp [] \\
     Q.EXISTS_TAC ‘t’ >> art [])
 >> DISCH_TAC
 >> Q_TAC (UNBETA_TAC [subterm_of_solvables]) ‘subterm' X M (h::q) r’
 >> simp []
QED

(* Proposition 10.3.7 (i) [1, p.248] (Boehm out lemma)

   NOTE: This time the case ‘p = []’ can be included, but it's a trvial case.

   NOTE: The original lemma in textbook requires ‘p IN ltree_paths (BT X M)’,
   but this seems wrong, as ‘subterm X M p’ may not be defined if only ‘p’ is
   valid path (i.e. the subterm could be a bottom (\bot) as the result of un-
   solvable terms).

   NOTE: Can we enhance this lemma by using ‘-h->*’ instead of ‘==’?

   NOTE: Use subterm_imp_ltree_paths to prove ‘p IN ltree_paths (BT X M)’.
 *)
Theorem Boehm_out_lemma :
    !X p M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              subterm X M p r <> NONE ==>
              ?pi. Boehm_transform pi /\
                   ?ss. apply pi M == subterm' X M p r ISUB ss
Proof
    Q.X_GEN_TAC ‘X’
 >> Induct_on ‘p’
 >- (rw [] \\
     Q.EXISTS_TAC ‘[]’ >> rw [] \\
     Q.EXISTS_TAC ‘[]’ >> rw [])
 >> rpt STRIP_TAC
 >> rename1 ‘subterm X M (h::t) r <> NONE’
 >> qabbrev_tac ‘p = h::t’ (* head and tail *)
 >> ‘p <> []’ by rw [Abbr ‘p’]
 >> ‘(!q. q <<= p ==> subterm X M q r <> NONE) /\
      !q. q <<= FRONT p ==> solvable (subterm' X M q r)’
         by METIS_TAC [subterm_solvable_lemma]
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::t’, ‘r’] Boehm_transform_exists_lemma)
 >> simp []
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘p0’ MP_TAC)
 >> RW_TAC std_ss [] (* push p0 properties to assumptions *)
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘p’)) (* put q = p *)
 >> rw []
 >> qabbrev_tac ‘M' = apply p0 M’
 >> ‘solvable M' /\ ?y Ms. M' -h->* VAR y @* Ms /\ EVERY (\e. y # e) Ms’
       by METIS_TAC [is_ready_alt']
 >> ‘principle_hnf M' = VAR y @* Ms’ by rw [principle_hnf_thm', hnf_appstar]
 (* stage work *)
 >> qunabbrev_tac ‘p’
 >> Know ‘h < LENGTH Ms’
 >- (Q.PAT_X_ASSUM ‘subterm X M' (h::t) r <> NONE’ MP_TAC \\
     RW_TAC std_ss [subterm_of_solvables] >> fs [])
 >> DISCH_TAC
 >> qabbrev_tac ‘m = LENGTH Ms’
 >> qabbrev_tac ‘N = EL h Ms’
 (* stage work *)
 >> Know ‘subterm X N t (SUC r) <> NONE /\
          subterm' X M' (h::t) r = subterm' X N t (SUC r)’
 >- (Q.PAT_X_ASSUM ‘subterm' X M' (h::t) r =
                    [P/v] (subterm' X M (h::t) r)’ K_TAC \\
     Q.PAT_X_ASSUM ‘subterm X M' (h::t) r <> NONE’ MP_TAC \\
     rw [subterm_of_solvables, Abbr ‘N’])
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘subterm' X M' (h::t) r = subterm' X N t (SUC r)’ (fs o wrap)
 >> T_TAC
 (* stage work, now define a selector *)
 >> qabbrev_tac ‘U = selector h m’
 >> qabbrev_tac ‘p1 = [[U/y]]’
 >> ‘Boehm_transform p1’ by rw [Abbr ‘p1’]
 >> qabbrev_tac ‘p10 = p1 ++ p0’
 >> ‘Boehm_transform p10’ by rw [Abbr ‘p10’, Boehm_transform_APPEND]
 (* applying properties of selector (U) *)
 >> Know ‘apply p10 M == N’
 >- (rw [Abbr ‘p10’, Boehm_apply_APPEND] \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘apply p1 (principle_hnf M')’ \\
     CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong \\
                  CONJ_TAC >- art [] \\
                  MATCH_MP_TAC lameq_SYM \\
                  MATCH_MP_TAC lameq_principle_hnf' >> art []) \\
     rw [Abbr ‘p1’, appstar_SUB] \\
     Know ‘MAP [U/y] Ms = Ms’
     >- (rw [LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC lemma14b \\
         Q.PAT_X_ASSUM ‘EVERY (\e. y # e) Ms’ MP_TAC \\
         rw [EVERY_MEM, MEM_EL] \\
         POP_ASSUM MATCH_MP_TAC >> rename1 ‘i < m’ \\
         Q.EXISTS_TAC ‘i’ >> art []) >> Rewr' \\
     qunabbrevl_tac [‘U’, ‘N’] \\
     MATCH_MP_TAC selector_thm >> rw [Abbr ‘m’])
 >> DISCH_TAC
 (* stage work, now using IH *)
 >> Q.PAT_X_ASSUM ‘!M r. _’ (MP_TAC o (Q.SPECL [‘N’, ‘SUC r’])) >> simp []
 >> Know ‘FV N SUBSET X UNION RANK (SUC r)’
 >- (qunabbrevl_tac [‘N’, ‘M'’] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘FV (apply p0 M)’ >> art [] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘FV (VAR y @* Ms)’ \\
     reverse CONJ_TAC >- (MATCH_MP_TAC hreduce_FV_SUBSET >> art []) \\
     rw [SUBSET_DEF, FV_appstar, IN_UNION] \\
     DISJ2_TAC \\
     Q.EXISTS_TAC ‘FV (EL h Ms)’ >> art [] \\
     Q.EXISTS_TAC ‘EL h Ms’ >> rw [EL_MEM])
 >> RW_TAC std_ss []
 >> rename1 ‘apply p2 N == _ ISUB ss'’
 >> qabbrev_tac ‘N' = subterm' X M (h::t) r’
 (* final stage *)
 >> Q.EXISTS_TAC ‘p2 ++ p10’
 >> CONJ_TAC
 >- (MATCH_MP_TAC Boehm_transform_APPEND >> art [])
 >> Q.EXISTS_TAC ‘[(P,v)] ++ ss'’
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘apply p2 N’
 >> simp [ISUB_def]
 >> rw [Boehm_apply_APPEND]
 >> MATCH_MP_TAC Boehm_apply_lameq_cong >> art []
QED

(*---------------------------------------------------------------------------*
 *  Faithfulness and agreements of terms
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

(* Definition 10.2.32 (v) [1, p.245]

   NOTE: It's assumed that ‘X SUBSET FV M UNION FV N’ in applications.
 *)
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
 *)
Theorem subtree_equiv_lemma :
    !X Ms p r.
       FINITE X /\ p <> [] /\ 0 < r /\ Ms <> [] /\
       BIGUNION (IMAGE FV (set Ms)) SUBSET X UNION RANK r /\
       EVERY (\M. subterm X M p r <> NONE) Ms ==>
       ?pi. Boehm_transform pi /\ EVERY is_ready' (MAP (apply pi) Ms) /\
           (!M. MEM M Ms ==> p IN ltree_paths (BT' X (apply pi M) r)) /\
            !M N q. MEM M Ms /\ MEM N Ms /\ q <<= p ==>
                   (subtree_equiv X M N q r <=>
                    subtree_equiv X (apply pi M) (apply pi N) q r)
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘k = LENGTH Ms’
 >> Q.PAT_X_ASSUM ‘EVERY P Ms’ MP_TAC
 >> rw [EVERY_EL]
 >> qabbrev_tac ‘M = \i. EL i Ms’ >> fs []
 >> Know ‘!i. i < k ==> FV (M i) SUBSET X UNION RANK r’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘_ SUBSET X UNION RANK r’ MP_TAC \\
     rw [SUBSET_DEF, IN_BIGUNION_IMAGE] \\
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
     MATCH_MP_TAC subterm_imp_ltree_paths >> rw [])
 >> DISCH_TAC
 (* define M0 *)
 >> qabbrev_tac ‘M0 = \i. principle_hnf (M i)’
 >> Know ‘!i. i < k ==> hnf (M0 i)’
 >- (rw [Abbr ‘M0’] \\
     MATCH_MP_TAC hnf_principle_hnf \\
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
 >> qabbrev_tac ‘Y = BIGUNION (IMAGE FV (set Ms))’
 >> ‘FINITE Y’ by (rw [Abbr ‘Y’] >> REWRITE_TAC [FINITE_FV])
 (* ‘vs’ excludes all free variables in M

    NOTE: The basic requirement for ‘vs’ is that it must be disjoint with ‘Y’
    and is at row 0. But if we exclude ‘X UNION Y’, then it also holds that
    ‘set vs SUBSET X UNION RANK r’ just like another part of ‘M’.
  *)
 >> Q_TAC (NEWS_TAC (“vs :string list”, “n_max :num”)) ‘X UNION Y’
 >> Know ‘set vs SUBSET X UNION RANK (SUC r)’
 >- (Suff ‘set vs SUBSET RANK (SUC r)’ >- SET_TAC [] \\
     qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp [])
 >> DISCH_TAC
 (* construct p1 *)
 >> qabbrev_tac ‘p1 = MAP rightctxt (REVERSE (MAP VAR vs))’
 >> ‘Boehm_transform p1’ by rw [Abbr ‘p1’, MAP_MAP_o, GSYM MAP_REVERSE]
 (* decompose M0 by hnf_cases_shared *)
 >> Know ‘!i. i < k ==> ?y args. M0 i = LAMl (TAKE (n i) vs) (VAR y @* args)’
 >- (rw [Abbr ‘n’] >> irule (iffLR hnf_cases_shared) \\
     rw [] >- fs [o_DEF] \\
     MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘FV (EL i Ms)’ \\
     reverse CONJ_TAC
     >- (rw [Abbr ‘M0’] >> MATCH_MP_TAC principle_hnf_FV_SUBSET \\
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
 >> qabbrev_tac ‘M1 = \i. principle_hnf (M0 i @* MAP VAR vs)’
 >> Know ‘!i. i < k ==> M1 i = VAR (y i) @* args i @* DROP (n i) (MAP VAR vs)’
 >- (rw [Abbr ‘M1’] \\
     qabbrev_tac ‘t = VAR (y i) @* args i’ \\
     rw [GSYM MAP_DROP] \\
     qabbrev_tac ‘xs = TAKE (n i) vs’ \\
     Know ‘MAP VAR vs = MAP VAR xs ++ MAP VAR (DROP (n i) vs)’
     >- (REWRITE_TAC [GSYM MAP_APPEND] >> AP_TERM_TAC \\
         rw [Abbr ‘xs’, TAKE_DROP]) >> Rewr' \\
     REWRITE_TAC [appstar_APPEND] \\
     qabbrev_tac ‘l = MAP VAR (DROP (n i) vs)’ \\
     MATCH_MP_TAC principle_hnf_beta_reduce_ext \\
     rw [Abbr ‘t’, hnf_appstar])
 >> DISCH_TAC
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
 >> qabbrev_tac ‘d = MAX_LIST (MAP (\e. subterm_width e p) Ms)’
 >> Know ‘!i. i < k ==> subterm_width (M i) p <= d’
 >- (rw [Abbr ‘d’] \\
     MATCH_MP_TAC MAX_LIST_PROPERTY >> rw [MEM_MAP] \\
     Q.EXISTS_TAC ‘M i’ >> rw [EL_MEM, Abbr ‘M’])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==> m i <= d’
 >- (RW_TAC std_ss [] \\
     Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width (M i) p’ \\
     MP_TAC (Q.SPECL [‘X’, ‘(M :num -> term) i’, ‘p’, ‘r’] subterm_width_first) \\
     simp [Abbr ‘m’])
 >> DISCH_TAC
 (* NOTE: Thus P(d) is not enough to cover M1, whose ‘hnf_children_size’ is
    bounded by ‘d + n_max’. *)
 >> qabbrev_tac ‘d_max = d + n_max’
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
 (* stage work

    NOTE: There may be duplicated names among all ‘y i’. The function f maps
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
 (* Now we have a list of M1's whose children size is bounded by d_max.
    In the worst case, ‘P @* M1 i’ will leave ‘SUC d_max’ variable bindings
    at most (in this case, ‘args i = 0 /\ n i = n_max’), and to finally get a
   "is_ready" term, we should apply a fresh list of d_max+1 variables (l).

   NOTE: After redefining P by (\i. permutator (d_max + i), in the new worst
   case ‘P (f i) @* M1 i’ will leave at most ‘SUC d_max + k’ ending variables.
  *)
 >> Q_TAC (NEWS_TAC (“xs :string list”, “SUC d_max + k”))
          ‘X UNION (Y UNION set vs)’
 (* p3 is the maximal possible fresh list to be applied after the permutator *)
 >> qabbrev_tac ‘p3 = MAP rightctxt (REVERSE (MAP VAR xs))’
 >> ‘Boehm_transform p3’ by rw [Abbr ‘p3’, MAP_MAP_o, GSYM MAP_REVERSE]
 (* pre-final stage *)
 >> Q.EXISTS_TAC ‘p3 ++ p2 ++ p1’
 >> CONJ_TAC
 >- (MATCH_MP_TAC Boehm_transform_APPEND >> art [] \\
     MATCH_MP_TAC Boehm_transform_APPEND >> art [])
 >> ‘Boehm_transform (p3 ++ p2 ++ p1)’
       by (rpt (MATCH_MP_TAC Boehm_transform_APPEND >> art []))
 >> qabbrev_tac ‘pi = p3 ++ p2 ++ p1’
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
  (* applying principle_hnf_FV_SUBSET' *)
     Know ‘FV (M0 i) SUBSET FV (M i)’
     >- (SIMP_TAC std_ss [Abbr ‘M0’, o_DEF] \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' >> rw []) \\
     qunabbrev_tac ‘Z'’ \\
     Suff ‘y i IN FV (M0 i) UNION set vs /\
           BIGUNION (IMAGE FV (set (args i))) SUBSET
           FV (M0 i) UNION set vs’
     >- SET_TAC [] \\
     Know ‘FV (M1 i) SUBSET FV (M0 i @* MAP VAR vs)’
     >- (‘M1 i = principle_hnf (M0 i @* MAP VAR vs)’ by rw [] >> POP_ORW \\
         MATCH_MP_TAC principle_hnf_FV_SUBSET' \\
        ‘M0 i @* MAP VAR vs = apply p1 (M0 i)’
            by rw [Abbr ‘p1’, Boehm_apply_MAP_rightctxt'] >> POP_ORW \\
         Suff ‘solvable (M1 i)’ >- METIS_TAC [lameq_solvable_cong] \\
         REWRITE_TAC [solvable_iff_has_hnf] \\
         MATCH_MP_TAC hnf_has_hnf \\
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
 >- (rw [Abbr ‘Z’, UNION_SUBSET] \\
     Suff ‘set vs SUBSET RANK r’ >- SET_TAC [] \\
     qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw [])
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
     rw [BIGUNION_SUBSET] \\
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
         MATCH_MP_TAC principle_hnf_FV_SUBSET' >> simp []) \\
     qabbrev_tac ‘vs' = TAKE (n i) vs’ \\
    ‘M0 i @* MAP VAR vs' == VAR (y i) @* args i’
       by simp [lameq_LAMl_appstar_VAR] \\
  (* applying principle_hnf_beta_reduce *)
     Know ‘principle_hnf (M0 i @* MAP VAR vs') = VAR (y i) @* args i’
     >- (simp [] \\
         MATCH_MP_TAC principle_hnf_beta_reduce \\
         simp [hnf_appstar]) >> DISCH_TAC \\
     MP_TAC (Q.SPEC ‘M0 (i :num) @* MAP VAR vs'’ principle_hnf_FV_SUBSET') \\
     impl_tac >- (Suff ‘solvable (VAR (y i) @* args i)’
                  >- METIS_TAC [lameq_solvable_cong] \\
                  REWRITE_TAC [solvable_iff_has_hnf] \\
                  MATCH_MP_TAC hnf_has_hnf \\
                  simp [hnf_appstar]) \\
     POP_ORW \\
     REWRITE_TAC [FV_appstar_MAP_VAR, FV_appstar, FV_thm] \\
     SET_TAC [])
 >> DISCH_TAC
 (* NOTE: now, before proving ‘EVERY is_ready' ...’, (for future subgoals) we
    need to calculute the principle_hnf of ‘apply pi (EL i Ms)’ for any i < k.

   ‘args'’ is the possibly substituted version of ‘args’.
  *)
 >> qabbrev_tac ‘args' = \i. MAP (\t. t ISUB ss) (args i)’
 >> ‘!i. LENGTH (args' i) = m i’ by rw [Abbr ‘args'’, Abbr ‘m’]
 (* NOTE: In vs0, some elements are replaced by P, thus ‘set vs0 SUBSET set vs’ *)
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
                  MATCH_MP_TAC lameq_principle_hnf' >> rw []) \\
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
 (* calculating ‘principle_hnf (apply pi (M i))’ (hard) *)
 >> Know ‘!i. i < k ==>
              principle_hnf (apply pi (M i)) = VAR (b i) @* Ns i @* tl i’
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
  (* NOTE: This MP_TAC is for applying principle_hnf_denude_thm later. From
     now on, both ‘apply pi M == ...’ and ‘principle_hnf (apply pi M) = ...’
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
  (* rewriting RHS to principle_hnf of ISUB *)
     Know ‘VAR (b i) @* Ns i @* tl i =
           principle_hnf (P (f i) @* args' i @* args2 i @* MAP VAR xs)’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
        ‘hnf (VAR (b i) @* Ns i @* tl i)’
            by rw [GSYM appstar_APPEND, hnf_appstar] \\
         Suff ‘solvable (P (f i) @* args' i @* args2 i @* MAP VAR xs)’
         >- (METIS_TAC [principle_hnf_thm']) \\
         Suff ‘solvable (VAR (b i) @* Ns i @* tl i) /\
               P (f i) @* Ns i @@ VAR (b i) @* tl i == VAR (b i) @* Ns i @* tl i’
         >- (METIS_TAC [lameq_solvable_cong]) \\
         reverse CONJ_TAC >- (MATCH_MP_TAC hreduces_lameq >> rw []) \\
         REWRITE_TAC [solvable_iff_has_hnf] \\
         MATCH_MP_TAC hnf_has_hnf >> art []) >> Rewr' \\
     Know ‘P (f i) @* args' i @* args2 i @* MAP VAR xs = M1 i @* MAP VAR xs ISUB ss’
     >- (REWRITE_TAC [appstar_ISUB, Once EQ_SYM_EQ] \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> apply p2 (M1 i) = _’
           (drule o GSYM) >> Rewr' \\
         Q.PAT_X_ASSUM ‘!t. apply p2 t = t ISUB ss’ (ONCE_REWRITE_TAC o wrap) \\
         AP_TERM_TAC >> art []) >> Rewr' \\
  (* applying principle_hnf_ISUB_cong *)
     MATCH_MP_TAC principle_hnf_ISUB_cong \\
     CONJ_TAC (* has_hnf #1 *)
     >- (simp [GSYM solvable_iff_has_hnf, GSYM appstar_APPEND] \\
         Know ‘M0 i == M i’
         >- (SIMP_TAC std_ss [Abbr ‘M0’] \\
             MATCH_MP_TAC lameq_principle_hnf' >> rw []) >> DISCH_TAC \\
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
         REWRITE_TAC [solvable_iff_has_hnf] \\
         MATCH_MP_TAC hnf_has_hnf >> rw [hnf_appstar]) \\
     CONJ_TAC (* has_hnf #2 *)
     >- (REWRITE_TAC [GSYM solvable_iff_has_hnf] \\
         Suff ‘solvable (VAR (b i) @* Ns i @* tl i)’
         >- PROVE_TAC [lameq_solvable_cong] \\
         REWRITE_TAC [solvable_iff_has_hnf] \\
         MATCH_MP_TAC hnf_has_hnf >> rw [hnf_appstar]) \\
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
  (* applying principle_hnf_denude_thm, finally *)
     MATCH_MP_TAC principle_hnf_denude_thm >> simp [] \\
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
     REWRITE_TAC [solvable_iff_has_hnf] \\
     MATCH_MP_TAC hnf_has_hnf >> rw [hnf_appstar, GSYM appstar_APPEND])
 >> DISCH_TAC
 >> PRINT_TAC "stage work on subtree_equiv_lemma: L6560"
 >> CONJ_TAC (* EVERY is_ready' ... *)
 >- (rpt (Q.PAT_X_ASSUM ‘Boehm_transform _’ K_TAC) \\
     simp [EVERY_EL, EL_MAP] \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
  (* now expanding ‘is_ready’ using [is_ready_alt] *)
     ASM_SIMP_TAC std_ss [is_ready_alt'] \\
     qexistsl_tac [‘b i’, ‘Ns i ++ tl i’] \\
  (* subgoal: apply pi (M i) -h->* VAR (b i) @* (Ns i ++ tl i) *)
     CONJ_TAC
     >- (REWRITE_TAC [appstar_APPEND] \\
         Q.PAT_X_ASSUM ‘!i. i < k ==> principle_hnf (apply pi (M i)) = _’ drule \\
         rw [principle_hnf_thm']) \\
  (* final goal (is_ready): EVERY (\e. b # e) ... *)
     Q.PAT_X_ASSUM ‘!i. i < k ==> principle_hnf (apply pi (M i)) = _’ K_TAC \\
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
 >> PRINT_TAC "stage work on subtree_equiv_lemma: L6720"
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
         Q.EXISTS_TAC ‘RANK r’ >> rw [DISJOINT_RANK_RNEWS'] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ \\
         CONJ_TAC >- rw [Abbr ‘vs’, RNEWS_SUBSET_ROW] \\
         MATCH_MP_TAC ROW_SUBSET_RANK >> art []) >> DISCH_TAC \\
     Know ‘DISJOINT (set vs') (set ys')’
     >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs’ >> art [] \\
         rw [Abbr ‘vs'’, LIST_TO_SET_TAKE]) >> DISCH_TAC \\
     qabbrev_tac ‘t = VAR (y i) @* args i’ \\
  (* applying for principle_hnf_tpm_reduce *)
     Know ‘principle_hnf (LAMl vs' t @* MAP VAR ys') = tpm (ZIP (vs',ys')) t’
     >- (‘hnf t’ by rw [Abbr ‘t’, hnf_appstar] \\
         MATCH_MP_TAC principle_hnf_tpm_reduce' >> art [] \\
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
         >- (qunabbrev_tac ‘vs’ \\
             MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw []) >> DISCH_TAC \\
         Know ‘set vs' SUBSET RANK (SUC r)’
         >- (qunabbrev_tac ‘vs'’ \\
             Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set vs’ \\
             rw [LIST_TO_SET_TAKE]) >> DISCH_TAC \\
         Know ‘set ys' SUBSET RANK (SUC r)’
         >- (qunabbrev_tac ‘ys'’ \\
             MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw []) >> DISCH_TAC \\
         simp [Abbr ‘Z’, IN_UNION] \\
         reverse STRIP_TAC
      (* lswapstr (REVERSE pm) x IN set vs *)
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
             Know ‘set vs SUBSET ROW 0’
             >- (qunabbrev_tac ‘vs’ \\
                 MATCH_MP_TAC RNEWS_SUBSET_ROW >> rw []) >> DISCH_TAC \\
             Know ‘set ys' SUBSET ROW r’
             >- (qunabbrev_tac ‘ys'’ \\
                 MATCH_MP_TAC RNEWS_SUBSET_ROW >> art []) >> DISCH_TAC \\
             Know ‘DISJOINT (ROW 0) (ROW r)’ >- rw [ROW_DISJOINT] \\
             rw [DISJOINT_ALT] \\
             Suff ‘EL a vs NOTIN ROW r’ >- METIS_TAC [SUBSET_DEF] \\
             FIRST_X_ASSUM MATCH_MP_TAC \\
             Suff ‘EL a vs IN set vs’ >- METIS_TAC [SUBSET_DEF] \\
             MATCH_MP_TAC EL_MEM >> art []) \\
      (* lswapstr (REVERSE pm) x IN Y (SUBSET X UNION RANK r) *)
         Know ‘lswapstr (REVERSE pm) x IN X UNION RANK r’ >- ASM_SET_TAC [] \\
         Q.PAT_X_ASSUM ‘lswapstr (REVERSE pm) x IN Y’ K_TAC \\
         RW_TAC std_ss [IN_UNION]
         >- (FULL_SIMP_TAC std_ss [GSYM ssetpm_IN] \\
             DISJ1_TAC \\
             Suff ‘ssetpm pm X = X’ >- DISCH_THEN (FULL_SIMP_TAC std_ss o wrap) \\
             MATCH_MP_TAC ssetpm_unchanged >> rw [Abbr ‘pm’, MAP_ZIP] \\
             MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set vs’ >> art [] \\
             rw [Abbr ‘vs'’, LIST_TO_SET_TAKE]) \\
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
         qunabbrev_tac ‘vs’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> rw []) \\
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
 (* stage work: !M. MEM M Ms ==> p IN ltree_paths (BT' X (apply pi M) r) *)
 >> CONJ_TAC
 >- (RW_TAC std_ss [MEM_EL] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 (* upper bound of all FVs from l (args' ++ args2 ++ xs) *)
 >> Know ‘!i. i < k ==> BIGUNION (IMAGE FV (set (l i))) SUBSET X UNION RANK r’
 >- (rw [Abbr ‘l’] >| (* 3 subgoals *)
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
       reverse CONJ_TAC >- (MATCH_MP_TAC ROW_SUBSET_RANK >> art []) \\
       rw [IN_BIGUNION_IMAGE, SUBSET_DEF, MEM_MAP] \\
       POP_ASSUM MP_TAC >> rw [] \\
       Suff ‘set xs SUBSET ROW 0’ >- rw [SUBSET_DEF] \\
       qunabbrev_tac ‘xs’ \\
       MATCH_MP_TAC RNEWS_SUBSET_ROW >> rw [] ])
 >> DISCH_TAC
 (* ‘H i’ is the head reduction of apply pi (M i) *)
 >> qabbrev_tac ‘H = \i. VAR (b i) @* Ns i @* tl i’
 >> Know ‘!i. solvable (H i)’
 >- (rw [Abbr ‘H’, solvable_iff_has_hnf] \\
     MATCH_MP_TAC hnf_has_hnf >> rw [hnf_appstar])
 >> DISCH_TAC
 >> Know ‘!i. i < k ==> FV (H i) SUBSET X UNION RANK r’
 >- (rw [Abbr ‘H’, GSYM appstar_APPEND, FV_appstar] >| (* 3 subgoals *)
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
       qunabbrev_tac ‘xs’ \\
       MATCH_MP_TAC RNEWS_SUBSET_ROW >> simp [],
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
 >- (qunabbrevl_tac [‘vs’, ‘ys’] \\
     MATCH_MP_TAC DISJOINT_RNEWS >> simp [])
 >> DISCH_TAC
 >> PRINT_TAC "stage work on subtree_equiv_lemma: L7024"
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
     Know ‘principle_hnf (H i) = H i’
     >- (MATCH_MP_TAC principle_hnf_reduce \\
         simp [Abbr ‘H’, GSYM appstar_APPEND, hnf_appstar]) >> DISCH_TAC \\
    ‘LAMl_size (H i) = 0’
       by rw [Abbr ‘H’, LAMl_size_appstar, GSYM appstar_APPEND] \\
     simp [] \\
     NTAC 2 (POP_ASSUM K_TAC) \\
     DISCH_TAC \\
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
     >- (qunabbrev_tac ‘ys’ \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘RANK r’ >> rw [DISJOINT_RANK_RNEWS'] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘ROW 0’ \\
         CONJ_TAC >- rw [Abbr ‘vs’, RNEWS_SUBSET_ROW] \\
         MATCH_MP_TAC ROW_SUBSET_RANK >> art []) >> DISCH_TAC \\
     Know ‘DISJOINT (set vs') (set ys')’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘set ys’ \\
         reverse CONJ_TAC >- rw [LIST_TO_SET_TAKE] \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs’ \\
         simp [Abbr ‘vs'’, LIST_TO_SET_TAKE]) >> DISCH_TAC \\
  (* applying for principle_hnf_tpm_reduce *)
     Know ‘principle_hnf (LAMl vs' t0 @* MAP VAR ys') = tpm (ZIP (vs',ys')) t0’
     >- (‘hnf t0’ by rw [Abbr ‘t0’, hnf_appstar] \\
         MATCH_MP_TAC principle_hnf_tpm_reduce' >> art [] \\
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
     fs [Abbr ‘args'’, EL_MAP] \\
     qabbrev_tac ‘pm' = ZIP (vs',ys')’ \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs') (set ys')’ K_TAC \\
  (* applying tpm_unchanged *)
     Know ‘tpm pm' N = tpm pm N’ (* (n i) vs n_max *)
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
             rw [DISJOINT_ALT'] \\
             Know ‘x IN FV (M i) UNION set (TAKE (n i) vs)’
             >- METIS_TAC [SUBSET_DEF] \\
             rw [IN_UNION]
             >- (Q.PAT_X_ASSUM ‘DISJOINT (set ys) (FV (M i))’ MP_TAC \\
                 rw [DISJOINT_ALT']) \\
             Suff ‘DISJOINT (set (TAKE (n i) vs)) (set ys)’
             >- rw [DISJOINT_ALT] \\
             MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set vs’ >> rw [LIST_TO_SET_TAKE]) \\
      (* vs is slightly harder *)
         rw [DISJOINT_ALT'] \\
         Know ‘x IN FV (M i) UNION set (TAKE (n i) vs)’
         >- METIS_TAC [SUBSET_DEF] \\
         reverse (rw [IN_UNION])
         >- (Know ‘ALL_DISTINCT (TAKE (n i) vs ++ DROP (n i) vs)’
             >- rw [TAKE_DROP] \\
             rw [ALL_DISTINCT_APPEND]) \\
         Suff ‘DISJOINT (set (DROP (n i) vs)) (FV (M i))’ >- rw [DISJOINT_ALT'] \\
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
         rw [BIGUNION_SUBSET] \\
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
 >> PRINT_TAC "stage work on subtree_equiv_lemma: L7236"
 >> Suff ‘(!M N q.
            MEM M Ms /\ MEM N Ms /\ q <<= p /\
            subtree_equiv X M N q r ==>
            subtree_equiv X (apply pi M) (apply pi N) q r) /\
          (!M N q.
            MEM M Ms /\ MEM N Ms /\ q <<= p /\
            subtree_equiv X (apply pi M) (apply pi N) q r ==>
            subtree_equiv X M N q r)’
 >- METIS_TAC []
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
  (* applying BT_of_principle_hnf *)
     Know ‘BT' X (M' j1) r = BT' X (principle_hnf (M' j1)) r’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC BT_of_principle_hnf \\
         simp [Abbr ‘M'’] \\
         METIS_TAC [lameq_solvable_cong]) >> Rewr' \\
     Know ‘BT' X (M' j2) r = BT' X (principle_hnf (M' j2)) r’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC BT_of_principle_hnf \\
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

     The case ‘q = []’ is special:
   *)
     Cases_on ‘q = []’
     >- (POP_ORW >> simp [BT_ltree_el_NIL] \\
         Know ‘!i. principle_hnf (H i) = H i’
         >- (rw [Abbr ‘H’] >> MATCH_MP_TAC principle_hnf_reduce \\
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
         Q_TAC (RNEWS_TAC (“ys1 :string list”, “r :num”,
                           “(n :num -> num) j1”)) ‘X’ \\
         Q_TAC (RNEWS_TAC (“ys2 :string list”, “r :num”,
                           “(n :num -> num) j2”)) ‘X’ \\
         Know ‘DISJOINT (set vs1) (set ys1)’
         >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set vs’ \\
             reverse CONJ_TAC >- rw [Abbr ‘vs1’, LIST_TO_SET_TAKE] \\
             qunabbrev_tac ‘ys1’ \\
             MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘RANK r’ >> rw [DISJOINT_RANK_RNEWS'] \\
             MATCH_MP_TAC SUBSET_TRANS \\
             Q.EXISTS_TAC ‘ROW 0’ \\
             CONJ_TAC >- rw [Abbr ‘vs’, RNEWS_SUBSET_ROW] \\
             MATCH_MP_TAC ROW_SUBSET_RANK >> art []) >> DISCH_TAC \\
         Know ‘DISJOINT (set vs2) (set ys2)’
         >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘set vs’ \\
             reverse CONJ_TAC >- rw [Abbr ‘vs2’, LIST_TO_SET_TAKE] \\
             qunabbrev_tac ‘ys2’ \\
             MATCH_MP_TAC DISJOINT_SUBSET' \\
             Q.EXISTS_TAC ‘RANK r’ >> rw [DISJOINT_RANK_RNEWS'] \\
             MATCH_MP_TAC SUBSET_TRANS \\
             Q.EXISTS_TAC ‘ROW 0’ \\
             CONJ_TAC >- rw [Abbr ‘vs’, RNEWS_SUBSET_ROW] \\
             MATCH_MP_TAC ROW_SUBSET_RANK >> art []) >> DISCH_TAC \\
         qabbrev_tac ‘t1 = VAR (y j1) @* args j1’ \\
         qabbrev_tac ‘t2 = VAR (y j2) @* args j2’ \\
      (* applying for principle_hnf_tpm_reduce *)
         Know ‘principle_hnf (LAMl vs1 t1 @* MAP VAR ys1) = tpm (ZIP (vs1,ys1)) t1’
         >- (‘hnf t1’ by rw [Abbr ‘t1’, hnf_appstar] \\
             MATCH_MP_TAC principle_hnf_tpm_reduce' >> art [] \\
             MATCH_MP_TAC subterm_disjoint_lemma \\
             qexistsl_tac [‘X’, ‘r’, ‘n j1’] >> simp [] \\
             MATCH_MP_TAC SUBSET_TRANS \\
             Q.EXISTS_TAC ‘Z’ >> art [] \\
             rw [Abbr ‘t1’, FV_appstar]) >> Rewr' \\
         Know ‘principle_hnf (LAMl vs2 t2 @* MAP VAR ys2) = tpm (ZIP (vs2,ys2)) t2’
         >- (‘hnf t2’ by rw [Abbr ‘t2’, hnf_appstar] \\
             MATCH_MP_TAC principle_hnf_tpm_reduce' >> art [] \\
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

        P (f j1) = VAR (y j1) ISUB ss =
                   VAR (y j2) ISUB ss = P (f j2)
    ==> permutator (d_max + f j1) = permutator (d_max + f j2)
    ==> d_max + f j1 = d_max + f j2 ==> f j1 = f j2
       *)
         PRINT_TAC "stage work on subtree_equiv_lemma: L7381" \\
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
           Abbrev (M1 = (\i. principle_hnf (M0 i @* MAP VAR vs)))
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
     qabbrev_tac ‘N0 = principle_hnf N’ \\
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
     qabbrev_tac ‘N0' = principle_hnf N'’ \\
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
     qabbrev_tac ‘N1 = principle_hnf (N0 @* MAP VAR vs1)’ \\
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
     qabbrev_tac ‘N1' = principle_hnf (N0' @* MAP VAR vs2)’ \\
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
         qunabbrev_tac ‘vs’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp [Abbr ‘r1’]) >> DISCH_TAC \\
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
           simp [subterm_width_nil, principle_hnf_tpm'] \\
           rpt STRIP_TAC \\
           Know ‘y i IN X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
           Suff ‘RANK r SUBSET RANK r1’ >- SET_TAC [] \\
           simp [Abbr ‘r1’, RANK_MONO],
           (* goal 2 (of 2) *)
           MATCH_MP_TAC (cj 1 solvable_isub_permutator_alt) \\
           qexistsl_tac [‘X’, ‘r1’, ‘d_max’, ‘y’, ‘k’] \\
           simp [subterm_width_nil, principle_hnf_tpm'] \\
           rpt STRIP_TAC \\
           Know ‘y i IN X UNION RANK r’ >- METIS_TAC [SUBSET_DEF] \\
           Suff ‘RANK r SUBSET RANK r1’ >- SET_TAC [] \\
           simp [Abbr ‘r1’, RANK_MONO] ]) >> STRIP_TAC \\
  (* stage work *)
     PRINT_TAC "stage work on subtree_equiv_lemma: L7668" \\
     Q.PAT_X_ASSUM ‘!i. i < k ==> subterm X (H i) q r <> NONE /\ _’ ASSUME_TAC \\
  (* applying BT_subterm_thm on ‘H j1’ *)
     MP_TAC (Q.SPECL [‘q’, ‘X’, ‘H (j1 :num)’, ‘r’] BT_subterm_thm) \\
     simp [] >> STRIP_TAC (* this asserts ‘x’ *) \\
     NTAC 3 (Cases_on ‘x’ >> fs []) \\
     rename1 ‘subterm X (H j1) q r = SOME (W,r1)’ \\
     qabbrev_tac ‘W0 = principle_hnf W’ \\
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
     qabbrev_tac ‘W0' = principle_hnf W'’ \\
     qabbrev_tac ‘m4 = hnf_children_size W0'’ \\
     rename1 ‘ltree_el (BT' X (H j2) r) q = SOME (SOME (vs4,y4),SOME m4)’ \\
     Q.PAT_X_ASSUM ‘_ = SOME (vs4,y4)’ K_TAC \\
     Q.PAT_X_ASSUM ‘_ = SOME m4’       K_TAC \\
     qabbrev_tac ‘n4 = LAMl_size W0'’ \\
     Q.PAT_X_ASSUM ‘_ = r1’ (fs o wrap) >> T_TAC \\
  (* decompose W *)
     Q.PAT_X_ASSUM ‘RNEWS r1 n3 X = vs3’ (fs o wrap o SYM) \\
     Q_TAC (RNEWS_TAC (“vs3 :string list”, “r1 :num”, “n3 :num”)) ‘X’ \\
     qabbrev_tac ‘W1 = principle_hnf (W0 @* MAP VAR vs3)’ \\
     Q_TAC (HNF_TAC (“W0 :term”, “vs3 :string list”,
                     “y3' :string”, “Ns3 :term list”)) ‘W1’ \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs3) (FV W0)’ K_TAC \\
  (* decompose W' *)
     Q.PAT_X_ASSUM ‘RNEWS r1 n4 X = vs4’ (fs o wrap o SYM) \\
     Q_TAC (RNEWS_TAC (“vs4 :string list”, “r1 :num”, “n4 :num”)) ‘X’ \\
     qabbrev_tac ‘W1' = principle_hnf (W0' @* MAP VAR vs4)’ \\
     Q_TAC (HNF_TAC (“W0' :term”, “vs4 :string list”,
                     “y4' :string”, “Ns4 :term list”)) ‘W1'’ \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs4) (FV W0')’ K_TAC \\
  (* stage work *)
     Know ‘TAKE (LAMl_size W0) vs3 = vs3 /\ TAKE (LAMl_size W0') vs4 = vs4’
     >- simp [] \\
     DISCH_THEN (rfs o CONJUNCTS) \\
     Q.PAT_X_ASSUM ‘hnf_headvar (principle_hnf (W0 @* MAP VAR vs3)) = y3’ MP_TAC \\
     simp [] (* y3' = y3 *) \\
     DISCH_THEN (rfs o wrap) \\
     Q.PAT_X_ASSUM ‘hnf_headvar (principle_hnf (W0' @* MAP VAR vs4)) = y4’ MP_TAC \\
     simp [] (* y4' = y4 *) \\
     DISCH_THEN (rfs o wrap) \\
  (* properties of W0 *)
    ‘LAMl_size W0 = n3 /\ hnf_children_size W0 = m3 /\ hnf_headvar W1 = y3’
       by rw [] \\
     Q.PAT_X_ASSUM ‘W0 = _’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘W1 = _’ (ASSUME_TAC o SYM) \\
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
    ‘N -h->* N0 /\ N' -h->* N0'’ by METIS_TAC [principle_hnf_thm'] \\
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
           qunabbrevl_tac [‘vs1’, ‘vs’] \\
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
           qunabbrevl_tac [‘vs2’, ‘vs’] \\
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
         LAMl vs2 (VAR y1' @* Ns2'') = W0'’ by METIS_TAC [principle_hnf_thm'] \\
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
     PRINT_TAC "stage work on subtree_equiv_lemma: L7837" \\
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
         METIS_TAC [principle_hnf_thm']) >> STRIP_TAC \\
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
     3. principle_hnf (W0  @* MAP VAR vs3) = VAR y3 @* Ns3 (= W1 )
     4. principle_hnf (W0' @* MAP VAR vs4) = VAR y4 @* Ns4 (= W1')

     Thus y3 and y4 are the same permutation of h, thus is the same. To
     actually prove it, we can use [principle_hnf_tpm_reduce'], which requires
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
                                      (SUC d_max)
                      ----- L -------------->|
     zs1' = |<--- vs1 --->|<--- zs1 ------>|h| (ROW 0 & r1)
     vs3  = |<---(vs1)--- vs3 ----(xs1)----->| (ROW r1)
             (n3 = 1 + d_max + n1 - m1 > n1)

                                      (SUC d_max)
                      ----- L -------------->|
     zs2' = |<--- vs2 ------>|<-- zs2 ---->|h| (ROW 0 & r1)
     vs3  = |<---(vs2)----- vs4 ---(xs2)---->| (ROW r1)
             (n4 = 1 + d_max + n2 - m2 > n2)

     now applying RNEWS_prefix first:
   *)
     PRINT_TAC "stage work on subtree_equiv_lemma: L7986" \\
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
         qunabbrevl_tac [‘vs’, ‘vs3’] \\
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
      (* Ns1' is tpm (REVERSE pm) of Ns1
         pm = ZIP (vs,ys), vs is in ROW 0, ys s in ROW r
         vsx (part of vs4) is in ROW r1 > r

         The key is to prove DISJOINT (set vsx) (FV (EL i Ns1)).
       *)
         POP_ASSUM MP_TAC \\
         simp [Abbr ‘Ns1'’, EL_listpm, Abbr ‘pm’, REVERSE_ZIP] >> DISCH_TAC \\
      (* applying FV_tpm_disjoint *)
         MATCH_MP_TAC FV_tpm_disjoint \\
         simp [ALL_DISTINCT_REVERSE] \\
      (* goal: DISJOINT (set ys1) (FV (EL i Ns1)), given:

         principle_hnf (N0 @* MAP VAR vs1) = VAR y1 @* Ns1
         FV N0 SUBSET FV N SUBSET X UNION RANK r1
       *)
         Know ‘FV N0 SUBSET X UNION RANK r1’
         >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV N’ >> art [] \\
             qunabbrev_tac ‘N0’ \\
             MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) >> DISCH_TAC \\
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
             MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) >> DISCH_TAC \\
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
  (* applying hreduces_hnf_imp_principle_hnf *)
     Know ‘W1  = tpm pm1 (VAR h @* Ns1x) /\
           W1' = tpm pm2 (VAR h @* Ns2x)’
     >- (simp [Abbr ‘W1’, Abbr ‘W1'’] \\
         CONJ_TAC (* 2 subgoals, same tactics *) \\
         MATCH_MP_TAC hreduces_hnf_imp_principle_hnf \\
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
     >- (PRINT_TAC "stage work on subtree_equiv_lemma: L8238" \\
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
     PRINT_TAC "stage work on subtree_equiv_lemma: L8253" \\
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
 >> PRINT_TAC "stage work on subtree_equiv_lemma: L8339"
 >> rpt GEN_TAC >> STRIP_TAC
 >> POP_ASSUM MP_TAC
 >> ONCE_REWRITE_TAC [MONO_NOT_EQ]
 (* NOTE: The antecedent “~subtree_equiv' X t1 t2 q r” makes sure that
   ‘n1 + m2 <> n1 + m1’ is always assumed (instead of ‘y1 <> y2’). And
    the goal is to prove ‘y3 <> y4 \/ n3 + m3 <> n4 + m4’

    The original proof assumes q = p, but the proof also work for q <<= p.
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
 >> Know ‘BT' X (M' j1) r = BT' X (principle_hnf (M' j1)) r’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC BT_of_principle_hnf \\
     simp [Abbr ‘M'’] \\
     METIS_TAC [lameq_solvable_cong])
 >> Rewr'
 >> Know ‘BT' X (M' j2) r = BT' X (principle_hnf (M' j2)) r’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC BT_of_principle_hnf \\
     simp [Abbr ‘M'’] \\
     METIS_TAC [lameq_solvable_cong])
 >> Rewr'
 >> simp [Abbr ‘M'’] (* now H is involved instead of ‘apply pi ...’ *)
 (* special case: q = [] *)
 >> Cases_on ‘q = []’
 >- (Q.PAT_X_ASSUM ‘!q. q <<= p /\ q <> [] ==> _’ K_TAC \\
     POP_ORW >> simp [BT_ltree_el_NIL] \\
     Know ‘!i. principle_hnf (H i) = H i’
     >- (rw [Abbr ‘H’] >> MATCH_MP_TAC principle_hnf_reduce \\
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
         qunabbrev_tac ‘ys1’ \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘RANK r’ >> rw [DISJOINT_RANK_RNEWS'] \\
         MATCH_MP_TAC SUBSET_TRANS \\
         Q.EXISTS_TAC ‘ROW 0’ \\
         CONJ_TAC >- rw [Abbr ‘vs’, RNEWS_SUBSET_ROW] \\
         MATCH_MP_TAC ROW_SUBSET_RANK >> art []) >> DISCH_TAC \\
     Know ‘DISJOINT (set vs2) (set ys2)’
     >- (MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘set vs’ \\
         reverse CONJ_TAC >- rw [Abbr ‘vs2’, LIST_TO_SET_TAKE] \\
         qunabbrev_tac ‘ys2’ \\
         MATCH_MP_TAC DISJOINT_SUBSET' \\
         Q.EXISTS_TAC ‘RANK r’ >> rw [DISJOINT_RANK_RNEWS'] \\
         MATCH_MP_TAC SUBSET_TRANS \\
         Q.EXISTS_TAC ‘ROW 0’ \\
         CONJ_TAC >- rw [Abbr ‘vs’, RNEWS_SUBSET_ROW] \\
         MATCH_MP_TAC ROW_SUBSET_RANK >> art []) >> DISCH_TAC \\
     qabbrev_tac ‘t1 = VAR (y j1) @* args j1’ \\
     qabbrev_tac ‘t2 = VAR (y j2) @* args j2’ \\
  (* applying for principle_hnf_tpm_reduce *)
     Know ‘principle_hnf (LAMl vs1 t1 @* MAP VAR ys1) = tpm (ZIP (vs1,ys1)) t1’
     >- (‘hnf t1’ by rw [Abbr ‘t1’, hnf_appstar] \\
         MATCH_MP_TAC principle_hnf_tpm_reduce' >> art [] \\
         MATCH_MP_TAC subterm_disjoint_lemma \\
         qexistsl_tac [‘X’, ‘r’, ‘n j1’] >> simp [] \\
         MATCH_MP_TAC SUBSET_TRANS \\
         Q.EXISTS_TAC ‘Z’ >> art [] \\
         rw [Abbr ‘t1’, FV_appstar]) >> Rewr' \\
     Know ‘principle_hnf (LAMl vs2 t2 @* MAP VAR ys2) = tpm (ZIP (vs2,ys2)) t2’
     >- (‘hnf t2’ by rw [Abbr ‘t2’, hnf_appstar] \\
         MATCH_MP_TAC principle_hnf_tpm_reduce' >> art [] \\
         MATCH_MP_TAC subterm_disjoint_lemma \\
         qexistsl_tac [‘X’, ‘r’, ‘n j2’] >> simp [] \\
         MATCH_MP_TAC SUBSET_TRANS \\
         Q.EXISTS_TAC ‘Z’ >> art [] \\
         rw [Abbr ‘t2’, FV_appstar]) >> Rewr' \\
     simp [Abbr ‘t1’, Abbr ‘t2’, tpm_appstar] \\
     PRINT_TAC "stage work on subtree_equiv_lemma: L8443" \\
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
     reverse (Cases_on ‘solvable (subterm' X (M j2) q r)’)
     >- (Know ‘unsolvable (subterm' X (M j2) q r) <=>
               ltree_el (BT' X (M j2) r) q = SOME bot’
         >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> rw []) \\
         simp []) \\
     Know ‘unsolvable (subterm' X (H j1) q r)’
     >- (ASM_SIMP_TAC std_ss [] \\
         MATCH_MP_TAC unsolvable_ISUB \\
         simp [solvable_tpm]) >> DISCH_TAC \\
     Know ‘unsolvable (subterm' X (H j1) q r) <=>
           ltree_el (BT' X (H j1) r) q = SOME bot’
     >- (MATCH_MP_TAC BT_ltree_el_of_unsolvables >> simp []) \\
     simp [] >> DISCH_THEN K_TAC \\
     MP_TAC (Q.SPECL [‘q’, ‘X’, ‘M (j2 :num)’, ‘r’] BT_subterm_thm) \\
     simp [] >> STRIP_TAC \\
     NTAC 3 (Cases_on ‘x’ >> fs []) \\
     qabbrev_tac ‘r2 = r + LENGTH q’ \\
     rename1 ‘subterm X (M j2) q r = SOME (N,r2)’ \\
     qabbrev_tac ‘N0 = principle_hnf N’ \\
     qabbrev_tac ‘m2 = hnf_children_size N0’ \\
     rename1 ‘ltree_el (BT' X (M j2) r) q = SOME (SOME (vs2,y2),SOME m2)’ \\
     Q.PAT_X_ASSUM ‘_ = SOME (vs2,y2)’ K_TAC >> gs [] \\
     Q.PAT_X_ASSUM ‘_ = r2’            K_TAC \\
     Q.PAT_X_ASSUM ‘_ = SOME m2’       K_TAC \\
     qabbrev_tac ‘n2 = LAMl_size N0’ \\
  (* decompose N *)
     Q.PAT_X_ASSUM ‘RNEWS r2 n2 X = vs2’ (fs o wrap o SYM) \\
     Q_TAC (RNEWS_TAC (“vs2 :string list”, “r2 :num”, “n2 :num”)) ‘X’ \\
     qabbrev_tac ‘N1 = principle_hnf (N0 @* MAP VAR vs2)’ \\
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
         qunabbrev_tac ‘vs’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp [Abbr ‘r2’]) >> DISCH_TAC \\
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
         simp [subterm_width_nil, principle_hnf_tpm'] \\
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
     qabbrev_tac ‘N0 = principle_hnf N’ \\
     qabbrev_tac ‘m1 = hnf_children_size N0’ \\
     rename1 ‘ltree_el (BT' X (M j1) r) q = SOME (SOME (vs1,y1),SOME m1)’ \\
     Q.PAT_X_ASSUM ‘_ = SOME (vs1,y1)’ K_TAC >> gs [] \\
     Q.PAT_X_ASSUM ‘_ = r1’      K_TAC \\
     Q.PAT_X_ASSUM ‘_ = SOME m1’ K_TAC \\
     qabbrev_tac ‘n1 = LAMl_size N0’ \\
  (* decompose N *)
     Q.PAT_X_ASSUM ‘RNEWS r1 n1 X = vs1’ (fs o wrap o SYM) \\
     Q_TAC (RNEWS_TAC (“vs1 :string list”, “r1 :num”, “n1 :num”)) ‘X’ \\
     qabbrev_tac ‘N1 = principle_hnf (N0 @* MAP VAR vs1)’ \\
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
         qunabbrev_tac ‘vs’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp [Abbr ‘r1’]) >> DISCH_TAC \\
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
         simp [subterm_width_nil, principle_hnf_tpm'] \\
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
 >> PRINT_TAC "stage work on subtree_equiv_lemma: L8751"
 >> MP_TAC (Q.SPECL [‘q’, ‘X’, ‘M (j1 :num)’, ‘r’] BT_subterm_thm)
 >> simp [] >> STRIP_TAC (* this asserts ‘x’ *)
 >> NTAC 3 (Cases_on ‘x’ >> fs [])
 >> qabbrev_tac ‘r1 = r + LENGTH q’
 >> rename1 ‘subterm X (M j1) q r = SOME (N,r1)’
 >> qabbrev_tac ‘N0 = principle_hnf N’
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
 >> qabbrev_tac ‘N0' = principle_hnf N'’
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
 >> qabbrev_tac ‘N1 = principle_hnf (N0 @* MAP VAR vs1)’
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
 >> qabbrev_tac ‘N1' = principle_hnf (N0' @* MAP VAR vs2)’
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
     qunabbrev_tac ‘vs’ \\
     MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp [Abbr ‘r1’])
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
       simp [subterm_width_nil, principle_hnf_tpm'] \\
       POP_ASSUM MP_TAC >> rw [Abbr ‘m1’] \\
       Q.PAT_X_ASSUM ‘IMAGE y (count k) SUBSET X UNION RANK r1’ MP_TAC \\
       rw [SUBSET_DEF] \\
       POP_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘i’ >> art [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC (cj 1 solvable_isub_permutator_alt) \\
       qexistsl_tac [‘X’, ‘r1’, ‘d_max’, ‘y’, ‘k’] \\
       simp [subterm_width_nil, principle_hnf_tpm'] \\
       POP_ASSUM MP_TAC >> rw [Abbr ‘m1’] \\
       Q.PAT_X_ASSUM ‘IMAGE y (count k) SUBSET X UNION RANK r1’ MP_TAC \\
       rw [SUBSET_DEF] \\
       POP_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘i’ >> art [] ])
 >> STRIP_TAC
 >> PRINT_TAC "stage work on subtree_equiv_lemma: L8881"
 >> Q.PAT_X_ASSUM ‘!i. i < k ==> subterm X (H i) q r <> NONE /\ _’ ASSUME_TAC
 >> MP_TAC (Q.SPECL [‘q’, ‘X’, ‘H (j1 :num)’, ‘r’] BT_subterm_thm)
 >> simp [] >> STRIP_TAC (* this asserts ‘x’ *)
 >> NTAC 3 (Cases_on ‘x’ >> fs [])
 >> rename1 ‘subterm X (H j1) q r = SOME (W,r1)’
 >> qabbrev_tac ‘W0 = principle_hnf W’
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
 >> qabbrev_tac ‘W0' = principle_hnf W'’
 >> qabbrev_tac ‘m4 = hnf_children_size W0'’
 >> rename1 ‘ltree_el (BT' X (H j2) r) q = SOME (SOME (vs4,y4),SOME m4)’
 >> Q.PAT_X_ASSUM ‘_ = SOME (vs4,y4)’ K_TAC
 >> Q.PAT_X_ASSUM ‘_ = SOME m4’       K_TAC
 >> qabbrev_tac ‘n4 = LAMl_size W0'’
 >> Q.PAT_X_ASSUM ‘_ = r1’ (fs o wrap) >> T_TAC
 (* decompose W *)
 >> Q.PAT_X_ASSUM ‘RNEWS r1 n3 X = vs3’ (fs o wrap o SYM)
 >> Q_TAC (RNEWS_TAC (“vs3 :string list”, “r1 :num”, “n3 :num”)) ‘X’
 >> qabbrev_tac ‘W1 = principle_hnf (W0 @* MAP VAR vs3)’
 >> Q_TAC (HNF_TAC (“W0 :term”, “vs3 :string list”,
                    “y3' :string”, “Ns3 :term list”)) ‘W1’
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs3) (FV W0)’ K_TAC
  (* decompose W' *)
 >> Q.PAT_X_ASSUM ‘RNEWS r1 n4 X = vs4’ (fs o wrap o SYM)
 >> Q_TAC (RNEWS_TAC (“vs4 :string list”, “r1 :num”, “n4 :num”)) ‘X’
 >> qabbrev_tac ‘W1' = principle_hnf (W0' @* MAP VAR vs4)’
 >> Q_TAC (HNF_TAC (“W0' :term”, “vs4 :string list”,
                    “y4' :string”, “Ns4 :term list”)) ‘W1'’
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs4) (FV W0')’ K_TAC
  (* decompose W and W' (ending part) *)
 >> Know ‘TAKE (LAMl_size W0) vs3 = vs3 /\ TAKE (LAMl_size W0') vs4 = vs4’
 >- simp []
 >> DISCH_THEN (rfs o CONJUNCTS)
 >> Q.PAT_X_ASSUM ‘hnf_headvar (principle_hnf (W0 @* MAP VAR vs3)) = y3’ MP_TAC
 >> simp [] (* y3' = y3 *)
 >> DISCH_THEN (rfs o wrap)
 >> Q.PAT_X_ASSUM ‘hnf_headvar (principle_hnf (W0' @* MAP VAR vs4)) = y4’ MP_TAC
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
 >> ‘N -h->* N0 /\ N' -h->* N0'’ by METIS_TAC [principle_hnf_thm']
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
       qunabbrevl_tac [‘vs1’, ‘vs’] \\
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
       qunabbrevl_tac [‘vs2’, ‘vs’] \\
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

    Now, to understand the (alternative) principle_hnf of W and W', we need to
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
     LAMl vs2 (VAR y2' @* Ns2'') = W0'’ by METIS_TAC [principle_hnf_thm'] \\
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

    It seems that y4 is ‘LAST vs4’ while y1' (at most in vs1/vs3, which is
    strictly shorter than vs4), thus cannot be the same (ALL_DISTINCT vs4).
  *)
 >- (PRINT_TAC "stage work on subtree_equiv_lemma: L9111" \\
     POP_ASSUM MP_TAC >> simp [ISUB_VAR_FRESH'] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘j3’ STRIP_ASSUME_TAC) \\
    ‘(LEAST j. y j = y2') = f j3’ by rw [] >> POP_ORW \\
     ONCE_REWRITE_TAC [TAUT ‘p /\ q ==> r <=> p ==> q ==> r’] >> STRIP_TAC \\
    ‘hnf (LAMl vs1 (VAR y1' @* Ns1''))’ by rw [hnf_appstar] \\
    ‘LAMl vs1 (VAR y1' @* Ns1'') = W0’ by METIS_TAC [principle_hnf_thm'] \\
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
         METIS_TAC [principle_hnf_thm']) >> DISCH_TAC \\
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
         qunabbrevl_tac [‘vs’, ‘vs4’] \\
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
             MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) >> DISCH_TAC \\
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
 >- (PRINT_TAC "stage work on subtree_equiv_lemma: L9414" \\
     Q.PAT_X_ASSUM ‘~(y1' NOTIN DOM ss)’ MP_TAC >> simp [ISUB_VAR_FRESH'] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘j3’ STRIP_ASSUME_TAC) \\
    ‘(LEAST j. y j = y1') = f j3’ by rw [] >> POP_ORW \\
     ONCE_REWRITE_TAC [TAUT ‘p /\ q ==> r <=> q ==> p ==> r’] >> STRIP_TAC \\
    ‘hnf (LAMl vs2 (VAR y2' @* Ns2''))’ by rw [hnf_appstar] \\
    ‘LAMl vs2 (VAR y2' @* Ns2'') = W0'’ by METIS_TAC [principle_hnf_thm'] \\
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
         METIS_TAC [principle_hnf_thm']) >> DISCH_TAC \\
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
         qunabbrevl_tac [‘vs’, ‘vs3’] \\
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
             MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) >> DISCH_TAC \\
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
 >> PRINT_TAC "stage work on subtree_equiv_lemma: L9685"
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
     METIS_TAC [principle_hnf_thm'])
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
         qunabbrevl_tac [‘vs’, ‘vs3’] \\
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
             MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) >> DISCH_TAC \\
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
         qunabbrevl_tac [‘vs’, ‘vs4’] \\
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
             MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) >> DISCH_TAC \\
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
 >> PRINT_TAC "stage work on subtree_equiv_lemma: L10027"
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
 >> PRINT_TAC "stage work on subtree_equiv_lemma: L10097"
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

val _ = export_theory ();
val _ = html_theory "boehm";

(* References:

 [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
     College Publications, London (1984).
 [2] https://en.wikipedia.org/wiki/Corrado_Böhm (UOK)
 [3] Böhm, C.: Alcune proprietà delle forme β-η-normali nel λ-K-calcolo. (UOK)
     Pubblicazioni dell'IAC 696, 1-19 (1968)
     English translation: "Some properties of beta-eta-normal forms in the
     lambda-K-calculus".
 *)
