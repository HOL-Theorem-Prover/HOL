(*---------------------------------------------------------------------------*
 * boehmScript.sml: (Effective) Boehm Trees (Chapter 10 of [1])              *
 *---------------------------------------------------------------------------*)

open HolKernel boolLib Parse bossLib;

(* core theories *)
open optionTheory arithmeticTheory pred_setTheory listTheory rich_listTheory
     llistTheory relationTheory ltreeTheory pathTheory posetTheory hurdUtils
     finite_mapTheory;

open binderLib nomsetTheory termTheory appFOLDLTheory chap2Theory chap3Theory
     head_reductionTheory standardisationTheory solvableTheory reductionEval;

open horeductionTheory takahashiS3Theory;

val _ = new_theory "boehm";

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];

val o_DEF = combinTheory.o_DEF;

(*---------------------------------------------------------------------------*
 *  Boehm tree
 *---------------------------------------------------------------------------*)

(* The type of Boehm tree:

   For each ltree node, ‘NONE’ represents {\bot} (for unsolvable terms), while
  ‘SOME (vs,y)’ represents ‘LAMl vs (VAR y)’. This separation of vs and y has
   at least two advantages:

   1. ‘set vs’ is the set of binding variables (BV) at that ltree node.
   2. ‘LAMl vs (VAR y)’ can be easily "expanded" (w.r.t. eta reduction) into terms
      such as ‘LAMl (vs ++ [z0;z1]) t’ (with two extra children ‘z0’ and ‘z1’)
      without changing the head variable (VAR y).
 *)
Type boehm_tree[pp] = “:(string list # string) option ltree”

(* Definition 10.1.9 [1, p.221] (Effective Boehm tree)

   NOTE: The setup of ‘X UNION FV M’ when calling ‘FRESH_list’ guarentees that
   the generated Boehm tree is "correct" no matter what X is supplied.

   The word "correct" means that the binding lists of each node in the generated
   Boehm tree do not capture free variables in the children nodes. Thus, if we
   further translate each node from ‘string list # string’ to ‘num # num’ w.r.t.
   de Bruijn encodings, the resulting Boehm tree should be unique for all X.

   2024 UPDATE: Now BT_generator takes (X,M) where X is the initial X. Then,
   for each generating children, the created fresh binding list ‘vs’ at current
   level must be added into X for the next level. This is because the children
   terms may contain free variables in ‘vs’, which was bound (thus not included
   in FV M). When choosing binding variables for the next level, ‘vs’ must be
   avoided too, for a "correct" generation.            -- Chun Tian, 4 gen 2024
 *)
Definition BT_generator_def :
    BT_generator (X,M) =
      if solvable M then
         let M0 = principle_hnf M;
              n = LAMl_size M0;
             vs = FRESH_list n (X UNION FV M);
             M1 = principle_hnf (M0 @* (MAP VAR vs));
             Ms = hnf_children M1;
              l = MAP ($, (X UNION set vs)) Ms;
              y = hnf_headvar M1;
              h = (vs,y)
         in
            (SOME h, fromList l)
      else
            (NONE  , LNIL)
End

Definition BT_def :
    BT = ltree_unfold BT_generator
End

Overload BTe = “\X M. BT (X,M)”

(* BTe is actually the Curry-ized version of BT *)
Theorem BTe_def :
    !X M. BTe X M = CURRY BT X M
Proof
    rw [pairTheory.CURRY_DEF]
QED

(* This is the meaning of Boehm tree nodes, ‘fromNote’ translated from BT nodes
   to lambda terms in form of ‘SOME (LAMl vs (VAR y))’ or ‘NONE’.
 *)
Definition fromNode_def :
    fromNode = OPTION_MAP (\(vs,y). LAMl vs (VAR y))
End

(* Boehm tree of a single (free) variable ‘VAR s’ *)
Definition BT_VAR_def :
    BT_VAR s :boehm_tree = Branch (SOME (NIL,s)) LNIL
End

(* Remarks 10.1.3 (iii) [1, p.216]: unsolvable terms all have the same Boehm
   tree (‘bot’). The following overloaded ‘bot’ may be returned by
  ‘THE (ltree_lookup A p)’ when looking up a terminal node of the Boehm tree.
 *)
Overload bot = “Branch NONE (LNIL :boehm_tree llist)”

(* Another form of ‘bot’, usually returned by “THE (ltree_el A p)”. *)
Overload bot = “(NONE :(string list # string) option, SOME 0)”

(* Unicode name: "base" *)
val _ = Unicode.unicode_version {u = UTF8.chr 0x22A5, tmnm = "bot"};
val _ = TeX_notation {hol = "bot", TeX = ("\\ensuremath{\\bot}", 1)};

(* some easy theorems about Boehm trees of unsolvable terms *)
Theorem BT_of_unsolvables :
    !X M. unsolvable M ==> BTe X M = bot
Proof
    rw [BT_def, BT_generator_def, ltree_unfold, ltree_map]
QED

Theorem BT_of_unsolvables_EQ :
    !X M N. unsolvable M /\ unsolvable N ==> BTe X M = BTe X N
Proof
    rw [BT_of_unsolvables]
QED

Theorem BT_finite_branching :
    !X M. finite_branching (BTe X M)
Proof
    rpt GEN_TAC
 >> irule finite_branching_coind'
 >> Q.EXISTS_TAC ‘\b. ?X M. b = BTe X M’
 >> rw [] >- (qexistsl_tac [‘X’, ‘M’] >> rw [])
 (* stage work *)
 >> qabbrev_tac ‘A = BTe X M’
 >> qabbrev_tac ‘a = ltree_node A’
 >> qabbrev_tac ‘ts = ltree_children A’
 >> qexistsl_tac [‘a’, ‘ts’]
 (* A = Branch a ts *)
 >> CONJ_TAC >- rw [Abbr ‘a’, Abbr ‘ts’]
 (* LFINITE ts *)
 >> CONJ_TAC
 >- rw [Abbr ‘A’, Abbr ‘ts’, BT_def, BT_generator_def, Once ltree_unfold,
        LFINITE_fromList]
 >> qabbrev_tac ‘P = \b. ?X M. b = BTe X M’
 >> rw [Abbr ‘A’, Abbr ‘ts’, BT_def, BT_generator_def, Once ltree_unfold]
 >> rw [every_fromList_EVERY, LMAP_fromList, EVERY_MAP, Abbr ‘P’, EVERY_MEM]
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> qabbrev_tac ‘vs = FRESH_list n (X UNION FV M)’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> rename1 ‘MEM N (hnf_children M1)’
 >> qexistsl_tac [‘X UNION set vs’, ‘N’] >> rw [BT_def]
QED

(* Given a hnf ‘M0’ and a shared binding variable list ‘vs’

   hnf_tac adds the following abbreviation and new assumptions:

   Abbrev (M1 = principle_hnf (M0 @* MAP VAR (TAKE (LAMl_size M0) vs)))
   M0 = LAMl (TAKE (LAMl_size M0) vs) (VAR y @* args)
   M1 = VAR y @* args

   where the names "M1", "y" and "args" can be chosen from inputs.
 *)
fun hnf_tac (M0, vs, M1, y, args) = let
 val n = “LAMl_size ^M0” in
    qabbrev_tac ‘^M1 = principle_hnf (^M0 @* MAP VAR (TAKE ^n ^vs))’
 >> Know ‘?^y ^args. ^M0 = LAMl (TAKE ^n ^vs) (VAR ^y @* ^args)’
 >- (irule (iffLR hnf_cases_shared) >> rw [])
 >> STRIP_TAC
 >> Know ‘^M1 = VAR ^y @* ^args’
 >- (qunabbrev_tac ‘^M1’ \\
     Q.PAT_ASSUM ‘^M0 = LAMl (TAKE ^n ^vs) (VAR ^y @* ^args)’
        (fn th => REWRITE_TAC [Once th]) \\
     MATCH_MP_TAC principle_hnf_beta_reduce >> rw [hnf_appstar])
 >> DISCH_TAC
end;

(* Proposition 10.1.6 [1, p.219] (beta-equivalent terms have the same Boehm tree)

   NOTE: X is an sufficiently large finite set of names covering all FVs of
         M and N. The Boehm trees of M and N are generated with help of this set.

   TODO: this theorem can be improved to an iff: M == N <=> BTe X M = BTe X N
 *)
Theorem lameq_BT_cong :
    !X M N. FINITE X /\ FV M UNION FV N SUBSET X ==>
            M == N ==> BTe X M = BTe X N
Proof
    RW_TAC std_ss []
 >> reverse (Cases_on ‘solvable M’)
 >- (‘unsolvable N’ by METIS_TAC [lameq_solvable_cong] \\
     rw [BT_of_unsolvables])
 >> ‘solvable N’ by METIS_TAC [lameq_solvable_cong]
 (* applying ltree_bisimulation *)
 >> rw [ltree_bisimulation]
 (* NOTE: ‘solvable P /\ solvable Q’ cannot be added into the next relation *)
 >> Q.EXISTS_TAC ‘\x y. ?P Q Y. FINITE Y /\ FV P UNION FV Q SUBSET Y /\
                                P == Q /\ x = BTe Y P /\ y = BTe Y Q’
 >> BETA_TAC
 >> CONJ_TAC >- (qexistsl_tac [‘M’, ‘N’, ‘X’] >> rw [])
 (* stage work *)
 >> qx_genl_tac [‘a1’, ‘ts1’, ‘a2’, ‘ts2’] >> STRIP_TAC
 >> qabbrev_tac ‘P0 = principle_hnf P’
 >> qabbrev_tac ‘Q0 = principle_hnf Q’
 >> qabbrev_tac ‘n  = LAMl_size P0’
 >> qabbrev_tac ‘n' = LAMl_size Q0’
 >> qabbrev_tac ‘vs = FRESH_list n (Y UNION FV P)’
 >> qabbrev_tac ‘vs' = FRESH_list n' (Y UNION FV Q)’
 >> qabbrev_tac ‘P1 = principle_hnf (P0 @* MAP VAR vs)’
 >> qabbrev_tac ‘Q1 = principle_hnf (Q0 @* MAP VAR vs')’
 >> qabbrev_tac ‘Ps = hnf_children P1’
 >> qabbrev_tac ‘Qs = hnf_children Q1’
 >> qabbrev_tac ‘y  = hnf_headvar P1’
 >> qabbrev_tac ‘y' = hnf_headvar Q1’
 (* applying ltree_unfold *)
 >> Q.PAT_X_ASSUM ‘_ = BTe Y Q’ MP_TAC
 >> simp [BT_def, Once ltree_unfold, BT_generator_def]
 >> Q.PAT_X_ASSUM ‘_ = BTe Y P’ MP_TAC
 >> simp [BT_def, Once ltree_unfold, BT_generator_def]
 >> NTAC 2 STRIP_TAC
 (* easy case: unsolvable P (and Q) *)
 >> reverse (Cases_on ‘solvable P’)
 >- (‘unsolvable Q’ by PROVE_TAC [lameq_solvable_cong] >> fs [] \\
     rw [llist_rel_def, LLENGTH_MAP])
 (* now both P and Q are solvable *)
 >> ‘solvable Q’ by PROVE_TAC [lameq_solvable_cong]
 (* clean up definitions of vs and vs' by using ‘FV M UNION FV N SUBSET X’ *)
 >> Know ‘Y UNION FV P = Y /\ Y UNION FV Q = Y’
 >- (Q.PAT_X_ASSUM ‘FV P UNION FV Q SUBSET Y’ MP_TAC >> SET_TAC [])
 >> DISCH_THEN (fs o wrap)
 >> Know ‘n = n' /\ vs = vs'’
 >- (reverse CONJ_ASM1_TAC >- rw [Abbr ‘vs’, Abbr ‘vs'’] \\
     qunabbrevl_tac [‘n’, ‘n'’, ‘P0’, ‘Q0’] \\
     MATCH_MP_TAC lameq_principle_hnf_size_eq' >> art [])
 (* clean up now duplicated abbreviations: n' and vs' *)
 >> qunabbrevl_tac [‘n'’, ‘vs'’]
 >> DISCH_THEN (rfs o wrap o GSYM)
 (* proving y = y' *)
 >> STRONG_CONJ_TAC
 >- (MP_TAC (Q.SPECL [‘Y’, ‘P’, ‘Q’, ‘P0’, ‘Q0’, ‘n’, ‘vs’, ‘P1’, ‘Q1’]
                     lameq_principle_hnf_headvar_eq') >> simp [])
 >> DISCH_THEN (rfs o wrap o GSYM)
 >> qunabbrevl_tac [‘y’, ‘y'’]
 (* applying lameq_principle_hnf_thm' *)
 >> MP_TAC (Q.SPECL [‘Y’, ‘P’, ‘Q’, ‘P0’, ‘Q0’, ‘n’, ‘vs’, ‘P1’, ‘Q1’]
                     lameq_principle_hnf_thm') >> simp []
 >> rw [llist_rel_def, LLENGTH_MAP, EL_MAP]
 >> Cases_on ‘i < LENGTH Ps’ >> fs [LNTH_fromList, EL_MAP]
 >> Q.PAT_X_ASSUM ‘(Y UNION set vs,EL i Ps) = z’  (ONCE_REWRITE_TAC o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘(Y UNION set vs,EL i Qs) = z'’ (ONCE_REWRITE_TAC o wrap o SYM)
 >> qexistsl_tac [‘EL i Ps’, ‘EL i Qs’, ‘Y UNION set vs’] >> simp []
 (* preparing for hnf_children_FV_SUBSET

    Here, once again, we need to get suitable explicit forms of P0 and Q0,
    to show that, P1 and Q1 are absfree hnf.
  *)
 >> ‘hnf P0 /\ hnf Q0’ by PROVE_TAC [hnf_principle_hnf, solvable_iff_has_hnf]
 >> qabbrev_tac ‘n = LAMl_size Q0’
 >> ‘ALL_DISTINCT vs /\ LENGTH vs = n /\ DISJOINT (set vs) Y’
      by rw [Abbr ‘vs’, FRESH_list_def]
 >> Know ‘DISJOINT (set vs) (FV P0)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘Y’ >> art [] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘FV P’ >> art [] \\
     qunabbrev_tac ‘P0’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set vs) (FV Q0)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘Y’ >> art [] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘FV Q’ >> art [] \\
     qunabbrev_tac ‘Q0’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 (* NOTE: the next two hnf_tac will refine P1 and Q1 *)
 >> qunabbrevl_tac [‘P1’, ‘Q1’]
 >> hnf_tac (“P0 :term”, “vs :string list”,
             “P1 :term”, “y  :string”, “args :term list”)
 >> hnf_tac (“Q0 :term”, “vs :string list”,
             “Q1 :term”, “y' :string”, “args' :term list”)
 >> ‘TAKE n vs = vs’ by rw [TAKE_LENGTH_ID_rwt]
 >> POP_ASSUM (rfs o wrap)
 (* refine P1 and Q1 again for clear assumptions using them *)
 >> qunabbrevl_tac [‘P1’, ‘Q1’]
 >> qabbrev_tac ‘P1 = principle_hnf (P0 @* MAP VAR vs)’
 >> qabbrev_tac ‘Q1 = principle_hnf (Q0 @* MAP VAR vs)’
 (* applying hnf_children_FV_SUBSET *)
 >> CONJ_TAC
 >| [ (* goal 1 (of 2) *)
      Know ‘!i. i < LENGTH Ps ==> FV (EL i Ps) SUBSET FV P1’
      >- (MATCH_MP_TAC hnf_children_FV_SUBSET >> rw [Abbr ‘Ps’, hnf_appstar]) \\
      DISCH_TAC \\
      MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV P1’ \\
      CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
      MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV P0 UNION set vs’ \\
      CONJ_TAC >- simp [FV_LAMl] \\
      Suff ‘FV P0 SUBSET Y’ >- SET_TAC [] \\
      MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV P’ \\
      reverse CONJ_TAC >- art [] (* FV P SUBSET Y *) \\
      qunabbrev_tac ‘P0’ >> MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [],
      (* goal 2 (of 2) *)
      Know ‘!i. i < LENGTH Qs ==> FV (EL i Qs) SUBSET FV Q1’
      >- (MATCH_MP_TAC hnf_children_FV_SUBSET >> rw [Abbr ‘Qs’, hnf_appstar]) \\
      DISCH_TAC \\
      MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV Q1’ \\
      CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
      MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV Q0 UNION set vs’ \\
      CONJ_TAC >- simp [FV_LAMl] \\
      Suff ‘FV Q0 SUBSET Y’ >- SET_TAC [] \\
      MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV Q’ \\
      reverse CONJ_TAC >- art [] (* FV Q SUBSET Y *) \\
      qunabbrev_tac ‘Q0’ >> MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [] ]
QED

(*---------------------------------------------------------------------------*
 *  subterm
 *---------------------------------------------------------------------------*)

(* Definition 10.1.13 (iii), ‘subterm’ is the main device connecting Boehm trees
   to Boehm transformations (below).

  ‘subterm X M p’ returns (Y,N) where Y is X enriched with all binding variables
   up to p, and N is the actual subterm.

   NOTE: Similarily with BT_generator, the setup of ‘X UNION FV M’ guarentees
   the correctness of ‘subterm X M’ for whatever X provided, including {}.

   Also, in the recursive call of substerm, ‘X UNION set vs’ is used instead of
   just ‘X’, because ‘vs’ may be free variables in some Ms.
 *)
Definition subterm_def :
    subterm X M []      = SOME (X,M :term) /\
    subterm X M (x::xs) = if solvable M then
        let M0 = principle_hnf M;
             n = LAMl_size M0;
            vs = FRESH_list n (X UNION FV M);
            M1 = principle_hnf (M0 @* (MAP VAR vs));
            Ms = hnf_children M1;
             m = LENGTH Ms
        in
            if x < m then subterm (X UNION set vs) (EL x Ms) xs else NONE
    else
        NONE
End

(* This assumes ‘subterm X M p <> NONE’ *)
Overload subterm' = “\X M p. SND (THE (subterm X M p))”

(* |- !X M. subterm X M [] = SOME M *)
Theorem subterm_NIL[simp] = cj 1 subterm_def

(* Lemma 10.1.15 [1, p.222] *)
Theorem BT_subterm_thm :
    !p X M. p IN ltree_paths (BTe X M) /\ subterm X M p <> NONE ==>
            BT (THE (subterm X M p)) = THE (ltree_lookup (BTe X M) p)
Proof
    Induct_on ‘p’
 >- rw [subterm_def, ltree_lookup_def]
 >> rw [subterm_def, ltree_lookup]
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> qabbrev_tac ‘vs = FRESH_list n (X UNION FV M)’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* (MAP VAR vs))’
 >> qabbrev_tac ‘Ms = hnf_children M1’
 >> Know ‘BTe X M = ltree_unfold BT_generator (X,M)’ >- rw [BT_def]
 >> simp [Once ltree_unfold, BT_generator_def]
 >> DISCH_TAC
 >> simp [LNTH_fromList, EL_MAP]
 >> Q.PAT_X_ASSUM ‘h::p IN ltree_paths (BTe X M)’ MP_TAC
 >> POP_ORW
 >> rw [ltree_paths_def, ltree_lookup_def, LNTH_fromList, GSYM BT_def, EL_MAP]
QED

(* NOTE: In the above theorem, when the antecedents hold, i.e.

         p IN ltree_paths (BTe X M) /\ subterm X M p = NONE

   Then ‘subterm' X M (FRONT p)’ must be an unsolvable term. This result can be
   even improved to an iff, as the present theorem shows.
 *)
Theorem subterm_is_none_iff_parent_unsolvable :
    !p X M. p IN ltree_paths (BTe X M) ==>
           (subterm X M p = NONE <=>
            p <> [] /\ unsolvable (subterm' X M (FRONT p)))
Proof
    Induct_on ‘p’ >> rw [subterm_def] (* 2 subgoals, only one left *)
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> qabbrev_tac ‘vs = FRESH_list n (X UNION FV M)’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* (MAP VAR vs))’
 >> qabbrev_tac ‘Ms = hnf_children M1’
 >> reverse (Cases_on ‘solvable M’)
 >- (rw [] >> Suff ‘p = []’ >- rw [subterm_NIL] \\
     Q.PAT_X_ASSUM ‘h::p IN ltree_paths (BTe X M)’ MP_TAC \\
     simp [BT_of_unsolvables, ltree_paths_def, ltree_lookup_def])
 >> simp []
 (* stage work, now M is solvable *)
 >> Cases_on ‘p = []’
 >- (rw [subterm_NIL] \\
     Q.PAT_X_ASSUM ‘[h] IN ltree_paths (BTe X M)’ MP_TAC \\
     simp [BT_def, Once ltree_unfold, BT_generator_def, ltree_paths_def,
           ltree_lookup_def, LNTH_fromList] \\
     Cases_on ‘h < LENGTH Ms’ >> simp [])
 (* now: p <> [] *)
 >> Know ‘h < LENGTH Ms’
 >- (Q.PAT_X_ASSUM ‘h::p IN ltree_paths (BTe X M)’ MP_TAC \\
     simp [BT_def, Once ltree_unfold, BT_generator_def, ltree_paths_def,
           ltree_lookup_def, LNTH_fromList] \\
     Cases_on ‘h < LENGTH Ms’ >> simp [])
 >> RW_TAC std_ss [FRONT_DEF]
 (* stage work *)
 >> qabbrev_tac ‘N = EL h Ms’
 >> Know ‘subterm X M (h::FRONT p) = subterm (X UNION set vs) N (FRONT p)’
 >- rw [subterm_def]
 >> Rewr'
 >> FULL_SIMP_TAC std_ss []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 (* p IN ltree_paths (BTe X N) *)
 >> Q.PAT_X_ASSUM ‘h::p IN ltree_paths (BTe X M)’ MP_TAC
 >> rw [BT_def, Once ltree_unfold, BT_generator_def, ltree_paths_def,
        ltree_lookup_def, LNTH_fromList, EL_MAP]
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
               vs = FRESH_list (MAX n n') (FV M0 UNION FV N0);
              vsM = TAKE n  vs;
              vsN = TAKE n' vs;
               M1 = principle_hnf (M0 @* (MAP VAR vsM));
               N1 = principle_hnf (N0 @* (MAP VAR vsN));
               y  = hnf_head M1;
               y' = hnf_head N1;
               m  = LENGTH (hnf_children M1);
               m' = LENGTH (hnf_children N1);
           in
               y = y' /\ n + m' = n' + m
        else
           ~solvable M /\ ~solvable N
End

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
              vs = FRESH_list (MAX n n') (FV M0 UNION FV N0);
             vsM = TAKE n  vs;
             vsN = TAKE n' vs;
              M1 = principle_hnf (M0 @* (MAP VAR vsM));
              N1 = principle_hnf (N0 @* (MAP VAR vsN));
              y  = hnf_head M1;
              y' = hnf_head N1;
              m  = LENGTH (hnf_children M1);
              m' = LENGTH (hnf_children N1);
           in
              y = y' /\ n + m' = n' + m)
Proof
    RW_TAC std_ss [equivalent_def]
QED

(* NOTE: the initial calls of ‘principle_hnf’ get eliminated if the involved
         terms are already in head normal forms.
 *)
Theorem equivalent_of_hnf :
    !M N. hnf M /\ hnf N ==>
         (equivalent M N <=>
          let n  = LAMl_size M;
              n' = LAMl_size N;
              vs = FRESH_list (MAX n n') (FV M UNION FV N);
             vsM = TAKE n  vs;
             vsN = TAKE n' vs;
              M1 = principle_hnf (M @* (MAP VAR vsM));
              N1 = principle_hnf (N @* (MAP VAR vsN));
              y  = hnf_head M1;
              y' = hnf_head N1;
              m  = LENGTH (hnf_children M1);
              m' = LENGTH (hnf_children N1);
           in
              y = y' /\ n + m' = n' + m)
Proof
    rpt STRIP_TAC
 >> ‘solvable M /\ solvable N’ by PROVE_TAC [hnf_has_hnf, solvable_iff_has_hnf]
 >> RW_TAC std_ss [equivalent_def, principle_hnf_reduce]
 >> METIS_TAC []
QED

(* The following combined tactic is useful after:

   RW_TAC std_ss [equivalent_of_solvables, principle_hnf_reduce]

   NOTE: it doesn't work with equivalent_of_hnf
 *)
val equivalent_tac =
    ‘hnf M0 /\ hnf N0’ by PROVE_TAC [hnf_principle_hnf, solvable_iff_has_hnf]
 >> ‘ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M0 UNION FV N0) /\
     LENGTH vs = MAX n n'’ by rw [Abbr ‘vs’, FRESH_list_def]
 >> ‘DISJOINT (set vs) (FV M0) /\ DISJOINT (set vs) (FV N0)’
      by METIS_TAC [DISJOINT_SYM, DISJOINT_UNION]
 >> qunabbrevl_tac [‘M1’, ‘N1’]
 >> hnf_tac (“M0 :term”, “vs :string list”,
             “M1 :term”, “y1 :string”, “args1 :term list”)
 >> hnf_tac (“N0 :term”, “vs :string list”,
             “N1 :term”, “y2 :string”, “args2 :term list”)
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
 >> ‘VAR y2 = y'’ by rw [Abbr ‘y'’, absfree_hnf_head];

(* From [1, p.238]. This concerte example shows that dB encoding is not easy in
   defining this "concept": the literal encoding of inner head variables are not
   the same for equivalent terms.
 *)
Theorem not_equivalent_example :
    !x y. x <> y ==> ~equivalent (LAM x (VAR y @@ M)) (LAM y (VAR y @@ M))
Proof
 (* NOTE: ‘y’ must avoid here for the shared equivalent_tac *)
    qx_genl_tac [‘x’, ‘v’] >> DISCH_TAC
 >> ‘hnf (LAM x (VAR v @@ M)) /\ hnf (LAM v (VAR v @@ M))’ by rw []
 >> ‘solvable (LAM x (VAR v @@ M)) /\ solvable (LAM v (VAR v @@ M))’
       by rw [solvable_iff_has_hnf, hnf_has_hnf]
 >> RW_TAC std_ss [equivalent_of_solvables, principle_hnf_reduce]
 (* applying shared tactics *)
 >> equivalent_tac
 >> qunabbrevl_tac [‘n’, ‘n'’]
 >> Know ‘LAMl_size M0 = 1 /\ LAMl_size N0 = 1’
 >- (rw [Abbr ‘M0’, Abbr ‘N0’, LAMl_size_def])
 >> DISCH_THEN (rfs o wrap)
 >> qabbrev_tac ‘z = HD vs’
 >> ‘vs = [z]’ by METIS_TAC [SING_HD]
 >> Q.PAT_X_ASSUM ‘vsN = vsM’ (rfs o wrap o SYM)
 >> rfs [Abbr ‘vsN’]
 >> POP_ASSUM (rfs o wrap)
 >> qunabbrevl_tac [‘M0’, ‘N0’]
 >> DISJ1_TAC
 >> qunabbrevl_tac [‘y’, ‘y'’]
 (* applying principle_hnf_beta *)
 >> qabbrev_tac ‘t = VAR v @@ M’
 >> ‘hnf t’ by rw [Abbr ‘t’]
 >> Know ‘M1 = [VAR z/x] t’
 >- (qunabbrev_tac ‘M1’ \\
     Cases_on ‘z = x’ >- POP_ASSUM (rfs o wrap) \\
     MATCH_MP_TAC principle_hnf_beta >> simp [Abbr ‘t’] \\
     rfs [FV_thm])
 >> Rewr'
 >> Know ‘N1 = [VAR z/v] t’
 >- (qunabbrev_tac ‘N1’ \\
     Cases_on ‘z = v’ >- POP_ASSUM (rfs o wrap) \\
     MATCH_MP_TAC principle_hnf_beta >> simp [Abbr ‘t’] \\
     rfs [FV_thm])
 >> Rewr'
 >> simp [Abbr ‘t’]
 (* final goal: y <> z *)
 >> Q.PAT_X_ASSUM ‘z # LAM x (VAR v @@ M)’ MP_TAC
 >> rw [FV_thm]
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

(* Definition 10.3.2 [1, p.246] *)
val _ = set_fixity "is_substitution_instance_of" (Infixr 490);

(* NOTE: ‘(DOM phi) SUBSET (FV M)’ is not necessary *)
Definition is_substitution_instance_of :
    N is_substitution_instance_of M <=> ?phi. N = M ISUB phi
End

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
Definition apply_def :
    apply pi = FOLDR $o I pi
End

(* NOTE: either FOLDL or FOLDR is correct (due to combinTheory.o_ASSOC),
         but FOLDR seems more natural requiring natural list induction in
         the next proof(s), while FOLDL would require SNOC_INDUCT.
 *)
Theorem apply_alt :
    !pi. apply pi = FOLDL $o I pi
Proof
    REWRITE_TAC [apply_def]
 >> Induct_on ‘pi’ >> rw [FOLDL, FOLDR]
 >> KILL_TAC (* only FOLDL is left *)
 >> Induct_on ‘pi’ using SNOC_INDUCT
 >> rw [FOLDL_SNOC, FOLDL]
 >> POP_ASSUM (rw o wrap o SYM)
QED

Theorem apply_rwts[simp] :
    (apply [] = I) /\
    (!f pi M. apply (f::pi) M = f (apply pi M)) /\
    (!f pi M. apply (SNOC f pi) M = apply pi (f M))
Proof
    NTAC 2 (CONJ_TAC >- rw [apply_def, o_DEF])
 >> rw [apply_alt, o_DEF, FOLDL_SNOC]
QED

(* Lemma 10.3.4 (i) [1, p.246] *)
Theorem Boehm_transform_lameq_ctxt :
    !pi. Boehm_transform pi ==> ?c. ctxt c /\ !M. apply pi M == c M
Proof
    Induct_on ‘pi’
 >> rw [Boehm_transform_def, apply_def]
 >- (Q.EXISTS_TAC ‘\x. x’ >> rw [ctxt_rules, FOLDR])
 >> fs [GSYM Boehm_transform_def, apply_def]
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

(* Lemma 10.3.4 (ii) [1, p.246]

   Used by: Boehm_transform_lameq_appstar
 *)
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

(* An corollary of the above lemma with ‘xs = {}’

   Used by: closed_separability_thm
 *)
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

(* Used by: distinct_benf_imp_inconsistent *)
Theorem asmlam_apply_cong :
    !pi M N. Boehm_transform pi /\ asmlam eqns M N ==>
             asmlam eqns (apply pi M) (apply pi N)
Proof
    Induct_on ‘pi’ using SNOC_INDUCT >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> fs [solving_transform_def]
 >- rw [asmlam_rules]
 >> MATCH_MP_TAC asmlam_subst >> art []
QED

(* Used by: separability_lemma2 *)
Theorem lameq_apply_cong :
    !pi M N. Boehm_transform pi /\ M == N ==> apply pi M == apply pi N
Proof
    Induct_on ‘pi’ using SNOC_INDUCT >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> MATCH_MP_TAC solving_transform_lameq >> art []
QED

(* Used by separability_thm *)
Theorem Boehm_transform_APPEND :
    !p1 p2. Boehm_transform p1 /\ Boehm_transform p2 ==> Boehm_transform (p1 ++ p2)
Proof
    rw [Boehm_transform_def]
QED

(* Used by separability_thm *)
Theorem Boehm_apply_APPEND :
    !p1 p2 M. apply (p1 ++ p2) M = apply p1 (apply p2 M)
Proof
    Q.X_GEN_TAC ‘p1’
 >> Induct_on ‘p2’ using SNOC_INDUCT
 >> rw [APPEND_SNOC]
QED

(* Used by separability_lemma2 *)
Theorem Boehm_apply_MAP_rightctxt :
    !Ns t. apply (MAP rightctxt Ns) t = t @* (REVERSE Ns)
Proof
    Induct_on ‘Ns’ >> rw [rightctxt_thm]
 >> rw [GSYM SNOC_APPEND]
QED

(* Used by separability_lemma0 *)
Theorem Boehm_apply_MAP_rightctxt' :
    !Ns t. apply (MAP rightctxt (REVERSE Ns)) t = t @* Ns
Proof
    rpt GEN_TAC
 >> qabbrev_tac ‘Ns' = REVERSE Ns’
 >> ‘Ns = REVERSE Ns'’ by rw [Abbr ‘Ns'’, REVERSE_REVERSE]
 >> rw [Boehm_apply_MAP_rightctxt]
QED

(* Used by separability_lemma2 *)
Theorem Boehm_apply_unsolvable :
    !pi M. Boehm_transform pi /\ unsolvable M ==> unsolvable (apply pi M)
Proof
    Induct_on ‘pi’ using SNOC_INDUCT >> rw []
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
    head_original M0 = let n = LAMl_size M0;
                          vs = FRESH_list n (FV M0);
                          M1 = principle_hnf (M0 @* MAP VAR vs);
                       in
                          EVERY (\e. hnf_headvar M1 # e) (hnf_children M1)
End

(* Definition 10.3.5 (iii)

   NOTE: |- has_hnf M <=> ?N. M == N /\ hnf N
 *)
Definition is_ready_def :
    is_ready M <=> unsolvable M \/
                   ?N. M == N /\ hnf N /\ ~is_abs N /\ head_original N
End

(* cf. NEW_TAC (This is the multivariate version)

   NOTE: “FINITE X” must be present in the assumptions or provable by rw [].
 *)
fun FRESH_list_tac (vs,n,X) =
    qabbrev_tac ‘^vs = FRESH_list ^n ^X’
 >> KNOW_TAC “ALL_DISTINCT ^vs /\ DISJOINT (set ^vs) ^X /\ LENGTH ^vs = ^n”
 >- rw [FRESH_list_def, Abbr ‘^vs’]
 >> STRIP_TAC;

(* NOTE: This alternative definition of ‘is_ready’ consumes ‘head_original’
         and eliminated the ‘principle_hnf’ inside it.
 *)
Theorem is_ready_alt :
    !M. is_ready M <=>
        unsolvable M \/ ?y Ns. M == VAR y @* Ns /\ EVERY (\e. y # e) Ns
Proof
    Q.X_GEN_TAC ‘M’
 >> reverse EQ_TAC
 >- (rw [is_ready_def] >- art [] \\
     DISJ2_TAC >> Q.EXISTS_TAC ‘VAR y @* Ns’ >> art [] \\
     CONJ_ASM1_TAC >- (rw [hnf_appstar]) >> simp [] \\
     RW_TAC std_ss [head_original_def, LAMl_size_hnf_absfree] \\
     qunabbrev_tac ‘n’ \\
    ‘vs = []’ by METIS_TAC [LENGTH_NIL, FRESH_list_def, FINITE_FV] \\
     POP_ASSUM (fs o wrap) >> qunabbrev_tac ‘vs’ \\
    ‘M1 = VAR y @* Ns’ by rw [principle_hnf_reduce, Abbr ‘M1’] \\
     POP_ORW >> qunabbrev_tac ‘M1’ \\
     simp [hnf_head_hnf, hnf_children_hnf])
 (* stage work *)
 >> rw [is_ready_def] >- art []
 >> DISJ2_TAC
 >> qabbrev_tac ‘n = LAMl_size N’
 >> FRESH_list_tac (“vs :string list”, “n :num”, “FV (N :term)”)
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

(* Lemma 10.3.6 (i) [1, p.247] *)
Theorem Boehm_transform_exists_lemma1 :
    !M. ?pi. Boehm_transform pi /\ is_ready (apply pi M)
Proof
    Q.X_GEN_TAC ‘M’
 >> reverse (Cases_on ‘solvable M’)
 >- (Q.EXISTS_TAC ‘[]’ >> rw [is_ready_def])
 (* now M is solvable *)
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> ‘hnf M0’ by PROVE_TAC [hnf_principle_hnf, solvable_iff_has_hnf]
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> qabbrev_tac ‘vs = FRESH_list n (FV M0)’
 >> ‘ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M0) /\ LENGTH vs = n’
       by (rw [Abbr ‘vs’, FRESH_list_def])
 (* applying the shared hnf_tac *)
 >> hnf_tac (“M0 :term”, “vs :string list”,
             “M1 :term”, “y :string”, “args :term list”)
 >> ‘TAKE (LAMl_size M0) vs = vs’ by rw []
 >> POP_ASSUM (REV_FULL_SIMP_TAC std_ss o wrap)
 >> qabbrev_tac ‘xs :term list = MAP VAR vs’
 >> qabbrev_tac ‘p1 = MAP rightctxt (REVERSE xs)’
 >> ‘apply p1 M0 == M1’
       by (rw [Abbr ‘p1’, Boehm_apply_MAP_rightctxt', Abbr ‘xs’])
 >> qabbrev_tac ‘m = LENGTH args’
 (* X collects all free variables in ‘args’ *)
 >> qabbrev_tac ‘X = BIGUNION (IMAGE FV (set args))’
 >> Know ‘FINITE X’
 >- (qunabbrev_tac ‘X’ \\
     MATCH_MP_TAC FINITE_BIGUNION >> rw [] >> rw [])
 >> DISCH_TAC
 (* Z needs to avoid any free variables in args' *)
 >> FRESH_list_tac (“Z :string list”, “(m + 1) :num”, “X :string set”)
 >> ‘Z <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> qabbrev_tac ‘z = LAST Z’
 >> ‘MEM z Z’ by rw [Abbr ‘z’, MEM_LAST_NOT_NIL]
 (* P is a permutator *)
 >> qabbrev_tac ‘P = LAMl Z (VAR z @* MAP VAR (FRONT Z))’
 >> Know ‘FV P = {}’
 >- (rw [Abbr ‘P’, FV_LAMl] \\
     Suff ‘FV (VAR z @* MAP VAR (FRONT Z)) SUBSET set Z’ >- SET_TAC [] \\
     rw [FV_appstar, SUBSET_DEF, MEM_MAP] >- art [] \\
     rfs [MEM_FRONT_NOT_NIL])
 >> DISCH_TAC
 >> qabbrev_tac ‘p2 = [[P/y]]’
 >> ‘apply p2 M1 = P @* MAP [P/y] args’ by (rw [Abbr ‘p2’, appstar_SUB])
 >> qabbrev_tac ‘args' = MAP [P/y] args’
 >> ‘!i. i < m ==> FV (EL i args') SUBSET FV (EL i args)’
         by rw [Abbr ‘args'’, EL_MAP, FV_SUB]
 >> ‘LENGTH args' = m’ by rw [Abbr ‘args'’, Abbr ‘m’]
  (* Key: “args'” has less free variables than “args” *)
 >> Know ‘BIGUNION (IMAGE FV (set args')) SUBSET
          BIGUNION (IMAGE FV (set args))’
 >- (rw [SUBSET_DEF, IN_BIGUNION_IMAGE, MEM_EL] \\
     Q.EXISTS_TAC ‘EL n args’ \\
     CONJ_TAC >- (Q.EXISTS_TAC ‘n’ >> art []) \\
     POP_ASSUM MP_TAC \\
     Suff ‘FV (EL n args') SUBSET FV (EL n args)’ >- METIS_TAC [SUBSET_DEF] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> DISCH_TAC
 (* a needs to avoid any free variables in args' *)
 >> NEW_TAC "a" “X :string set”
 >> qabbrev_tac ‘p3 = [rightctxt (VAR a)]’
 >> Know ‘apply p3 (P @* args') == VAR a @* args'’
 >- (rw [Abbr ‘p3’, Abbr ‘P’, rightctxt_thm] \\
    ‘!t. LAMl Z t = LAMl (SNOC z (FRONT Z)) t’
         by (ASM_SIMP_TAC std_ss [Abbr ‘z’, SNOC_LAST_FRONT]) >> POP_ORW \\
     REWRITE_TAC [LAMl_SNOC] \\
     qabbrev_tac ‘t = LAM z (VAR z @* MAP VAR (FRONT Z))’ \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘LAM z (VAR z @* args') @@ VAR a’ \\
  (* applying lameq_LAMl_appstar_ssub *)
     CONJ_TAC
     >- (MATCH_MP_TAC lameq_APPL \\
         Suff ‘LAM z (VAR z @* args') = (FEMPTY |++ ZIP (FRONT Z,args')) ' t’
         >- (Rewr' >> MATCH_MP_TAC lameq_LAMl_appstar_ssub \\
             CONJ_TAC >- rw [ALL_DISTINCT_FRONT] \\
             CONJ_TAC >- rw [LENGTH_FRONT] \\
             ONCE_REWRITE_TAC [DISJOINT_SYM] \\
             MATCH_MP_TAC DISJOINT_SUBSET >> Q.EXISTS_TAC ‘set Z’ \\
             reverse CONJ_TAC >- rw [SUBSET_DEF, MEM_FRONT_NOT_NIL] \\
             ASM_SIMP_TAC std_ss [Once DISJOINT_SYM, Abbr ‘X’] \\
             MATCH_MP_TAC DISJOINT_SUBSET \\
             Q.EXISTS_TAC ‘BIGUNION (IMAGE FV (set args))’ >> art []) \\
         qunabbrev_tac ‘t’ \\
         qabbrev_tac ‘fm = FEMPTY |++ ZIP (FRONT Z,args')’ \\
        ‘LENGTH (FRONT Z) = LENGTH args'’ by rw [LENGTH_FRONT] \\
        ‘FDOM fm = set (FRONT Z)’ by rw [Abbr ‘fm’, FDOM_FUPDATE_LIST, MAP_ZIP] \\
         Know ‘z NOTIN FDOM fm’
         >- (rw [Abbr ‘z’] \\
             Know ‘ALL_DISTINCT (SNOC (LAST Z) (FRONT Z))’
             >- rw [SNOC_LAST_FRONT] \\
             rw [ALL_DISTINCT_SNOC]) >> DISCH_TAC \\
         qabbrev_tac ‘t = VAR z @* MAP VAR (FRONT Z)’ \\
         qabbrev_tac ‘L = ZIP (FRONT Z,args')’ \\
         Know ‘!n. n < LENGTH args' ==> (FEMPTY |++ L) ' (EL n (FRONT Z)) = EL n args'’
         >- (rpt STRIP_TAC \\
             MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM \\
             Q.EXISTS_TAC ‘n’ >> rw [Abbr ‘L’, MAP_ZIP] \\
            ‘m <> n’ by rw [] \\
            ‘ALL_DISTINCT (FRONT Z)’ by METIS_TAC [ALL_DISTINCT_FRONT] \\
             METIS_TAC [EL_ALL_DISTINCT_EL_EQ]) >> DISCH_TAC \\
         Know ‘fm ' (LAM z t) = LAM z (fm ' t)’
         >- (MATCH_MP_TAC ssub_LAM >> art [] \\
             rw [Abbr ‘fm’, FDOM_FUPDATE_LIST, MAP_ZIP, MEM_EL] \\
             Know ‘(FEMPTY |++ L) ' (EL n (FRONT Z)) = EL n args'’
             >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr' \\
             Suff ‘z # EL n args’
             >- (DISCH_TAC >> CCONTR_TAC >> fs [] >> METIS_TAC [SUBSET_DEF]) \\
             CCONTR_TAC >> fs [] \\
             Q.PAT_X_ASSUM ‘DISJOINT (set Z) X’ MP_TAC \\
             rw [DISJOINT_ALT, Abbr ‘X’] \\
             Q.EXISTS_TAC ‘FV (EL n args)’ \\
             CONJ_TAC >- (Q.EXISTS_TAC ‘EL n args’ >> rw [MEM_EL] \\
                          Q.EXISTS_TAC ‘n’ >> rw []) \\
             Q.EXISTS_TAC ‘z’ >> rw [MEM_LAST_NOT_NIL, Abbr ‘z’]) >> Rewr' \\
         simp [Abbr ‘t’, ssub_appstar] \\
         simp [Once LIST_EQ_REWRITE] \\
         Q.X_GEN_TAC ‘i’ \\
         Q.PAT_X_ASSUM ‘LENGTH args = LENGTH args'’ K_TAC \\
         REWRITE_TAC [MAP_MAP_o] \\
         DISCH_TAC >> ‘i < LENGTH (FRONT Z)’ by rw [] \\
         ASM_SIMP_TAC std_ss [EL_MAP] \\
        ‘MEM (EL i (FRONT Z)) (FRONT Z)’ by METIS_TAC [MEM_EL] \\
         rw [Abbr ‘fm’, ssub_thm]) \\
     Suff ‘VAR a @* args' = [VAR a/z](VAR z @* args')’
     >- (Rewr' >> rw [lameq_BETA]) \\
     rw [appstar_SUB] \\
     rw [Once LIST_EQ_REWRITE] >> rename1 ‘n < LENGTH args'’ \\
     rw [EL_MAP] \\
     MATCH_MP_TAC (GSYM lemma14b) \\
     Know ‘DISJOINT (set Z) (BIGUNION (IMAGE FV (set args')))’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘X’ >> rw [Abbr ‘X’]) \\
     rw [DISJOINT_ALT] >> FIRST_X_ASSUM irule >> art [] \\
     Q.EXISTS_TAC ‘EL n args'’ >> rw [MEM_EL] \\
     Q.EXISTS_TAC ‘n’ >> art [])
 >> DISCH_TAC
 (* final stage *)
 >> Q.EXISTS_TAC ‘p3 ++ p2 ++ p1’
 >> CONJ_ASM1_TAC
 >- (MATCH_MP_TAC Boehm_transform_APPEND \\
     reverse CONJ_TAC
     >- (rw [Abbr ‘p1’, Abbr ‘xs’, MAP_MAP_o, GSYM MAP_REVERSE]) \\
     MATCH_MP_TAC Boehm_transform_APPEND >> rw [Abbr ‘p2’, Abbr ‘p3’])
 (* applying is_ready_alt *)
 >> simp [is_ready_alt]
 >> DISJ2_TAC
 >> qexistsl_tac [‘a’, ‘args'’]
 >> reverse CONJ_TAC
 >- (rw [EVERY_MEM] \\
     Suff ‘FV e SUBSET X’ >- METIS_TAC [SUBSET_DEF] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘BIGUNION (IMAGE FV (set args'))’ \\
     reverse CONJ_TAC >- rw [Abbr ‘X’] \\
     rw [SUBSET_DEF, IN_BIGUNION_IMAGE] \\
     Q.EXISTS_TAC ‘e’ >> art [])
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘apply (p3 ++ p2 ++ p1) M0’
 >> CONJ_TAC
 >- (MATCH_MP_TAC lameq_apply_cong \\
     CONJ_TAC >- art [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC lameq_SYM \\
     MATCH_MP_TAC lameq_principle_hnf_reduce' >> art [])
 >> ONCE_REWRITE_TAC [Boehm_apply_APPEND]
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘apply (p3 ++ p2) M1’
 >> CONJ_TAC
 >- (MATCH_MP_TAC lameq_apply_cong >> art [] \\
     MATCH_MP_TAC Boehm_transform_APPEND >> rw [Abbr ‘p2’, Abbr ‘p3’])
 >> REWRITE_TAC [Boehm_apply_APPEND]
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘apply p3 (P @* args')’ >> art []
 >> MATCH_MP_TAC lameq_apply_cong
 >> rw [Abbr ‘p3’]
QED

(*---------------------------------------------------------------------------*
 *  Separability of terms
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
 >> qabbrev_tac ‘vs = FRESH_list (k + 1) (y INSERT FV P UNION FV Q)’
 >> ‘ALL_DISTINCT vs /\ DISJOINT (set vs) (y INSERT FV P UNION FV Q)’
      by rw [Abbr ‘vs’, FRESH_list_def]
 >> qabbrev_tac ‘a = HD vs’
 >> qabbrev_tac ‘bs = DROP 1 vs’
 >> Know ‘LENGTH bs + 1 = LENGTH vs /\ 1 < LENGTH vs’
 >- (‘LENGTH vs = k + 1’ by rw [Abbr ‘vs’, FRESH_list_def] \\
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
 >> qabbrev_tac ‘Z = FRESH_list (p + 1) {}’
 >> ‘ALL_DISTINCT Z /\ LENGTH Z = p + 1’ by rw [Abbr ‘Z’, FRESH_list_def]
 >> ‘Z <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> qabbrev_tac ‘z = LAST Z’
 >> qabbrev_tac ‘p2 = [[LAMl Z (VAR z)/y]]’
 >> ‘Boehm_transform p2’ by rw [Boehm_transform_def, Abbr ‘p2’]
 >> Know ‘apply p2 (VAR y @* (args1 ++ MAP VAR vs)) == VAR a @* MAP VAR bs’
 >- (simp [Abbr ‘p2’, appstar_SUB] \\
     Know ‘MAP [LAMl Z (VAR z)/y] (MAP VAR vs) = MAP VAR vs’
     >- (rw [LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC lemma14b \\
         Q.PAT_X_ASSUM ‘DISJOINT (set vs) _’ (MP_TAC o (ONCE_REWRITE_RULE [DISJOINT_SYM])) \\
         rw [DISJOINT_ALT, MEM_EL] >> METIS_TAC []) >> Rewr' \\
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
     rw [GSYM I_alt] \\
     MATCH_MP_TAC lameq_appstar_cong >> rw [lameq_I])
 >> DISCH_TAC
 >> qabbrev_tac ‘b0 = LAST bs’
 >> Know ‘apply p2 (VAR y @* (args2 ++ MAP VAR vs)) == VAR b0’
 >- (simp [Abbr ‘p2’, appstar_SUB] \\
     Know ‘MAP [LAMl Z (VAR z)/y] (MAP VAR vs) = MAP VAR vs’
     >- (rw [LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC lemma14b \\
         Q.PAT_X_ASSUM ‘DISJOINT (set vs) _’ (MP_TAC o (ONCE_REWRITE_RULE [DISJOINT_SYM])) \\
         rw [DISJOINT_ALT, MEM_EL] >> METIS_TAC []) >> Rewr' \\
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
             MATCH_MP_TAC (GSYM SNOC_LAST_FRONT) >> rw [Abbr ‘l’]) \\
         MATCH_MP_TAC (GSYM LAST_APPEND_NOT_NIL) >> rw []) >> Rewr' \\
     REWRITE_TAC [appstar_SNOC] \\
     qabbrev_tac ‘t :term = LAM z (VAR z)’ \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘t @@ VAR b0’ \\
     CONJ_TAC >- (MATCH_MP_TAC lameq_APPL \\
                  MATCH_MP_TAC lameq_LAMl_appstar_reduce \\
                  rw [Abbr ‘t’, Abbr ‘args2'’, LENGTH_FRONT] \\
                 ‘LENGTH vs = k + 1’ by rw [Abbr ‘vs’, FRESH_list_def] >> rw []) \\
     rw [Abbr ‘t’, GSYM I_alt, lameq_I])
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
      CONJ_TAC >- (MATCH_MP_TAC lameq_apply_cong >> art []) \\
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
      MATCH_MP_TAC lameq_apply_cong >> art [] ]
QED

Theorem separability_lemma0[local] :
    !M N. solvable (M :term) /\ solvable N /\
          LAMl_size (principle_hnf M) <= LAMl_size (principle_hnf N) ==>
          equivalent M N \/
          !P Q. ?pi. Boehm_transform pi /\ apply pi M == P /\ apply pi N == Q
Proof
    RW_TAC std_ss [equivalent_of_solvables]
 (* applying the shared equivalent_tac *)
 >> equivalent_tac
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

     NOTE: This Z = [z1;z2] contains two fresh variables fixing the textbook proof,
           where [1, p.254] the iterated substition "[LAMl as P/y1] [LAMl as' Q/y2]"
           must be fixed to act as a simultaneous substitition:

       [LAMl as [VAR z2/y2]P/y1] [LAMl as' [VAR z1/y1]Q/y2] [VAR y1/z1] [VAR y2/z2]
   *)
     qabbrev_tac ‘Z = FRESH_list 2 (FV P UNION FV Q)’ \\
    ‘ALL_DISTINCT Z /\ DISJOINT (set Z) (FV P UNION FV Q) /\ LENGTH Z = 2’
       by rw [FRESH_list_def, Abbr ‘Z’] \\
     qabbrev_tac ‘z1 = EL 0 Z’ \\
     qabbrev_tac ‘z2 = EL 1 Z’ \\
    ‘MEM z1 Z /\ MEM z2 Z’
       by (rw [MEM_EL, Abbr ‘z1’, Abbr ‘z2’] >| (* 2 subgoals *)
           [ Q.EXISTS_TAC ‘0’ >> rw [],
             Q.EXISTS_TAC ‘1’ >> rw [] ]) \\
    ‘z1 <> z2’ by (rw [Abbr ‘z1’, Abbr ‘z2’, ALL_DISTINCT_EL_IMP]) \\
     qabbrev_tac ‘as = FRESH_list (m + k) (FV P UNION set Z)’ \\
    ‘LENGTH as = m + k /\ DISJOINT (set as) (FV P UNION set Z)’
       by rw [Abbr ‘as’, FRESH_list_def] \\
     qabbrev_tac ‘as' = FRESH_list m' (FV Q UNION set Z)’ \\
    ‘LENGTH as' = m' /\ DISJOINT (set as') (FV Q UNION set Z)’
       by rw [Abbr ‘as'’, FRESH_list_def] \\
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
         Cases_on ‘y2 IN FV P’ >> rw [SUBSET_DEF, Abbr ‘z2’] >> art []) \\
     DISCH_TAC \\
     Know ‘DISJOINT (set as') (FV ([VAR z1/y1] Q))’
     >- (MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘FV Q UNION set Z’ >> art [] \\
         simp [FV_SUB] \\
         Cases_on ‘y1 IN FV Q’ >> rw [SUBSET_DEF, Abbr ‘z2’] >> art []) \\
     DISCH_TAC \\
  (* stage work *)
     Q.EXISTS_TAC ‘p1 ++ p0’ \\
     CONJ_ASM1_TAC >- rw [Boehm_transform_APPEND] \\
     reverse CONJ_TAC >| (* 2 subgoals, Q part seems easier *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply (p1 ++ p0) N0’ \\
       CONJ_TAC >- (MATCH_MP_TAC lameq_apply_cong >> POP_ASSUM (REWRITE_TAC o wrap) \\
                    qunabbrev_tac ‘N0’ >> MATCH_MP_TAC lameq_SYM \\
                    MATCH_MP_TAC lameq_principle_hnf_reduce >> art [GSYM solvable_iff_has_hnf]) \\
    (* eliminating p0 *)
       REWRITE_TAC [Boehm_apply_APPEND] \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply p1 N1’ \\
       CONJ_TAC >- (MATCH_MP_TAC lameq_apply_cong >> art []) \\
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
       CONJ_TAC >- (MATCH_MP_TAC lameq_apply_cong >> POP_ASSUM (REWRITE_TAC o wrap) \\
                    qunabbrev_tac ‘M0’ \\
                    MATCH_MP_TAC lameq_SYM \\
                    MATCH_MP_TAC lameq_principle_hnf_reduce >> art [GSYM solvable_iff_has_hnf]) \\
    (* eliminating p0 *)
       REWRITE_TAC [Boehm_apply_APPEND] \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply p1 (M1 @* DROP n (MAP VAR vs))’ \\
       CONJ_TAC >- (MATCH_MP_TAC lameq_apply_cong >> art []) \\
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
           MATCH_MP_TAC lemma14b >> rw [FV_SUB] \\
           CCONTR_TAC >> ‘MEM y2 Z’ by METIS_TAC [] \\
           Q.PAT_X_ASSUM ‘DISJOINT (set Z) (FV P UNION FV Q)’
               (MP_TAC o ONCE_REWRITE_RULE [DISJOINT_SYM]) \\
           rw [DISJOINT_ALT] >> METIS_TAC []) >> Rewr' \\
    (* eliminating f3 *)
       Know ‘f3 ([VAR z2/y2] P) = [VAR z2/y2] P’
       >- (qunabbrev_tac ‘f3’ \\
           MATCH_MP_TAC lemma14b \\
           Suff ‘z1 # P’ >- rw [FV_SUB] \\
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
      MP_TAC (Q.SPECL [‘y2’, ‘args1'’, ‘args2’, ‘l - m'’] separability_lemma0_case2) \\
      simp [] \\
      DISCH_THEN (STRIP_ASSUME_TAC o (Q.SPECL [‘P’, ‘Q’])),
      (* goal 2 (of 2) *)
      MP_TAC (Q.SPECL [‘y2’, ‘args2’, ‘args1'’, ‘m' - l’] separability_lemma0_case2) \\
      simp [] \\
      DISCH_THEN (STRIP_ASSUME_TAC o (Q.SPECL [‘Q’, ‘P’])) ]
 (* shared tactics *)
 >> (Q.EXISTS_TAC ‘pi ++ p0’ \\
     CONJ_ASM1_TAC >- rw [Boehm_transform_APPEND] \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1.1 (of 2) *)
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply (pi ++ p0) M0’ \\
       CONJ_TAC >- (MATCH_MP_TAC lameq_apply_cong >> POP_ASSUM (REWRITE_TAC o wrap) \\
                    qunabbrev_tac ‘M0’ >> MATCH_MP_TAC lameq_SYM \\
                    MATCH_MP_TAC lameq_principle_hnf_reduce \\
                    ASM_REWRITE_TAC [GSYM solvable_iff_has_hnf]) \\
       REWRITE_TAC [Boehm_apply_APPEND] \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply pi (y' @* args1')’ \\
       reverse CONJ_TAC >- art [] \\
       MATCH_MP_TAC lameq_apply_cong \\
       Q.PAT_X_ASSUM ‘VAR y2 = y'’ (ONCE_REWRITE_TAC o wrap o SYM) >> art [],
       (* goal 1.2 (of 2) *)
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply (pi ++ p0) N0’ \\
       CONJ_TAC >- (MATCH_MP_TAC lameq_apply_cong >> POP_ASSUM (REWRITE_TAC o wrap) \\
                    qunabbrev_tac ‘N0’ >> MATCH_MP_TAC lameq_SYM \\
                    MATCH_MP_TAC lameq_principle_hnf_reduce \\
                    ASM_REWRITE_TAC [GSYM solvable_iff_has_hnf]) \\
       REWRITE_TAC [Boehm_apply_APPEND] \\
       MATCH_MP_TAC lameq_TRANS \\
       Q.EXISTS_TAC ‘apply pi (y @* args2)’ \\
       reverse CONJ_TAC >- art [] \\
       MATCH_MP_TAC lameq_apply_cong \\
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
 >> qabbrev_tac ‘as = FRESH_list (LENGTH args) (FV P)’
 >> qabbrev_tac ‘pi = [LAMl as P/y]::MAP rightctxt (MAP VAR (REVERSE vs))’
 >> Q.EXISTS_TAC ‘pi’
 >> STRONG_CONJ_TAC
 >- rw [Abbr ‘pi’, Boehm_transform_def, EVERY_SNOC, EVERY_MAP]
 >> DISCH_TAC
 (* applying Boehm_apply_unsolvable *)
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC Boehm_apply_unsolvable >> art [])
 (* stage work *)
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘apply pi M0’
 >> CONJ_TAC >- (MATCH_MP_TAC lameq_apply_cong >> art [])
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
       by rw [FRESH_list_def, Abbr ‘as’]
 >> MATCH_MP_TAC lameq_LAMl_appstar_reduce >> rw []
QED

val _ = export_theory ();
val _ = html_theory "boehm";

(* References:

   [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
       College Publications, London (1984).
 *)
