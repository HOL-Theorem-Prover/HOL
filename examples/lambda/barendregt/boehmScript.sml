(*---------------------------------------------------------------------------*
 * boehmScript.sml: (Effective) Boehm Trees (Chapter 10 of [1])              *
 *---------------------------------------------------------------------------*)

open HolKernel boolLib Parse bossLib BasicProvers;

(* core theories *)
open optionTheory arithmeticTheory pred_setTheory listTheory rich_listTheory
     llistTheory relationTheory ltreeTheory pathTheory posetTheory hurdUtils
     finite_mapTheory;

open binderLib termTheory appFOLDLTheory chap2Theory chap3Theory nomsetTheory
     head_reductionTheory standardisationTheory solvableTheory reductionEval;

open basic_swapTheory horeductionTheory takahashiS3Theory;

val _ = new_theory "boehm";

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];

val o_DEF = combinTheory.o_DEF;
val _ = hide "Y";

(*---------------------------------------------------------------------------*
 *  ‘tpm’ as an equivalence relation between terms
 *---------------------------------------------------------------------------*)

Definition tpm_rel_def :
    tpm_rel M N = ?pi. tpm pi M = N
End

Theorem tpm_rel_alt :
    !M N. tpm_rel M N <=> ?pi. M = tpm pi N
Proof
    rw [tpm_rel_def]
 >> EQ_TAC >> rpt STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      fs [tpm_eql] >> Q.EXISTS_TAC ‘REVERSE pi’ >> rw [],
      (* goal 2 (of 2) *)
      fs [tpm_eqr] >> Q.EXISTS_TAC ‘REVERSE pi’ >> rw [] ]
QED

Theorem equivalence_tpm_rel :
    equivalence tpm_rel
Proof
    rw [equivalence_def, reflexive_def, symmetric_def, transitive_def]
 >| [ (* goal 1 (of 3) *)
      rw [tpm_rel_def] >> Q.EXISTS_TAC ‘[]’ >> rw [],
      (* goal 2 (of 3) *)
      rw [tpm_rel_def] >> EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
      [ (* goal 2.1 (of 2) *)
        ONCE_REWRITE_TAC [EQ_SYM_EQ] >> fs [tpm_eql] \\
        Q.EXISTS_TAC ‘REVERSE pi’ >> rw [],
        (* goal 2.2 (of 2) *)
        ONCE_REWRITE_TAC [EQ_SYM_EQ] >> fs [tpm_eql] \\
        Q.EXISTS_TAC ‘REVERSE pi’ >> rw [] ],
      (* goal 3 (of 3) *)
      fs [tpm_rel_def] \\
      POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
      POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
      Q.EXISTS_TAC ‘pi' ++ pi’ \\
      rw [pmact_decompose] ]
QED

val tpm_rel_thm = equivalence_tpm_rel |>
    REWRITE_RULE [equivalence_def, reflexive_def, symmetric_def, transitive_def];

(* below are easy-to-use forms of [equivalence_tpm_rel] *)
Theorem tpm_rel_REFL[simp] :
    tpm_rel M M
Proof
    rw [tpm_rel_thm]
QED

Theorem tpm_rel_SYM :
    !M N. tpm_rel M N ==> tpm_rel N M
Proof
    rw [tpm_rel_thm]
QED

Theorem tpm_rel_SYM_EQ :
    !M N. tpm_rel M N <=> tpm_rel N M
Proof
    rw [tpm_rel_thm]
QED

Theorem tpm_rel_TRANS :
    !M1 M2 M3. tpm_rel M1 M2 /\ tpm_rel M2 M3 ==> tpm_rel M1 M3
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC (cj 3 tpm_rel_thm)
 >> Q.EXISTS_TAC ‘M2’ >> art []
QED

Theorem tpm_rel_reduce[simp] :
    tpm_rel (tpm pi M) M /\ tpm_rel M (tpm pi M)
Proof
    CONJ_ASM1_TAC
 >- (REWRITE_TAC [tpm_rel_alt] \\
     Q.EXISTS_TAC ‘pi’ >> REWRITE_TAC [])
 >> MATCH_MP_TAC tpm_rel_SYM >> art []
QED

Theorem tpm_rel_cong :
    !M M' N N'. tpm_rel M M' /\ tpm_rel N N' ==> (tpm_rel M N <=> tpm_rel M' N')
Proof
    rpt STRIP_TAC
 >> EQ_TAC >> STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC tpm_rel_TRANS >> Q.EXISTS_TAC ‘N’ >> art [] \\
      MATCH_MP_TAC tpm_rel_TRANS >> Q.EXISTS_TAC ‘M’ >> art [] \\
      MATCH_MP_TAC tpm_rel_SYM >> art [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC tpm_rel_TRANS >> Q.EXISTS_TAC ‘M'’ >> art [] \\
      MATCH_MP_TAC tpm_rel_TRANS >> Q.EXISTS_TAC ‘N'’ >> art [] \\
      MATCH_MP_TAC tpm_rel_SYM >> art [] ]
QED

(*---------------------------------------------------------------------------*
 *  Canonical binding list of a term w.r.t. excluded variables
 *---------------------------------------------------------------------------*)

(* NOTE: This definition assumes ‘solvable M’ (or ‘has_hnf M’) *)
Definition canonical_vars_def :
    canonical_vars X M =
       let M0 = principle_hnf M;
            n = LAMl_size M0
        in
           NEWS n (X UNION FV M0)
End

Theorem canonical_vars_thm :
    !X M M0 vs. FINITE X /\ solvable M /\
                M0 = principle_hnf M /\ vs = canonical_vars X M
            ==> ALL_DISTINCT vs /\ DISJOINT (set vs) (X UNION FV M0) /\
                LENGTH vs = LAMl_size M0
Proof
    rpt GEN_TAC
 >> simp [canonical_vars_def]
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘M0 = _’ K_TAC
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q.PAT_X_ASSUM ‘vs = _’ K_TAC
 >> qabbrev_tac ‘vs = NEWS n (X UNION FV M0)’
 >> MP_TAC (Q.SPECL [‘n’, ‘X UNION FV (M0 :term)’] NEWS_def)
 >> simp []
QED

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

(* Definition 10.1.9 [1, p.221] (Effective Boehm Tree)

   NOTE: The setup of ‘X UNION FV M’ when calling ‘NEWS’ guarentees that
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
             vs = NEWS n (X UNION FV M0);
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

Theorem BT_of_principle_hnf :
    !X M. solvable M ==> BTe X (principle_hnf M) = BTe X M
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
 >> qabbrev_tac ‘vs = NEWS n (X UNION FV M0)’
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

   NOTE2: this theorem can be improved to an iff: M == N <=> BTe X M = BTe X N
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
 (* NOTE: ‘solvable P /\ solvable Q’ cannot be added here *)
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
 >> qabbrev_tac ‘vs = NEWS n  (Y UNION FV P0)’
 >> qabbrev_tac ‘vs'= NEWS n' (Y UNION FV Q0)’
 >> qabbrev_tac ‘P1 = principle_hnf (P0 @* MAP VAR vs)’
 >> qabbrev_tac ‘Q1 = principle_hnf (Q0 @* MAP VAR vs')’
 >> qabbrev_tac ‘Ps = hnf_children P1’
 >> qabbrev_tac ‘Qs = hnf_children Q1’
 >> qabbrev_tac ‘y  = hnf_head P1’
 >> qabbrev_tac ‘y' = hnf_head Q1’
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
 >> Know ‘Y UNION FV P0 = Y /\ Y UNION FV Q0 = Y’
 >- (Q.PAT_X_ASSUM ‘FV P UNION FV Q SUBSET Y’ MP_TAC \\
    ‘FV P0 SUBSET FV P’ by METIS_TAC [principle_hnf_FV_SUBSET'] \\
    ‘FV Q0 SUBSET FV Q’ by METIS_TAC [principle_hnf_FV_SUBSET'] \\
     NTAC 2 (POP_ASSUM MP_TAC) >> SET_TAC [])
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
                     lameq_principle_hnf_head_eq') >> simp [])
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
 >> ‘hnf P0 /\ hnf Q0’ by PROVE_TAC [hnf_principle_hnf']
 >> qabbrev_tac ‘n = LAMl_size Q0’
 >> ‘ALL_DISTINCT vs /\ LENGTH vs = n /\ DISJOINT (set vs) Y’
      by rw [Abbr ‘vs’, NEWS_def]
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
             m = hnf_children_size M0;
            vs = NEWS n (X UNION FV M0);
            M1 = principle_hnf (M0 @* (MAP VAR vs));
            Ms = hnf_children M1
        in
            if x < m then subterm (X UNION set vs) (EL x Ms) xs else NONE
    else
        NONE
End

Theorem subterm_of_solvables :
    !X M x xs. solvable M ==>
      subterm X M (x::xs) =
        let M0 = principle_hnf M;
             n = LAMl_size M0;
             m = hnf_children_size M0;
            vs = NEWS n (X UNION FV M0);
            M1 = principle_hnf (M0 @* (MAP VAR vs));
            Ms = hnf_children M1
        in
            if x < m then subterm (X UNION set vs) (EL x Ms) xs else NONE
Proof
    RW_TAC std_ss []
 >> rw [subterm_def]
QED

(* M0 is not needed if M is already an hnf *)
Theorem subterm_of_hnf :
    !X M x xs. FINITE X /\ hnf M ==>
      subterm X M (x::xs) =
        let  n = LAMl_size M;
             m = hnf_children_size M;
            vs = NEWS n (X UNION FV M);
            M1 = principle_hnf (M @* (MAP VAR vs));
            Ms = hnf_children M1
        in
            if x < m then subterm (X UNION set vs) (EL x Ms) xs else NONE
Proof
    rpt STRIP_TAC
 >> ‘solvable M’ by PROVE_TAC [solvable_iff_has_hnf, hnf_has_hnf]
 >> RW_TAC std_ss [subterm_of_solvables]
 >> ‘M0 = M’ by rw [Abbr ‘M0’, principle_hnf_reduce]
 >> POP_ASSUM (fn th => gs [Abbr ‘M0’, th])
QED

(* In the extreme case, M is a absfree hnf (i.e. VAR y @* args), and the
   definition of subterm can be greatly simplified.
 *)
Theorem subterm_of_absfree_hnf :
    !X M x xs. FINITE X /\ hnf M /\ ~is_abs M ==>
      subterm X M (x::xs) =
        let  m = hnf_children_size M;
            Ms = hnf_children M
        in
            if x < m then subterm X (EL x Ms) xs else NONE
Proof
    rpt STRIP_TAC
 >> ‘solvable M’ by PROVE_TAC [solvable_iff_has_hnf, hnf_has_hnf]
 >> RW_TAC std_ss [subterm_of_solvables]
 >> ‘?y args. M = VAR y @* args’ by PROVE_TAC [absfree_hnf_cases]
 >> gs [Abbr ‘m’, Abbr ‘M0’, Abbr ‘Ms’, Abbr ‘n’,
        hnf_children_hnf, hnf_appstar]
 >> gs [Abbr ‘vs’]
 >> gs [Abbr ‘Ms'’, Abbr ‘M1’, hnf_children_hnf]
QED

(* NOTE: The uses of ‘subterm' X M p’ assumes ‘subterm X M p <> NONE’ *)
Overload subterm' = “\X M p. SND (THE (subterm X M p))”

(* |- !X M. subterm X M [] = SOME (X,M) *)
Theorem subterm_NIL[simp] = SPEC_ALL (cj 1 subterm_def)

Theorem subterm_NIL'[simp] :
    subterm' X M [] = M
Proof
    rw [subterm_NIL]
QED

(* NOTE: This theorem is only possible when ‘vs = NEWS n (X UNION FV M0)’
        (instead of ‘FV M’) in the definition of [subterm_def].
 *)
Theorem subterm_of_principle_hnf :
    !X M p. solvable M /\ p <> [] ==> subterm X (principle_hnf M) p = subterm X M p
Proof
    rpt STRIP_TAC
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> Cases_on ‘p’ >> fs []
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> ‘solvable M0’ by PROVE_TAC [solvable_principle_hnf]
 >> RW_TAC std_ss [subterm_of_solvables]
 >> ‘M0' = M0’ by rw [Abbr ‘M0'’, Abbr ‘M0’, principle_hnf_stable']
 >> qunabbrev_tac ‘M0'’
 >> POP_ASSUM (fs o wrap)
 >> ‘vs' = vs’ by rw [Abbr ‘vs’, Abbr ‘vs'’]
 >> POP_ASSUM (fs o wrap)
 >> PROVE_TAC []
QED

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
 >> qabbrev_tac ‘vs = NEWS n (X UNION FV M0)’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> qabbrev_tac ‘Ms = hnf_children M1’
 >> Know ‘BTe X M = ltree_unfold BT_generator (X,M)’ >- rw [BT_def]
 >> simp [Once ltree_unfold, BT_generator_def]
 >> DISCH_TAC
 >> simp [LNTH_fromList, EL_MAP]
 >> Q.PAT_X_ASSUM ‘h::p IN ltree_paths (BTe X M)’ MP_TAC
 >> POP_ORW
 >> rw [ltree_paths_def, ltree_lookup_def, LNTH_fromList, GSYM BT_def, EL_MAP]
QED

(* NOTE: This proof shares a lot of tactics with [subterm_tpm_lemma] *)
Theorem BT_ltree_lookup_lemma :
    !p X Y M pi. FINITE X /\ FINITE Y /\
                 ltree_lookup (BTe X M) p <> NONE ==>
                 ltree_lookup (BTe Y (tpm pi M)) p <> NONE
Proof
    Induct_on ‘p’ >- rw [ltree_lookup_def]
 >> rpt GEN_TAC
 >> reverse (Cases_on ‘solvable M’)
 >- rw [BT_of_unsolvables]
 >> simp [ltree_lookup]
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> qabbrev_tac ‘vs = NEWS n (X UNION FV M0)’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> qabbrev_tac ‘Ms = hnf_children M1’
 >> Know ‘BTe X M = ltree_unfold BT_generator (X,M)’ >- rw [BT_def]
 >> simp [Once ltree_unfold, BT_generator_def, LNTH_fromList, LMAP_fromList]
 >> DISCH_THEN K_TAC
 >> REWRITE_TAC [GSYM BT_def]
 >> Cases_on ‘h < LENGTH Ms’ >> simp [EL_MAP]
 (* stage work *)
 >> Know ‘BTe Y (tpm pi M) = ltree_unfold BT_generator (Y,tpm pi M)’ >- rw [BT_def]
 >> simp [Once ltree_unfold, BT_generator_def, LNTH_fromList, LMAP_fromList]
 >> DISCH_THEN K_TAC
 >> qabbrev_tac ‘M0' = principle_hnf (tpm pi M)’
 >> qabbrev_tac ‘n' = LAMl_size M0'’
 >> qabbrev_tac ‘vs' = NEWS n' (Y UNION FV M0')’
 >> qabbrev_tac ‘M1' = principle_hnf (M0' @* MAP VAR vs')’
 >> qabbrev_tac ‘Ms' = hnf_children M1'’
 >> Know ‘M0' = tpm pi M0’
 >- (qunabbrevl_tac [‘M0’, ‘M0'’] \\
     MATCH_MP_TAC principle_hnf_tpm' >> art [])
 >> DISCH_TAC
 >> ‘n' = n’ by rw [Abbr ‘n’, Abbr ‘n'’, LAMl_size_tpm]
 >> STRIP_TAC
 >> Know ‘ALL_DISTINCT vs /\ DISJOINT (set vs) (X UNION FV M0) /\ LENGTH vs = n’
 >- rw [Abbr ‘vs’, NEWS_def]
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [DISJOINT_UNION']))
 >> Know ‘ALL_DISTINCT vs' /\ DISJOINT (set vs') (Y UNION FV (tpm pi M0)) /\
          LENGTH vs' = n’
 >- rw [Abbr ‘vs'’, NEWS_def]
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [DISJOINT_UNION']))
 >> qabbrev_tac ‘vs1p = listpm string_pmact (REVERSE pi) vs'’
 >> ‘ALL_DISTINCT vs1p’ by rw [Abbr ‘vs1p’]
 (* rewriting inside the abbreviation of M1' *)
 >> Know ‘tpm pi M0 @* MAP VAR vs' = tpm pi (M0 @* MAP VAR vs1p)’
 >- (rw [Abbr ‘vs1p’, tpm_appstar] \\
     Suff ‘listpm term_pmact pi (MAP VAR (listpm string_pmact (REVERSE pi) vs')) =
           MAP VAR vs'’ >- rw [] \\
     rw [LIST_EQ_REWRITE, EL_MAP])
 >> DISCH_THEN (fs o wrap)
 >> qunabbrev_tac ‘n'’
 >> Q.PAT_X_ASSUM ‘LAMl_size M0 = n’ (fs o wrap o SYM)
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q.PAT_X_ASSUM ‘T’ K_TAC
 >> Know ‘DISJOINT (set vs1p) (FV M0)’
 >- (rw [Abbr ‘vs1p’, DISJOINT_ALT', MEM_listpm] \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs') (FV (tpm pi M0))’ MP_TAC \\
     rw [DISJOINT_ALT', FV_tpm])
 >> DISCH_TAC
 >> ‘LENGTH vs1p = n’ by rw [Abbr ‘vs1p’, LENGTH_listpm]
 >> qabbrev_tac ‘Z = X UNION Y UNION FV M0 UNION set vs UNION set vs1p’
 >> ‘FINITE Z’ by rw [Abbr ‘Z’]
 >> qabbrev_tac ‘vs2 = NEWS n Z’
 >> Know ‘ALL_DISTINCT vs2 /\ DISJOINT (set vs2) Z /\ LENGTH vs2 = n’
 >- rw [Abbr ‘vs2’, NEWS_def]
 >> Q.PAT_X_ASSUM ‘FINITE Z’ K_TAC
 >> qunabbrev_tac ‘Z’
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [DISJOINT_UNION']))
 (* stage work *)
 >> ‘hnf M0’ by PROVE_TAC [hnf_principle_hnf']
 >> hnf_tac (“M0 :term”, “vs2 :string list”,
             “M2 :term”, “y :string”, “args :term list”)
 >> ‘TAKE n vs2 = vs2’ by rw [TAKE_LENGTH_ID_rwt]
 >> POP_ASSUM (rfs o wrap)
 >> ‘hnf M2’ by rw [hnf_appstar]
 >> Know ‘DISJOINT (set vs) (FV M2) /\
          DISJOINT (set vs1p) (FV M2)’
 >- (rpt CONJ_TAC (* 2 subgoals, same tactics *) \\
     (MATCH_MP_TAC DISJOINT_SUBSET \\
      Q.EXISTS_TAC ‘FV M0 UNION set vs2’ \\
      CONJ_TAC >- (Q.PAT_X_ASSUM ‘M0 = LAMl vs2 (VAR y @* args)’ K_TAC \\
                   reverse (rw [DISJOINT_UNION']) >- rw [Once DISJOINT_SYM] \\
                   MATCH_MP_TAC DISJOINT_SUBSET \\
                   Q.EXISTS_TAC ‘FV M’ >> art []) \\
     ‘FV M0 UNION set vs2 = FV (M0 @* MAP VAR vs2)’ by rw [] >> POP_ORW \\
      qunabbrev_tac ‘M2’ \\
      MATCH_MP_TAC principle_hnf_FV_SUBSET' \\
      Know ‘solvable (VAR y @* args)’
      >- (rw [solvable_iff_has_hnf] \\
          MATCH_MP_TAC hnf_has_hnf \\
          rw [hnf_appstar]) >> DISCH_TAC \\
      Suff ‘M0 @* MAP VAR vs2 == VAR y @* args’
      >- PROVE_TAC [lameq_solvable_cong] \\
      rw [lameq_LAMl_appstar_VAR]))
 >> STRIP_TAC
 >> Know ‘M1 = tpm (ZIP (vs2,vs)) M2’
 >- (simp [Abbr ‘M1’] \\
     MATCH_MP_TAC principle_hnf_LAMl_appstar \\
     Q.PAT_X_ASSUM ‘M2 = VAR y @* args’ (ONCE_REWRITE_TAC o wrap o SYM) >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘p1 = ZIP (vs2,vs)’
 >> Know ‘M1' = tpm pi (principle_hnf (M0 @* MAP VAR vs1p))’
 >- (qunabbrev_tac ‘M1'’ \\
     MATCH_MP_TAC principle_hnf_tpm >> art [] \\
     REWRITE_TAC [has_hnf_thm] \\
     Q.EXISTS_TAC ‘(FEMPTY |++ ZIP (vs2,MAP VAR vs1p)) ' (VAR y @* args)’ \\
     CONJ_TAC
     >- (MATCH_MP_TAC hreduce_LAMl_appstar \\
         rw [EVERY_MEM, MEM_MAP] >> rw [] \\
         Q.PAT_X_ASSUM ‘DISJOINT (set vs2) (set vs1p)’ MP_TAC \\
         rw [DISJOINT_ALT']) \\
     REWRITE_TAC [GSYM fromPairs_def] \\
    ‘FDOM (fromPairs vs2 (MAP VAR vs1p)) = set vs2’ by rw [FDOM_fromPairs] \\
     Cases_on ‘MEM y vs2’
     >- (simp [ssub_thm, ssub_appstar, hnf_appstar] \\
         fs [MEM_EL] >> rename1 ‘i < LENGTH vs2’ \\
         Know ‘fromPairs vs2 (MAP VAR vs1p) ' (EL i vs2) = EL i (MAP VAR vs1p)’
         >- (MATCH_MP_TAC fromPairs_FAPPLY_EL >> rw []) >> Rewr' \\
         rw [EL_MAP]) \\
     simp [ssub_thm, ssub_appstar, hnf_appstar])
 >> DISCH_TAC
 >> Know ‘M1' = tpm pi (tpm (ZIP (vs2,vs1p)) M2)’
 >- (POP_ORW >> simp [] \\
     MATCH_MP_TAC principle_hnf_LAMl_appstar \\
     Q.PAT_X_ASSUM ‘M2 = VAR y @* args’ (ONCE_REWRITE_TAC o wrap o SYM) >> art [])
 >> POP_ASSUM K_TAC (* M1' = ... (already used) *)
 >> REWRITE_TAC [GSYM pmact_decompose]
 >> qabbrev_tac ‘p2 = pi ++ ZIP (vs2,vs1p)’
 >> DISCH_TAC
 (* pop all assumptions about ‘Ms’ *)
 >> Q.PAT_X_ASSUM ‘ltree_lookup (BTe (X UNION set vs) (EL h Ms)) p <> NONE’ MP_TAC
 >> Q.PAT_X_ASSUM ‘h < LENGTH Ms’ MP_TAC
 (* applying hnf_children_tpm to rewrite Ms and Ms' *)
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
 >> simp [EL_MAP, GSYM BT_def]
 >> qabbrev_tac ‘N = EL h args’
 >> Know ‘?pi'. tpm p2 N = tpm pi' (tpm p1 N)’
 >- (Q.EXISTS_TAC ‘p2 ++ REVERSE p1’ \\
     rw [pmact_decompose])
 >> STRIP_TAC
 >> POP_ORW
 >> qabbrev_tac ‘N' = tpm p1 N’
 (* finally, using IH in a bulk way *)
 >> NTAC 2 DISCH_TAC
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘X UNION set vs’ >> rw []
QED

(* The set of ltree paths of BT is unique w.r.t. excluded list *)
Theorem BT_ltree_paths_unique :
    !X Y M. FINITE X /\ FINITE Y ==>
            ltree_paths (BTe X M) = ltree_paths (BTe Y M)
Proof
    rw [ltree_paths_def]
 >> MATCH_MP_TAC SUBSET_ANTISYM
 >> rw [SUBSET_DEF]
 >| [ (* goal 1 (of 2) *)
      MP_TAC (Q.SPECL [‘x’, ‘X’, ‘Y’, ‘M’, ‘[]’] BT_ltree_lookup_lemma),
      (* goal 2 (of 2) *)
      MP_TAC (Q.SPECL [‘x’, ‘Y’, ‘X’, ‘M’, ‘[]’] BT_ltree_lookup_lemma) ]
 >> rw [] (* shared ending tactics *)
QED

(* NOTE: In the above theorem, when the antecedents hold, i.e.

         p IN ltree_paths (BTe X M) /\ subterm X M p = NONE

   Then ‘subterm' X M (FRONT p)’ must be an unsolvable term. This result can be
   even improved to an iff, as the present theorem shows.
 *)
Theorem subterm_is_none_iff_parent_unsolvable :
    !p X M. FINITE X /\ p IN ltree_paths (BTe X M) ==>
           (subterm X M p = NONE <=>
            p <> [] /\ subterm X M (FRONT p) <> NONE /\
            unsolvable (subterm' X M (FRONT p)))
Proof
    Induct_on ‘p’
 >> rw [subterm_def] (* 2 subgoals, only one left *)
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> qabbrev_tac ‘m = hnf_children_size M0’
 >> qabbrev_tac ‘vs = NEWS n (X UNION FV M0)’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* (MAP VAR vs))’
 >> qabbrev_tac ‘Ms = hnf_children M1’
 >> reverse (Cases_on ‘solvable M’)
 >- (rw [] >> Suff ‘p = []’ >- rw [subterm_NIL] \\
     Q.PAT_X_ASSUM ‘h::p IN ltree_paths (BTe X M)’ MP_TAC \\
     simp [BT_of_unsolvables, ltree_paths_def, ltree_lookup_def])
 >> simp []
 >> Know ‘m = LENGTH Ms’
 >- (qunabbrev_tac ‘M1’ \\
    ‘ALL_DISTINCT vs /\ LENGTH vs = n /\ DISJOINT (set vs) (X UNION FV M0)’
       by (rw [Abbr ‘vs’, NEWS_def]) \\
    ‘hnf M0’ by rw [hnf_principle_hnf', Abbr ‘M0’] \\
     Know ‘?y args. M0 = LAMl (TAKE n vs) (VAR y @* args)’
     >- (qunabbrev_tac ‘n’ >> irule (iffLR hnf_cases_shared) >> rw [] \\
         MATCH_MP_TAC DISJOINT_SUBSET \\
         Q.EXISTS_TAC ‘X UNION FV M0’ >> art [] \\
         SET_TAC []) >> STRIP_TAC \\
    ‘TAKE n vs = vs’ by rw [] \\
     POP_ASSUM (REV_FULL_SIMP_TAC std_ss o wrap) \\
     qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’ \\
     Know ‘M1 = VAR y @* args’
     >- (qunabbrev_tac ‘M1’ >> POP_ORW \\
         MATCH_MP_TAC principle_hnf_beta_reduce >> rw [hnf_appstar]) \\
     qunabbrev_tac ‘Ms’ \\
     Rewr' >> simp [hnf_children_hnf] \\
     qunabbrev_tac ‘m’ >> simp [])
 >> DISCH_TAC
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

Theorem subterm_is_none_imp_parent_not :
    !p X M. FINITE X /\ p IN ltree_paths (BTe X M) /\
            subterm X M p = NONE ==> subterm X M (FRONT p) <> NONE
Proof
    METIS_TAC [subterm_is_none_iff_parent_unsolvable]
QED

(* NOTE: for whatever reasons such that ‘subterm X M p = NONE’, even when
        ‘p NOTIN ltree_paths (BTe X M)’, the conclusion (rhs) always holds.
 *)
Theorem subterm_is_none_iff_children :
    !X M p. subterm X M p = NONE <=> !p'. p <<= p' ==> subterm X M p' = NONE
Proof
    rpt GEN_TAC
 >> reverse EQ_TAC
 >- (DISCH_THEN (MP_TAC o (Q.SPEC ‘p’)) >> rw [])
 >> Q.ID_SPEC_TAC ‘M’
 >> Q.ID_SPEC_TAC ‘X’
 >> Q.ID_SPEC_TAC ‘p’
 >> Induct_on ‘p’ >- rw [subterm_NIL]
 >> rw [subterm_def]
 >> Cases_on ‘p'’ >> fs [subterm_def]
QED

Theorem subterm_solvable_lemma :
    !X M p. FINITE X /\ p <> [] /\
            p IN ltree_paths (BTe X M) /\ subterm X M p <> NONE ==>
           (!q. q <<= p ==> subterm X M q <> NONE) /\
           (!q. q <<= FRONT p ==> solvable (subterm' X M q))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> CONJ_ASM1_TAC
 >- (Q.X_GEN_TAC ‘q’ >> DISCH_TAC \\
     CCONTR_TAC \\
     POP_ASSUM (MP_TAC o (REWRITE_RULE [Once subterm_is_none_iff_children])) \\
     DISCH_THEN (MP_TAC o (Q.SPEC ‘p’)) >> rw [])
 >> ‘0 < LENGTH p’ by rw [GSYM NOT_NIL_EQ_LENGTH_NOT_0]
 >> Q.X_GEN_TAC ‘q’
 >> Suff ‘!l. l <> [] /\ l <<= p ==> solvable (subterm' X M (FRONT l))’
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
 >> MP_TAC (Q.SPECL [‘l’, ‘X’, ‘M’] subterm_is_none_iff_parent_unsolvable)
 >> ‘l IN ltree_paths (BTe X M)’ by PROVE_TAC [ltree_paths_inclusive]
 >> simp []
 >> Suff ‘subterm X M (FRONT l) <> NONE’ >- PROVE_TAC []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> MATCH_MP_TAC IS_PREFIX_TRANS
 >> Q.EXISTS_TAC ‘l’ >> rw []
 >> MATCH_MP_TAC IS_PREFIX_BUTLAST' >> art []
QED

(* cf. [subterm_some_none_cong] when X changes but M remains *)
Theorem lameq_subterm_cong_none :
    !p X M N. FINITE X /\ FV M UNION FV N SUBSET X /\ M == N ==>
             (subterm X M p = NONE <=> subterm X N p = NONE)
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
 >> Know ‘X UNION FV M0 = X /\ X UNION FV M0' = X’
 >- (Q.PAT_X_ASSUM ‘FV M UNION FV N SUBSET X’ MP_TAC \\
    ‘FV M0 SUBSET FV M’ by METIS_TAC [principle_hnf_FV_SUBSET'] \\
    ‘FV M0' SUBSET FV N’ by METIS_TAC [principle_hnf_FV_SUBSET'] \\
     NTAC 2 (POP_ASSUM MP_TAC) >> SET_TAC [])
 >> DISCH_THEN (fs o wrap)
 >> Know ‘n = n' /\ vs = vs'’
 >- (reverse CONJ_ASM1_TAC >- rw [Abbr ‘vs’, Abbr ‘vs'’] \\
     qunabbrevl_tac [‘n’, ‘n'’, ‘M0’, ‘M0'’] \\
     MATCH_MP_TAC lameq_principle_hnf_size_eq' >> art [])
 (* clean up now duplicated abbreviations: n' and vs' *)
 >> qunabbrevl_tac [‘n'’, ‘vs'’]
 >> DISCH_THEN (rfs o wrap o GSYM)
 (* applying lameq_principle_hnf_thm' *)
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘N’, ‘M0’, ‘M0'’, ‘n’, ‘vs’, ‘M1’, ‘M1'’]
                     lameq_principle_hnf_thm')
 >> simp []
 >> RW_TAC std_ss [Abbr ‘m’, Abbr ‘m'’]
 (* preparing for hnf_children_FV_SUBSET

    Here, once again, we need to get suitable explicit forms of P0 and Q0,
    to show that, P1 and Q1 are absfree hnf.
  *)
 >> ‘hnf M0 /\ hnf M0'’ by PROVE_TAC [hnf_principle_hnf']
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> ‘ALL_DISTINCT vs /\ LENGTH vs = n /\ DISJOINT (set vs) X’
       by rw [Abbr ‘vs’, NEWS_def]
 >> Know ‘DISJOINT (set vs) (FV M0)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘X’ >> art [] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘FV M’ >> art [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set vs) (FV M0')’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘X’ >> art [] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘FV N’ >> art [] \\
     qunabbrev_tac ‘M0'’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 (* NOTE: the next two hnf_tac will refine M1 and M1' *)
 >> qunabbrevl_tac [‘M1’, ‘M1'’]
 >> hnf_tac (“M0 :term”, “vs :string list”,
             “M1 :term”, “y  :string”, “args :term list”)
 >> hnf_tac (“M0':term”, “vs :string list”,
             “M1':term”, “y' :string”, “args':term list”)
 >> Q.PAT_X_ASSUM ‘n = LAMl_size M0'’ (rfs o wrap o SYM)
 >> ‘TAKE n vs = vs’ by rw [TAKE_LENGTH_ID_rwt]
 >> POP_ASSUM (rfs o wrap)
 (* refine P1 and Q1 again for clear assumptions using them *)
 >> qunabbrevl_tac [‘M1’, ‘M1'’]
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> qabbrev_tac ‘M1' = principle_hnf (M0' @* MAP VAR vs)’
 >> Know ‘LENGTH args = LENGTH Ms’
 >- (qunabbrev_tac ‘Ms’ \\
     Q.PAT_X_ASSUM ‘M1 = VAR y @* args’ (ONCE_REWRITE_TAC o wrap) \\
     simp [hnf_children_hnf])
 >> Rewr'
 >> Know ‘LENGTH args' = LENGTH Ms'’
 >- (qunabbrev_tac ‘Ms'’ \\
     Q.PAT_X_ASSUM ‘M1' = VAR y' @* args'’ (ONCE_REWRITE_TAC o wrap) \\
     simp [hnf_children_hnf])
 >> Rewr'
 >> qabbrev_tac ‘m = LENGTH Ms'’
 >> Cases_on ‘h < m’ >> simp []
 >> Cases_on ‘p = []’ >> fs []
 (* final stage *)
 >> FIRST_X_ASSUM MATCH_MP_TAC >> simp []
 >> CONJ_TAC (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      Know ‘!i. i < LENGTH Ms ==> FV (EL i Ms) SUBSET FV M1’
      >- (MATCH_MP_TAC hnf_children_FV_SUBSET \\
          rw [hnf_appstar]) >> DISCH_TAC \\
      MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M1’ \\
      CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
      MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M0 UNION set vs’ \\
      CONJ_TAC >- simp [FV_LAMl] \\
      Suff ‘FV M0 SUBSET X’ >- SET_TAC [] \\
      MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M’ \\
      reverse CONJ_TAC >- art [] (* FV M SUBSET X *) \\
      qunabbrev_tac ‘M0’ >> MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [],
      (* goal 2 (of 2) *)
      Know ‘!i. i < LENGTH Ms' ==> FV (EL i Ms') SUBSET FV M1'’
      >- (MATCH_MP_TAC hnf_children_FV_SUBSET \\
          rw [hnf_appstar]) >> DISCH_TAC \\
      MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M1'’ \\
      CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw [Abbr ‘m’]) \\
      MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M0' UNION set vs’ \\
      CONJ_TAC >- simp [FV_LAMl] \\
      Suff ‘FV M0' SUBSET X’ >- SET_TAC [] \\
      MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV N’ \\
      reverse CONJ_TAC >- art [] (* FV N SUBSET X *) \\
      qunabbrev_tac ‘M0'’ >> MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [] ]
QED

Theorem lameq_subterm_cong :
    !p X M N. FINITE X /\ FV M UNION FV N SUBSET X /\ M == N /\
              subterm X M p <> NONE /\ subterm X N p <> NONE ==>
              subterm' X M p == subterm' X N p
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
 >> Q.PAT_X_ASSUM ‘subterm X N (h::p) <> NONE’ MP_TAC
 >> Q.PAT_X_ASSUM ‘subterm X M (h::p) <> NONE’ MP_TAC
 >> RW_TAC std_ss [subterm_of_solvables]
 >> gs []
 >> Know ‘X UNION FV M0 = X /\ X UNION FV M0' = X’
 >- (Q.PAT_X_ASSUM ‘FV M SUBSET X’ MP_TAC \\
     Q.PAT_X_ASSUM ‘FV N SUBSET X’ MP_TAC \\
    ‘FV M0 SUBSET FV M’ by METIS_TAC [principle_hnf_FV_SUBSET'] \\
    ‘FV M0' SUBSET FV N’ by METIS_TAC [principle_hnf_FV_SUBSET'] \\
     NTAC 2 (POP_ASSUM MP_TAC) >> SET_TAC [])
 >> DISCH_THEN (fs o wrap)
 >> Know ‘n = n' /\ vs = vs'’
 >- (reverse CONJ_ASM1_TAC >- rw [Abbr ‘vs’, Abbr ‘vs'’] \\
     qunabbrevl_tac [‘n’, ‘n'’, ‘M0’, ‘M0'’] \\
     MATCH_MP_TAC lameq_principle_hnf_size_eq' >> art [])
 (* clean up now duplicated abbreviations: n' and vs' *)
 >> qunabbrevl_tac [‘n'’, ‘vs'’]
 >> DISCH_THEN (rfs o wrap o GSYM)
 (* applying lameq_principle_hnf_thm' *)
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘N’, ‘M0’, ‘M0'’, ‘n’, ‘vs’, ‘M1’, ‘M1'’]
                     lameq_principle_hnf_thm') >> simp []
 >> RW_TAC std_ss [Abbr ‘m’, Abbr ‘m'’]
 (* preparing for hnf_children_FV_SUBSET *)
 >> ‘hnf M0 /\ hnf M0'’ by PROVE_TAC [hnf_principle_hnf']
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> ‘ALL_DISTINCT vs /\ LENGTH vs = n /\ DISJOINT (set vs) X’
      by rw [Abbr ‘vs’, NEWS_def]
 >> Know ‘DISJOINT (set vs) (FV M0)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘X’ >> art [] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘FV M’ >> art [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set vs) (FV M0')’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘X’ >> art [] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘FV N’ >> art [] \\
     qunabbrev_tac ‘M0'’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 (* NOTE: the next two hnf_tac will refine M1 and M1' *)
 >> qunabbrevl_tac [‘M1’, ‘M1'’]
 >> hnf_tac (“M0 :term”, “vs :string list”,
             “M1 :term”, “y  :string”, “args :term list”)
 >> hnf_tac (“M0':term”, “vs :string list”,
             “M1':term”, “y' :string”, “args':term list”)
 >> Q.PAT_X_ASSUM ‘n = LAMl_size M0'’ (rfs o wrap o SYM)
 >> ‘TAKE n vs = vs’ by rw [TAKE_LENGTH_ID_rwt]
 >> POP_ASSUM (rfs o wrap)
 (* refine P1 and Q1 again for clear assumptions using them *)
 >> qunabbrevl_tac [‘M1’, ‘M1'’]
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> qabbrev_tac ‘M1' = principle_hnf (M0' @* MAP VAR vs)’
 >> Know ‘LENGTH args = LENGTH Ms’
 >- (qunabbrev_tac ‘Ms’ \\
     Q.PAT_X_ASSUM ‘M1 = VAR y @* args’ (ONCE_REWRITE_TAC o wrap) \\
     simp [hnf_children_hnf])
 >> DISCH_TAC
 >> Know ‘LENGTH args' = LENGTH Ms'’
 >- (qunabbrev_tac ‘Ms'’ \\
     Q.PAT_X_ASSUM ‘M1' = VAR y' @* args'’ (ONCE_REWRITE_TAC o wrap) \\
     simp [hnf_children_hnf])
 >> DISCH_TAC
 >> qabbrev_tac ‘m = LENGTH Ms'’
 >> Cases_on ‘p = []’ >> fs []
 (* final stage *)
 >> FIRST_X_ASSUM MATCH_MP_TAC >> simp []
 >> CONJ_TAC (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      Know ‘!i. i < LENGTH Ms ==> FV (EL i Ms) SUBSET FV M1’
      >- (MATCH_MP_TAC hnf_children_FV_SUBSET \\
          rw [hnf_appstar]) >> DISCH_TAC \\
      MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M1’ \\
      CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
      MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M0 UNION set vs’ \\
      CONJ_TAC >- simp [FV_LAMl] \\
      Suff ‘FV M0 SUBSET X’ >- SET_TAC [] \\
      MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M’ \\
      reverse CONJ_TAC >- art [] (* FV M SUBSET X *) \\
      qunabbrev_tac ‘M0’ >> MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [],
      (* goal 2 (of 2) *)
      Know ‘!i. i < LENGTH Ms' ==> FV (EL i Ms') SUBSET FV M1'’
      >- (MATCH_MP_TAC hnf_children_FV_SUBSET \\
          rw [hnf_appstar]) >> DISCH_TAC \\
      MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M1'’ \\
      CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw [Abbr ‘m’]) \\
      MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M0' UNION set vs’ \\
      CONJ_TAC >- simp [FV_LAMl] \\
      Suff ‘FV M0' SUBSET X’ >- SET_TAC [] \\
      MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV N’ \\
      reverse CONJ_TAC >- art [] (* FV N SUBSET X *) \\
      qunabbrev_tac ‘M0'’ >> MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [] ]
QED

(* NOTE: This lemma is more general than subterm_tpm_cong, which cannot be
   directly proved. The current form of this lemma, suitable for doing
   induction, was due to repeated experiments.  -- Chun Tian, 19 feb 2024.
 *)
Theorem subterm_tpm_lemma :
    !p X Y M pi. FINITE X /\ FINITE Y ==>
                (subterm X M p = NONE ==> subterm Y (tpm pi M) p = NONE) /\
                (subterm X M p <> NONE ==>
                 tpm_rel (subterm' X M p) (subterm' Y (tpm pi M) p))
Proof
    Induct_on ‘p’ >- rw []
 >> rpt GEN_TAC >> STRIP_TAC
 >> reverse (Cases_on ‘solvable M’)
 >- (‘unsolvable (tpm pi M)’ by PROVE_TAC [solvable_tpm] \\
     simp [subterm_def])
 >> ‘solvable (tpm pi M)’ by PROVE_TAC [solvable_tpm]
 (* BEGIN Michael Norrish's tactics *)
 >> CONV_TAC (UNBETA_CONV “subterm X M (h::p)”)
 >> qmatch_abbrev_tac ‘P _’
 >> RW_TAC bool_ss [subterm_of_solvables]
 >> simp [Abbr ‘P’]
 (* END Michael Norrish's tactics.
    preparing for expanding ‘subterm' Y (tpm pi M) (h::p)’ *)
 >> qabbrev_tac ‘M0' = principle_hnf (tpm pi M)’
 >> Know ‘M0' = tpm pi M0’
 >- (qunabbrevl_tac [‘M0’, ‘M0'’] \\
     MATCH_MP_TAC principle_hnf_tpm' >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘m' = hnf_children_size M0'’
 >> Know ‘m' = m’ >- (rw [Abbr ‘m’, Abbr ‘m'’, hnf_children_size_tpm])
 >> DISCH_TAC
 >> qabbrev_tac ‘n' = LAMl_size M0'’
 >> Know ‘n' = n’ >- (rw [Abbr ‘n’, Abbr ‘n'’, LAMl_size_tpm])
 >> DISCH_TAC
 (* special case *)
 >> reverse (Cases_on ‘h < m’)
 >- (rw [] >> rw [subterm_of_solvables])
 (* stage work, now h < m *)
 >> simp [] (* eliminate ‘h < m’ in the goal *)
 (* BEGIN Michael Norrish's tactics, again *)
 >> CONV_TAC (UNBETA_CONV “subterm Y (tpm pi M) (h::p)”)
 >> qmatch_abbrev_tac ‘P _’
 >> RW_TAC bool_ss [subterm_of_solvables]
 >> simp [Abbr ‘P’]
 (* END Michael Norrish's tactics. *)
 >> Q.PAT_X_ASSUM ‘tpm pi M0 = principle_hnf (tpm pi M)’ (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘n  = n'’  (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘n  = n''’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘m' = m''’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘m  = m'’  (fs o wrap o SYM)
 (* stage work *)
 >> Know ‘ALL_DISTINCT vs /\ DISJOINT (set vs) (X UNION FV M0) /\ LENGTH vs = n’
 >- rw [Abbr ‘vs’, NEWS_def]
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [DISJOINT_UNION']))
 >> Know ‘ALL_DISTINCT vs' /\ DISJOINT (set vs') (Y UNION FV (tpm pi M0)) /\
          LENGTH vs' = n’
 >- rw [Abbr ‘vs'’, NEWS_def]
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [DISJOINT_UNION']))
 (* vs1p is a permutated version of vs', to be used as first principles *)
 >> qabbrev_tac ‘vs1p = listpm string_pmact (REVERSE pi) vs'’
 >> ‘ALL_DISTINCT vs1p’ by rw [Abbr ‘vs1p’]
 (* rewriting inside the abbreviation of M1' *)
 >> Know ‘tpm pi M0 @* MAP VAR vs' = tpm pi (M0 @* MAP VAR vs1p)’
 >- (rw [Abbr ‘vs1p’, tpm_appstar] \\
     Suff ‘listpm term_pmact pi (MAP VAR (listpm string_pmact (REVERSE pi) vs')) =
           MAP VAR vs'’ >- rw [] \\
     rw [LIST_EQ_REWRITE, EL_MAP])
 >> DISCH_THEN (fs o wrap)
 (* prove that ‘M0 @* MAP VAR vs1p’ correctly denude M0

    NOTE: ‘DISJOINT (set vs1p) X’ seems NOT true (but seems not needed)
  *)
 >> Know ‘DISJOINT (set vs1p) (FV M0)’
 >- (rw [Abbr ‘vs1p’, DISJOINT_ALT', MEM_listpm] \\
     Q.PAT_X_ASSUM ‘DISJOINT (set vs') (FV (tpm pi M0))’ MP_TAC \\
     rw [DISJOINT_ALT', FV_tpm])
 >> DISCH_TAC
 >> ‘LENGTH vs1p = n’ by rw [Abbr ‘vs1p’, LENGTH_listpm]
 (* now create Z and vs2

    Z is the union of all known variables so far, no harm to include even more.
  *)
 >> qabbrev_tac ‘Z = X UNION Y UNION FV M0 UNION set vs UNION set vs1p’
 >> ‘FINITE Z’ by rw [Abbr ‘Z’]
 >> qabbrev_tac ‘vs2 = NEWS n Z’
 >> Know ‘ALL_DISTINCT vs2 /\ DISJOINT (set vs2) Z /\ LENGTH vs2 = n’
 >- rw [Abbr ‘vs2’, NEWS_def]
 >> Q.PAT_X_ASSUM ‘FINITE Z’ K_TAC
 >> qunabbrev_tac ‘Z’
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [DISJOINT_UNION']))
 (* stage work *)
 >> ‘hnf M0’ by PROVE_TAC [hnf_principle_hnf']
 >> hnf_tac (“M0 :term”, “vs2 :string list”,
             “M2 :term”, “y :string”, “args :term list”)
 >> ‘TAKE n vs2 = vs2’ by rw [TAKE_LENGTH_ID_rwt]
 >> POP_ASSUM (rfs o wrap)
 >> ‘hnf M2’ by rw [hnf_appstar]
 >> Know ‘DISJOINT (set vs) (FV M2) /\
          DISJOINT (set vs1p) (FV M2)’
 >- (rpt CONJ_TAC (* 2 subgoals, same tactics *) \\
     (MATCH_MP_TAC DISJOINT_SUBSET \\
      Q.EXISTS_TAC ‘FV M0 UNION set vs2’ \\
      CONJ_TAC >- (Q.PAT_X_ASSUM ‘M0 = LAMl vs2 (VAR y @* args)’ K_TAC \\
                   reverse (rw [DISJOINT_UNION']) >- rw [Once DISJOINT_SYM] \\
                   MATCH_MP_TAC DISJOINT_SUBSET \\
                   Q.EXISTS_TAC ‘FV M’ >> art []) \\
     ‘FV M0 UNION set vs2 = FV (M0 @* MAP VAR vs2)’ by rw [] >> POP_ORW \\
      qunabbrev_tac ‘M2’ \\
      MATCH_MP_TAC principle_hnf_FV_SUBSET' \\
      Know ‘solvable (VAR y @* args)’
      >- (rw [solvable_iff_has_hnf] \\
          MATCH_MP_TAC hnf_has_hnf \\
          rw [hnf_appstar]) >> DISCH_TAC \\
      Suff ‘M0 @* MAP VAR vs2 == VAR y @* args’
      >- PROVE_TAC [lameq_solvable_cong] \\
      rw [lameq_LAMl_appstar_VAR]))
 >> STRIP_TAC
 (* rewriting M1 and M1' (much harder) by tpm of M2 *)
 >> Know ‘M1 = tpm (ZIP (vs2,vs)) M2’
 >- (simp [Abbr ‘M1’] \\
     MATCH_MP_TAC principle_hnf_LAMl_appstar \\
     Q.PAT_X_ASSUM ‘M2 = VAR y @* args’ (ONCE_REWRITE_TAC o wrap o SYM) >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘p1 = ZIP (vs2,vs)’
 >> Know ‘M1' = tpm pi (principle_hnf (M0 @* MAP VAR vs1p))’
 >- (qunabbrev_tac ‘M1'’ \\
     MATCH_MP_TAC principle_hnf_tpm >> art [] \\
     REWRITE_TAC [has_hnf_thm] \\
     Q.EXISTS_TAC ‘(FEMPTY |++ ZIP (vs2,MAP VAR vs1p)) ' (VAR y @* args)’ \\
     CONJ_TAC
     >- (MATCH_MP_TAC hreduce_LAMl_appstar \\
         rw [EVERY_MEM, MEM_MAP] >> rw [] \\
         Q.PAT_X_ASSUM ‘DISJOINT (set vs2) (set vs1p)’ MP_TAC \\
         rw [DISJOINT_ALT']) \\
     REWRITE_TAC [GSYM fromPairs_def] \\
    ‘FDOM (fromPairs vs2 (MAP VAR vs1p)) = set vs2’ by rw [FDOM_fromPairs] \\
     Cases_on ‘MEM y vs2’
     >- (simp [ssub_thm, ssub_appstar, hnf_appstar] \\
         fs [MEM_EL] >> rename1 ‘i < LENGTH vs2’ \\
         Know ‘fromPairs vs2 (MAP VAR vs1p) ' (EL i vs2) = EL i (MAP VAR vs1p)’
         >- (MATCH_MP_TAC fromPairs_FAPPLY_EL >> rw []) >> Rewr' \\
         rw [EL_MAP]) \\
     simp [ssub_thm, ssub_appstar, hnf_appstar])
 >> DISCH_TAC
 >> Know ‘M1' = tpm pi (tpm (ZIP (vs2,vs1p)) M2)’
 >- (POP_ORW >> simp [] \\
     MATCH_MP_TAC principle_hnf_LAMl_appstar \\
     Q.PAT_X_ASSUM ‘M2 = VAR y @* args’ (ONCE_REWRITE_TAC o wrap o SYM) >> art [])
 >> POP_ASSUM K_TAC (* M1' = ... (already used) *)
 >> REWRITE_TAC [GSYM pmact_decompose]
 >> qabbrev_tac ‘p2 = pi ++ ZIP (vs2,vs1p)’
 >> DISCH_TAC
 (* cleanups, the definition details of vs2 are useless *)
 >> Q.PAT_X_ASSUM ‘Abbrev (vs2 = _)’ K_TAC
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
 (* final stage *)
 >> Know ‘?pi'. tpm p2 N = tpm pi' (tpm p1 N)’
 >- (Q.EXISTS_TAC ‘p2 ++ REVERSE p1’ \\
     rw [pmact_decompose])
 >> STRIP_TAC
 >> POP_ORW
 >> qabbrev_tac ‘N' = tpm p1 N’
 (* finally, using IH in a bulk way *)
 >> FIRST_X_ASSUM MATCH_MP_TAC >> rw []
QED

(* NOTE: since ‘subterm X M p’ is correct for whatever X supplied, changing ‘X’ to
   something else shouldn't change the properties of ‘subterm X M p’, as long as
   these properties are not directly related to specific choices of ‘vs’.
 *)
Theorem subterm_tpm_cong :
    !p X Y M. FINITE X /\ FINITE Y ==>
             (subterm X M p = NONE <=> subterm Y M p = NONE) /\
             (subterm X M p <> NONE ==> tpm_rel (subterm' X M p) (subterm' Y M p))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> CONJ_ASM1_TAC
 >- (EQ_TAC >> DISCH_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MP_TAC (Q.SPECL [‘p’, ‘X’, ‘Y’, ‘M’, ‘[]’] subterm_tpm_lemma) >> rw [],
       (* goal 2 (of 2) *)
       MP_TAC (Q.SPECL [‘p’, ‘Y’, ‘X’, ‘M’, ‘[]’] subterm_tpm_lemma) >> rw [] ])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘Y’, ‘M’, ‘[]’] (cj 2 subterm_tpm_lemma))
 >> rw []
QED

(* In this way, two such terms have the same ‘hnf_children_size o principle_hnf’,
   because head reductions are congruence w.r.t. tpm.
 *)
Theorem subterm_hnf_children_size_cong :
    !X Y M p. FINITE X /\ FINITE Y /\
              subterm X M p <> NONE /\ solvable (subterm' X M p) ==>
              hnf_children_size (principle_hnf (subterm' X M p)) =
              hnf_children_size (principle_hnf (subterm' Y M p))
Proof
    rpt STRIP_TAC
 >> ‘subterm Y M p <> NONE /\
     tpm_rel (subterm' X M p) (subterm' Y M p)’ by METIS_TAC [subterm_tpm_cong]
 >> fs [tpm_rel_def]
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
 >> qabbrev_tac ‘N = subterm' X M p’
 >> rw [principle_hnf_tpm']
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
              vs = NEWS (MAX n n') (FV M UNION FV N);
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
       by rw [Abbr ‘vs’, NEWS_def]
 >> ‘vsM = vs’ by rw [Abbr ‘vsM’, TAKE_LENGTH_ID_rwt]
 >> POP_ASSUM (fs o wrap)
 >> Q.PAT_X_ASSUM ‘vs = vsN’ (fs o wrap o SYM)
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘N’, ‘M0’, ‘N0’, ‘n’, ‘vs’, ‘M1’, ‘N1’]
                    lameq_principle_hnf_thm')
 >> simp [Abbr ‘X’]
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
    Induct_on ‘pi’ using SNOC_INDUCT >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> fs [solving_transform_def]
 >- rw [asmlam_rules]
 >> MATCH_MP_TAC asmlam_subst >> art []
QED

Theorem Boehm_apply_lameq_cong :
    !pi M N. Boehm_transform pi /\ M == N ==> apply pi M == apply pi N
Proof
    Induct_on ‘pi’ using SNOC_INDUCT >> rw []
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
 >> Induct_on ‘p2’ using SNOC_INDUCT
 >> rw [APPEND_SNOC]
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
                          vs = NEWS n (FV M0);
                          M1 = principle_hnf (M0 @* MAP VAR vs);
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

(* cf. NEW_TAC (This is the multivariate version)

   NOTE: “FINITE X” must be present in the assumptions or provable by rw [].
 *)
fun NEWS_TAC (vs,n,X) =
    qabbrev_tac ‘^vs = NEWS ^n ^X’
 >> KNOW_TAC “ALL_DISTINCT ^vs /\ DISJOINT (set ^vs) ^X /\ LENGTH ^vs = ^n”
 >- rw [NEWS_def, Abbr ‘^vs’]
 >> STRIP_TAC;

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
     CONJ_ASM1_TAC >- (rw [hnf_appstar]) >> simp [] \\
     RW_TAC std_ss [head_original_def, LAMl_size_hnf_absfree] \\
     qunabbrev_tac ‘n’ \\
    ‘vs = []’ by METIS_TAC [LENGTH_NIL, NEWS_def, FINITE_FV] \\
     POP_ASSUM (fs o wrap) >> qunabbrev_tac ‘vs’ \\
    ‘M1 = VAR y @* Ns’ by rw [principle_hnf_reduce, Abbr ‘M1’] \\
     POP_ORW >> qunabbrev_tac ‘M1’ \\
     simp [hnf_head_hnf, hnf_children_hnf])
 (* stage work *)
 >> rw [is_ready_def] >- art []
 >> DISJ2_TAC
 >> qabbrev_tac ‘n = LAMl_size N’
 >> NEWS_TAC (“vs :string list”, “n :num”, “FV (N :term)”)
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

(* ‘subterm_width M p’ is the maximal number of children of all subterms in form
   ‘subterm X M t’ such that ‘t <<= p’ (prefix). The choice of X is irrelevant.

   In other words, it's the maximal ‘hnf_children_size o pH’ of all terms of the
   form ‘subterm X M t’ such that ‘t <<= FRONT p’ (The pH of ‘subterm X M p’ can
   can be ignored, because its hnf children are never considered.

   NOTE: This definition assumes ‘p <> []’ and ‘p IN ltree_paths (BTe X M)’ and
  ‘subterm X M p <> NONE’, because otherwise there will be no hnf children to
   consider.

   NOTE2: we forcely define ‘subterm_width M [] = 0’ since in this case the width
   is irrelevant. This setting is also perfect for induction.
 *)
Definition subterm_width_def :
    subterm_width M     [] = 0 /\
    subterm_width M (h::t) =
      let Ms = {subterm' {} M p' | p' <<= FRONT (h::t)} in
          MAX_SET (IMAGE (hnf_children_size o principle_hnf) Ms)
End

(* |- !M. subterm_width M [] = 0 *)
Theorem subterm_width_NIL[simp] = cj 1 subterm_width_def

Theorem subterm_width_alt :
    !X M p. FINITE X /\
            p <> [] /\ p IN ltree_paths (BTe X M) /\ subterm X M p <> NONE ==>
            subterm_width M p =
              let Ms = {subterm' X M p' | p' <<= FRONT p} in
                  MAX_SET (IMAGE (hnf_children_size o principle_hnf) Ms)
Proof
    rpt STRIP_TAC
 >> Cases_on ‘p’ >> rw [subterm_width_def]
 >> qabbrev_tac ‘p = h::t’
 (* preparing for subterm_hnf_children_size_cong *)
 >> Know ‘!Y. IMAGE (hnf_children_size o principle_hnf)
                    {subterm' Y M p' | p' <<= FRONT p} =
             {hnf_children_size (principle_hnf (subterm' Y M p')) | p' <<= FRONT p}’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       rename1 ‘q <<= FRONT p’ \\
       Q.EXISTS_TAC ‘q’ >> rw [],
       (* goal 2 (of 2) *)
       rename1 ‘q <<= FRONT p’ \\
       Q.EXISTS_TAC ‘subterm' Y M q’ >> art [] \\
       Q.EXISTS_TAC ‘q’ >> art [] ])
 >> Rewr
 (* applying subterm_hnf_children_size_cong *)
 >> Suff ‘{hnf_children_size (principle_hnf (subterm' {} M p')) | p' <<= FRONT p} =
          {hnf_children_size (principle_hnf (subterm' X M p')) | p' <<= FRONT p}’
 >- Rewr
 >> Suff ‘!q. q <<= FRONT p ==>
              hnf_children_size (principle_hnf (subterm' X M q)) =
              hnf_children_size (principle_hnf (subterm' {} M q))’
 >- (DISCH_TAC \\
     rw [Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       rename1 ‘q <<= FRONT p’ \\
       Q.EXISTS_TAC ‘q’ >> rw [],
       (* goal 2 (of 2) *)
       rename1 ‘q <<= FRONT p’ \\
       Q.EXISTS_TAC ‘q’ >> rw [] ])
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC subterm_hnf_children_size_cong
 >> simp []
 >> ‘p <> []’ by rw [Abbr ‘p’]
 (* applying subterm_solvable_lemma *)
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘p’] subterm_solvable_lemma)
 >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> MATCH_MP_TAC IS_PREFIX_TRANS
 >> Q.EXISTS_TAC ‘FRONT p’ >> art []
 >> MATCH_MP_TAC IS_PREFIX_BUTLAST' >> art []
QED

(* NOTE: The actual difficulty of this theorem is to prove that

   |- !X Y. hnf_children_size (principle_hnf (subterm' X M p) =
            hnf_children_size (principle_hnf (subterm' Y M p)
 *)
Theorem subterm_width_thm :
    !X M p p'. FINITE X /\
               p <> [] /\ p IN ltree_paths (BTe X M) /\ subterm X M p <> NONE /\
               p' <<= FRONT p ==>
       hnf_children_size (principle_hnf (subterm' X M p')) <= subterm_width M p
Proof
    rpt STRIP_TAC
 >> Cases_on ‘p’
 >> RW_TAC std_ss [subterm_width_def]
 >> qabbrev_tac ‘p = h::t’
 >> ‘p <> []’ by rw [Abbr ‘p’]
 >> ‘0 < LENGTH p’ by rw [GSYM NOT_NIL_EQ_LENGTH_NOT_0]
 >> qabbrev_tac ‘J = IMAGE (hnf_children_size o principle_hnf) Ms’
 >> Know ‘J <> {}’
 >- (rw [Abbr ‘J’, GSYM MEMBER_NOT_EMPTY, Abbr ‘Ms’] \\
     Q.EXISTS_TAC ‘[]’ >> rw [])
 >> DISCH_TAC
 >> Know ‘FINITE J’
 >- (qunabbrev_tac ‘J’ >> MATCH_MP_TAC IMAGE_FINITE \\
    ‘Ms = IMAGE (subterm' {} M) {p' | p' <<= FRONT p}’
       by (rw [Abbr ‘Ms’, Once EXTENSION]) >> POP_ORW \\
     MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 >> DISCH_TAC
 >> qabbrev_tac ‘m = hnf_children_size (principle_hnf (subterm' X M p'))’
 >> Suff ‘m IN J’ >- PROVE_TAC [MAX_SET_DEF]
 >> rw [Abbr ‘m’, Abbr ‘J’]
 >> Q.EXISTS_TAC ‘subterm' {} M p'’
 >> reverse CONJ_TAC
 >- (rw [Abbr ‘Ms’] >> Q.EXISTS_TAC ‘p'’ >> art [])
 >> ‘!p'. p' <<= p ==> subterm X M p' <> NONE’
       by PROVE_TAC [cj 1 subterm_solvable_lemma]
 (* applying subterm_hnf_children_size_cong *)
 >> MATCH_MP_TAC subterm_hnf_children_size_cong >> rw []
 >- (POP_ASSUM MATCH_MP_TAC \\
     MATCH_MP_TAC IS_PREFIX_TRANS \\
     Q.EXISTS_TAC ‘FRONT p’ >> art [] \\
     MATCH_MP_TAC IS_PREFIX_BUTLAST' >> art [])
 >> PROVE_TAC [cj 2 subterm_solvable_lemma]
QED

(* NOTE: This lemma does not hold without ‘v IN X’. *)
Theorem subterm_subst_cong_lemma[local] :
    !l X M p. l <<= p /\ FINITE X /\ v IN X /\
              p IN ltree_paths (BTe X M) /\ subterm X M p <> NONE /\
              P = permutator d /\ subterm_width M p <= d
          ==> subterm X ([P/v] M) l <> NONE /\
              tpm_rel (subterm' X ([P/v] M) l) ([P/v] (subterm' X M l))
Proof
    Induct_on ‘l’ >- rw []
 >> rpt GEN_TAC >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘P = permutator d’ (fs o wrap)
 >> qabbrev_tac ‘P = permutator d’
 >> Cases_on ‘p = []’ >- fs []
 (* common properties of ‘p’ *)
 >> ‘(!q. q <<= p ==> subterm X M q <> NONE) /\
     (!q. q <<= FRONT p ==> solvable (subterm' X M q))’
       by PROVE_TAC [subterm_solvable_lemma]
 >> qabbrev_tac ‘w = subterm_width M p’
 (* rewriting ‘h::l <<= p’ *)
 >> Cases_on ‘p’ >> fs []
 >> Q.PAT_X_ASSUM ‘h = h'’ (fs o wrap o SYM)
 >> rpt (Q.PAT_X_ASSUM ‘T’ K_TAC)
 >> Know ‘solvable M’
 >- (Q.PAT_X_ASSUM ‘!q. q <<= FRONT (h::t) ==> solvable (subterm' X M q)’
       (MP_TAC o (Q.SPEC ‘[]’)) >> rw [])
 >> DISCH_TAC
 >> Know ‘subterm X M (h::l) <> NONE’
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw [])
 (* BEGIN Michael Norrish's tactics *)
 >> CONV_TAC (UNBETA_CONV “subterm X M (h::l)”)
 >> qmatch_abbrev_tac ‘f _’
 >> RW_TAC bool_ss [subterm_of_solvables]
 >> simp [Abbr ‘f’]
 (* END Michael Norrish's tactics. *)
 >> STRIP_TAC
 (* getting explicit representation of M0 *)
 >> Know ‘ALL_DISTINCT vs /\ DISJOINT (set vs) (X UNION FV M0) /\ LENGTH vs = n’
 >- rw [Abbr ‘vs’, NEWS_def]
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [DISJOINT_UNION']))
 >> ‘hnf M0’ by PROVE_TAC [hnf_principle_hnf']
 >> qunabbrev_tac ‘M1’
 >> hnf_tac (“M0 :term”, “vs :string list”,
             “M1 :term”, “y :string”, “args :term list”)
 >> ‘TAKE n vs = vs’ by rw [TAKE_LENGTH_ID_rwt]
 >> POP_ASSUM (rfs o wrap)
 >> Know ‘m <= w’
 >- (MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::t’, ‘[]’] subterm_width_thm) \\
     rw [Abbr ‘w’])
 >> DISCH_TAC
 >> ‘Ms = args’ by rw [Abbr ‘Ms’, hnf_children_hnf]
 >> ‘LENGTH args = m’ by rw [Abbr ‘m’]
 (* KEY: some shared subgoals needed at the end, before rewriting ‘[P/v] M’:

    1. t IN ltree_paths (BTe (X UNION set vs) (EL h args))
    2. subterm (X UNION set vs) (EL h args) t <> NONE
    3. subterm_width (EL h args) t <= d

    NOTE: the last subgoal requires deep properties of ‘subterm_width’. The
    involved tactics are not to be repeated in other parts of this lemma.
  *)
 >> Know ‘t IN ltree_paths (BTe (X UNION set vs) (EL h args)) /\
          subterm (X UNION set vs) (EL h args) t <> NONE /\
          subterm_width (EL h args) t <= d’
 >- (CONJ_ASM1_TAC (* t IN ltree_paths ... *)
     >- (Q.PAT_X_ASSUM ‘h::t IN ltree_paths (BTe X M)’ MP_TAC \\
         simp [ltree_paths_def, ltree_lookup] \\
         Know ‘BTe X M = ltree_unfold BT_generator (X,M)’ >- rw [BT_def] \\
         simp [Once ltree_unfold, BT_generator_def, LNTH_fromList] \\
         rw [GSYM BT_def, EL_MAP, hnf_children_hnf]) \\
     CONJ_ASM1_TAC (* subterm (X UNION set vs) (EL h args) t <> NONE *)
     >- (Q.PAT_X_ASSUM ‘!q. q <<= h::t ==> subterm X M q <> NONE’
           (MP_TAC o (Q.SPEC ‘h::t’)) \\
         simp [subterm_of_solvables] >> fs []) \\
  (* goal: subterm_width (EL h args) t <= d *)
     MATCH_MP_TAC LESS_EQ_TRANS \\
     Q.EXISTS_TAC ‘w’ >> art [] \\
     qunabbrev_tac ‘w’ \\
  (* applying subterm_width_alt *)
     MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::t’] subterm_width_alt) \\
     simp [] >> DISCH_THEN K_TAC \\
     qabbrev_tac ‘p = h::t’ \\
     Know ‘!Y. IMAGE (hnf_children_size o principle_hnf)
                     {subterm' Y M p' | p' <<= FRONT p} =
               {hnf_children_size (principle_hnf (subterm' Y M p')) | p' <<= FRONT p}’
     >- (rw [Once EXTENSION] \\
         EQ_TAC >> rw [] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           rename1 ‘q <<= FRONT p’ \\
           Q.EXISTS_TAC ‘q’ >> rw [],
           (* goal 2 (of 2) *)
           rename1 ‘q <<= FRONT p’ \\
           Q.EXISTS_TAC ‘subterm' Y M q’ >> art [] \\
           Q.EXISTS_TAC ‘q’ >> art [] ]) >> Rewr' \\
     qunabbrev_tac ‘p’ \\
     Cases_on ‘t = []’ >- rw [] \\
  (* applying subterm_width_alt again *)
     MP_TAC (Q.SPECL [‘X UNION set vs’, ‘EL h args’, ‘t’] subterm_width_alt) \\
     simp [] >> DISCH_THEN K_TAC \\
  (* applying SUBSET_MAX_SET *)
     MATCH_MP_TAC SUBSET_MAX_SET \\
     CONJ_TAC >- (MATCH_MP_TAC IMAGE_FINITE \\
                 ‘{subterm' (X UNION set vs) (EL h args) p' | p' <<= FRONT t} =
                  IMAGE (subterm' (X UNION set vs) (EL h args))
                        {p' | p' <<= FRONT t}’
                     by rw [Once EXTENSION] >> POP_ORW \\
                  MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix]) \\
     CONJ_TAC >- (‘{hnf_children_size (principle_hnf (subterm' X M p')) |
                    p' <<= FRONT (h::t)} =
                   IMAGE (\p'. hnf_children_size (principle_hnf (subterm' X M p')))
                         {p' | p' <<= FRONT (h::t)}’
                     by rw [Once EXTENSION] >> POP_ORW \\
                  MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix]) \\
     rw [SUBSET_DEF] (* this asserts ‘p' <<= FRONT t’ *) \\
     Q.EXISTS_TAC ‘h::p'’ \\
    ‘FRONT (h::t) <> []’ by rw [] \\
     Know ‘h::p' <<= FRONT (h::t)’
     >- (simp [] >> Cases_on ‘t’ >> fs []) >> Rewr \\
  (* Michael Norrish's tactics *)
     CONV_TAC (UNBETA_CONV “subterm X M (h::p')”) \\
     qmatch_abbrev_tac ‘f _’ \\
     RW_TAC bool_ss [subterm_of_solvables] \\
     simp [Abbr ‘f’, hnf_children_hnf])
 >> STRIP_TAC
 (* NOTE: This is how ‘v IN X’ gets used in this proof *)
 >> Know ‘~MEM v vs’
 >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) X’ MP_TAC \\
     rw [DISJOINT_ALT'])
 >> DISCH_TAC
 (* NOTE: ‘[P/v] M’ is solvable iff ‘[P/v] M0’ is solvable, the latter is either
    already a hnf (v <> y), or can be head-reduced to a hnf (v = y).
  *)
 >> Know ‘solvable ([P/v] M)’
 >- (‘M0 == M’ by rw [Abbr ‘M0’, lameq_principle_hnf'] \\
     ‘[P/v] M0 == [P/v] M’ by rw [lameq_sub_cong] \\
     Suff ‘solvable ([P/v] M0)’ >- PROVE_TAC [lameq_solvable_cong] \\
    ‘FV P = {}’ by rw [Abbr ‘P’, FV_permutator] \\
    ‘DISJOINT (set vs) (FV P)’ by rw [DISJOINT_ALT'] \\
     simp [LAMl_SUB, appstar_SUB] \\
     reverse (Cases_on ‘y = v’)
     >- (simp [SUB_THM, solvable_iff_has_hnf] \\
         MATCH_MP_TAC hnf_has_hnf >> rw [hnf_appstar]) \\
     simp [solvable_iff_has_hnf, has_hnf_thm] \\
     qabbrev_tac ‘args' = MAP [P/v] args’ \\
    ‘LENGTH args' = m’ by rw [Abbr ‘args'’] \\
  (* applying permutator_hreduce_thm *)
     MP_TAC (Q.SPECL [‘{}’, ‘d’, ‘args'’] permutator_hreduce_thm) \\
     rw [Abbr ‘P’] \\
     Q.EXISTS_TAC ‘LAMl xs (LAM y (VAR y @* args' @* MAP VAR xs))’ \\
     rw [hnf_appstar, hnf_thm])
 >> DISCH_TAC
 (* Now we need to know the exact form of ‘principle_hnf ([P/v] M)’.

    First of all, we know that ‘principle_hnf M = LAMl vs (VAR y @* args)’. This
    means ‘M -h->* LAMl vs (VAR y @* args)’. Meanwhile, -h->* is substitutive,
    thus ‘[P/v] M -h->* [P/v] LAMl vs (VAR y @* args)’. Depending on the nature
    of ‘v’, the ending term ‘[P/v] LAMl vs (VAR y @* args)’ may or may not be
    a hnf. But it indeed has a hnf, as ‘solvable ([P/v] M)’ has been proved.

    Case 1 (MEM v vs): This case is false, but is eliminated by adding ‘v IN X’
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
 >> POP_ASSUM K_TAC (* DISJOINT (set vs) (FV P) *)
 >> qabbrev_tac ‘args' = MAP [P/v] args’
 >> ‘LENGTH args' = LENGTH args’ by rw [Abbr ‘args'’]
 (* shared properties of args and args' *)
 >> Know ‘!i. i < m ==> FV (EL i args) = FV (EL i args') \/
                        FV (EL i args) = v INSERT FV (EL i args')’
 >- (rpt STRIP_TAC \\
     Know ‘EL i args' = [P/v] (EL i args)’
     >- (rw [Abbr ‘args'’, EL_MAP]) >> Rewr' \\
     qabbrev_tac ‘N = EL i args’ \\
     qabbrev_tac ‘N' = EL i args'’ \\
    ‘FV P = {}’ by rw [Abbr ‘P’, FV_permutator] \\
     simp [FV_SUB] \\
     Cases_on ‘v IN FV N’ >> simp [])
 >> DISCH_TAC
 (* s and s' will appear later *)
 >> qabbrev_tac ‘s  = BIGUNION (IMAGE FV (set args))’
 >> qabbrev_tac ‘s' = BIGUNION (IMAGE FV (set args'))’
 >> Know ‘s = s' \/ s = v INSERT s'’
 >- (Q.PAT_X_ASSUM ‘Ms = args’ K_TAC \\
     Cases_on ‘!i. i < m ==> FV (EL i args) = FV (EL i args')’
     >- (DISJ1_TAC \\
         rw [Abbr ‘s’, Abbr ‘s'’, Once EXTENSION, IN_BIGUNION_IMAGE] \\
         EQ_TAC >> rw [MEM_EL] >| (* 2 symmetric subgoals *)
         [ (* goal 1 (of 2) *)
           Q.EXISTS_TAC ‘EL n args'’ \\
           reverse CONJ_TAC >- (Suff ‘FV (EL n args') = FV (EL n args)’
                                >- DISCH_THEN (art o wrap) >> rw []) \\
           Q.EXISTS_TAC ‘n’ >> art [],
           (* goal 2 (of 2) *)
           Q.EXISTS_TAC ‘EL n args’ \\
           reverse CONJ_TAC >- (Suff ‘FV (EL n args) = FV (EL n args')’
                                >- DISCH_THEN (art o wrap) >> rw []) \\
           Q.EXISTS_TAC ‘n’ >> art [] ]) \\
     fs [] (* This asserts ‘i’ such that ‘FV (EL i args) <> FV (EL i args')’ *) \\
    ‘FV (EL i args) = v INSERT FV (EL i args')’ by PROVE_TAC [] \\
     DISJ2_TAC \\
     rw [Abbr ‘s’, Abbr ‘s'’, Once EXTENSION, IN_BIGUNION_IMAGE] \\
     EQ_TAC >> rw [MEM_EL] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       Cases_on ‘x = v’ >> rw [] \\
       Q.PAT_X_ASSUM ‘x IN FV (EL n Ms)’ MP_TAC \\
      ‘FV (EL n Ms) = FV (EL n args') \/
       FV (EL n Ms) = v INSERT FV (EL n args')’ by PROVE_TAC []
       >- (rw [] \\
           Q.EXISTS_TAC ‘EL n args'’ >> art [] \\
           Q.EXISTS_TAC ‘n’ >> art []) \\
       rw [] \\
       Q.EXISTS_TAC ‘EL n args'’ >> art [] \\
       Q.EXISTS_TAC ‘n’ >> art [],
       (* goal 2 (of 3) *)
       Q.EXISTS_TAC ‘EL i Ms’ \\
       CONJ_TAC >- (Q.EXISTS_TAC ‘i’ >> art []) \\
       POP_ORW >> rw [],
       (* goal 2 (of 3) *)
       Q.EXISTS_TAC ‘EL n Ms’ \\
       CONJ_TAC >- (Q.EXISTS_TAC ‘n’ >> art []) \\
       Suff ‘FV (EL n args') SUBSET FV (EL n Ms)’ >- rw [SUBSET_DEF] \\
      ‘FV (EL n Ms) = FV (EL n args') \/
       FV (EL n Ms) = v INSERT FV (EL n args')’ by PROVE_TAC [] >- rw [] \\
       POP_ORW >> SET_TAC [] ])
 >> DISCH_TAC
 (* LHS rewriting of args'

    NOTE: until this moment, the "X" of ‘subterm X ([P/v] M) (h::l)’
    can be anything else.
  *)
 >> CONV_TAC (UNBETA_CONV “subterm X ([P/v] M) (h::l)”)
 >> qmatch_abbrev_tac ‘f _’
 >> ASM_SIMP_TAC std_ss [subterm_of_solvables]
 >> LET_ELIM_TAC
 >> Q.PAT_X_ASSUM ‘subterm _ (EL h (hnf_children M1)) l <> NONE’ MP_TAC
 >> simp [Abbr ‘f’, hnf_children_hnf]
 >> DISCH_TAC (* subterm (X UNION set vs) (EL h args) l <> NONE *)
 (* Case 2 *)
 >> reverse (Cases_on ‘y = v’)
 >- (‘FV P = {}’ by rw [Abbr ‘P’, FV_permutator] \\
     ‘DISJOINT (set vs) (FV P)’ by rw [DISJOINT_ALT'] \\
     simp [LAMl_SUB, appstar_SUB] \\
     DISCH_TAC (* [P/v] M -h->* LAMl vs (VAR y @* args') *) \\
    ‘hnf (LAMl vs (VAR y @* args'))’ by rw [hnf_appstar] \\
    ‘M0' = LAMl vs (VAR y @* args')’ by METIS_TAC [principle_hnf_thm'] \\
     Know ‘m' = m’
     >- (qunabbrevl_tac [‘m’, ‘m'’] >> art [] \\
         Q.PAT_X_ASSUM ‘LENGTH args = hnf_children_size M0’ K_TAC \\
         simp [hnf_children_size_appstar, Abbr ‘args'’]) \\
     DISCH_TAC \\
     Q.PAT_X_ASSUM ‘s = s' \/ s = v INSERT s'’ MP_TAC \\
     POP_ASSUM (fs o wrap) (* m' = m *) \\
     qunabbrev_tac ‘m'’ \\
     qunabbrev_tac ‘n'’ >> rfs [] \\
     rpt (Q.PAT_X_ASSUM ‘T’ K_TAC) \\
     DISCH_TAC (* s = s' \/ s = v INSERT s' *) \\
     Know ‘vs' = vs’
     >- (Suff ‘X UNION FV (LAMl vs (VAR y @* args)) =
               X UNION FV (LAMl vs (VAR y @* args'))’ >- DISCH_THEN (fs o wrap) \\
         simp [FV_LAMl, FV_appstar] \\
         fs [] (* only ‘s = v INSERT s'’ is left *) \\
         Q.PAT_X_ASSUM ‘v IN X’ MP_TAC \\
         SET_TAC [] (* amazing ... *)) \\
     POP_ASSUM K_TAC (* s = s' \/ ... *) \\
     DISCH_THEN (fs o wrap) >> qunabbrev_tac ‘vs'’ \\
     fs [principle_hnf_beta_reduce, hnf_appstar] \\
     fs [Abbr ‘M1'’, hnf_children_hnf] \\
     Q.PAT_X_ASSUM ‘args' = Ms'’ (fs o wrap o SYM) \\
     rpt (Q.PAT_X_ASSUM ‘T’ K_TAC) \\
  (* now applying IH *)
     simp [Abbr ‘m’, Abbr ‘args'’, EL_MAP, Abbr ‘P’] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘t’ >> simp [])
 (* Case 3 *)
 >> Q.PAT_X_ASSUM ‘s = s' \/ s = v INSERT s'’ MP_TAC
 >> POP_ASSUM (fs o wrap o SYM) (* y = v *)
 >> simp [Abbr ‘P’]
 >> DISCH_TAC (* s = s' \/ s = y INSERT s' *)
 >> DISCH_TAC (* [permutator d/y] M -h->* ... *)
 (* applying permutator_hreduce_thm with a suitable excluded list

    NOTE: ‘vs'’ is to be proved extending vs (vs' = vs ++ ys), and we will need
          DISJOINT (set (SNOC z xs)) (set ys), thus here ‘set vs'’ is used.
  *)
 >> MP_TAC (Q.SPECL [‘set vs'’, ‘d’, ‘args'’] permutator_hreduce_thm)
 >> simp []
 >> STRIP_TAC >> rename1 ‘ALL_DISTINCT (SNOC z xs)’
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
 >> Q.PAT_X_ASSUM ‘permutator d @* args' -h->* _’ K_TAC
 >> NTAC 2 (Q.PAT_X_ASSUM ‘[permutator d/y] M -h->* _’ K_TAC)
 (* NOTE: this proof includes ‘m <= m'’ *)
 >> Know ‘h < m'’
 >- (MATCH_MP_TAC LESS_LESS_EQ_TRANS \\
     Q.EXISTS_TAC ‘m’ >> art [] \\
     Q.PAT_X_ASSUM ‘LENGTH args = m’ K_TAC \\
     simp [Abbr ‘m’, Abbr ‘m'’, GSYM appstar_APPEND])
 >> Rewr
 (* NOTE: now we show that vs and vs' are generated from the same excluded list.
    For this purpose, hreduce_LAMl_appstar has been enhanced to provide extra
    disjointness information for xs and z.
  *)
 >> Know ‘X UNION FV M0' = X UNION FV M0’
 >- (simp [FV_LAMl, FV_appstar] \\
     qabbrev_tac ‘Z = {z} UNION s' UNION set xs DELETE z DIFF set xs’ \\
     Know ‘Z = s'’
     >- (qunabbrev_tac ‘Z’ \\
         Suff ‘z NOTIN s' /\ set xs INTER s' = {}’ >- SET_TAC [] \\
         REWRITE_TAC [GSYM DISJOINT_DEF] \\
         Suff ‘DISJOINT (set (SNOC z xs)) s'’
         >- simp [LIST_TO_SET_SNOC, DISJOINT_UNION] \\
         qabbrev_tac ‘l' = SNOC z xs’ \\
         simp [DISJOINT_ALT', Abbr ‘s'’, IN_BIGUNION_IMAGE] \\
         NTAC 2 STRIP_TAC \\
         rename1 ‘s1 = FV N’ \\
         Q.PAT_X_ASSUM ‘s1 = FV N’ (ONCE_REWRITE_TAC o wrap) \\
         Q.PAT_X_ASSUM ‘!N. MEM N args' ==> DISJOINT (FV N) (set l')’
           (MP_TAC o (Q.SPEC ‘N’)) \\
         rw [DISJOINT_ALT]) >> Rewr' \\
     qunabbrev_tac ‘Z’ \\
     Q.PAT_X_ASSUM ‘y IN X’ MP_TAC \\
     fs [] >> SET_TAC [])
 >> Q.PAT_X_ASSUM ‘!i. i < m ==> _’           K_TAC
 >> Q.PAT_X_ASSUM ‘s = s' \/ s = y INSERT s'’ K_TAC
 >> qunabbrevl_tac [‘s’, ‘s'’]
 >> Q.PAT_X_ASSUM ‘M0 = _’          (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = _’          (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M0' = LAMl vs _’ (ASSUME_TAC o SYM)
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
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
 >> Know ‘ALL_DISTINCT vs' /\ DISJOINT (set vs') (X UNION FV M0) /\ LENGTH vs' = n'’
 >- rw [Abbr ‘vs'’, NEWS_def]
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [DISJOINT_UNION']))
 (* applying NEWS_prefix !!! *)
 >> Know ‘vs <<= vs'’
 >- (qunabbrevl_tac [‘vs’, ‘vs'’] \\
     MATCH_MP_TAC NEWS_prefix >> rw [])
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [IS_PREFIX_APPEND]))
 >> rename1 ‘vs' = vs ++ ys’
 >> POP_ASSUM (fn th => rfs [th, MAP_APPEND, appstar_APPEND, LIST_TO_SET_APPEND,
                             ALL_DISTINCT_APPEND])
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
 >> Know ‘LAMl xs' t' @* MAP VAR ys -h->* (FEMPTY |++ ZIP (xs',MAP VAR ys)) ' t'’
 >- (MATCH_MP_TAC hreduce_LAMl_appstar >> simp [Abbr ‘xs'’] \\
     rw [EVERY_MEM, MEM_MAP] >> REWRITE_TAC [FV_thm] \\
     MATCH_MP_TAC DISJOINT_SUBSET' \\
     Q.EXISTS_TAC ‘set ys’ >> art [] \\
     rw [SUBSET_DEF])
 >> REWRITE_TAC [GSYM fromPairs_def]
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
     qabbrev_tac ‘l' = SNOC z xs’ \\
     Know ‘z = LAST l'’ >- rw [Abbr ‘l'’, LAST_SNOC] \\
    ‘l' <> []’ by rw [Abbr ‘l'’] \\
     simp [LAST_EL] >> DISCH_THEN K_TAC \\
     qabbrev_tac ‘i = PRE (LENGTH l')’ \\
     Q.EXISTS_TAC ‘EL i ys’ \\
    ‘i < LENGTH ys’ by rw [Abbr ‘i’, Abbr ‘l'’] \\
    ‘VAR (EL i ys) :term = EL i (MAP VAR ys)’ by rw [EL_MAP] >> POP_ORW \\
     MATCH_MP_TAC fromPairs_FAPPLY_EL \\
     simp [Abbr ‘i’, Abbr ‘l'’])
 >> STRIP_TAC >> POP_ORW
 >> qabbrev_tac ‘l' = MAP ($' fm) (MAP VAR xs)’ (* irrelevant list *)
 >> DISCH_TAC
 >> Know ‘M0' @* MAP VAR vs @* MAP VAR ys -h->* VAR z' @* (args' ++ l')’
 >- (REWRITE_TAC [appstar_APPEND] \\
     PROVE_TAC [hreduce_TRANS])
 >> Q.PAT_X_ASSUM ‘M0' @* MAP VAR vs @* MAP VAR ys -h->* _’ K_TAC
 >> Q.PAT_X_ASSUM ‘_ -h->* VAR z' @* args' @* l'’           K_TAC
 >> DISCH_TAC
 >> ‘hnf (VAR z' @* (args' ++ l'))’ by rw [hnf_appstar]
 >> ‘has_hnf (M0' @* MAP VAR vs @* MAP VAR ys)’ by PROVE_TAC [has_hnf_thm]
 (* finall we got the explicit form of M1' *)
 >> ‘M1' = VAR z' @* (args' ++ l')’ by METIS_TAC [principle_hnf_thm]
 >> Q.PAT_X_ASSUM ‘M0' @* MAP VAR vs @* MAP VAR ys -h->* _’ K_TAC
 >> Know ‘EL h Ms' = EL h args'’
 >- (simp [Abbr ‘Ms'’, hnf_children_hnf] \\
     MATCH_MP_TAC EL_APPEND1 >> art [])
 >> Rewr'
 (* cleanup args', l' and fm *)
 >> Q.PAT_X_ASSUM ‘!N. MEM N args' ==> _’         K_TAC
 >> Q.PAT_X_ASSUM ‘hnf (VAR z' @* (args' ++ l'))’ K_TAC
 >> Q.PAT_X_ASSUM ‘M1' = VAR z' @* (args' ++ l')’ K_TAC
 >> Q.PAT_X_ASSUM ‘LENGTH args' = m’              K_TAC
 >> Q.PAT_X_ASSUM ‘FDOM fm = set (SNOC z xs)’     K_TAC
 >> qunabbrev_tac ‘l'’
 >> qunabbrev_tac ‘fm’
 >> simp [Abbr ‘args'’, EL_MAP]
 >> Q.PAT_X_ASSUM ‘args = Ms’ (fs o wrap o SYM)
 >> qabbrev_tac ‘N = EL h args’
 >> qabbrev_tac ‘P = permutator d’
 (* NOTE: left side has ‘X UNION (set vs UNION set ys)’ and
          right side RHS has ‘X UNION set vs’... *)
 >> REWRITE_TAC [UNION_ASSOC]
 >> qabbrev_tac ‘Y = X UNION set vs’
 >> ‘FINITE Y’ by rw [Abbr ‘Y’]
 >> qabbrev_tac ‘Z = Y UNION set ys’
 >> ‘FINITE Z’ by rw [Abbr ‘Z’]
 >> Suff ‘subterm Y ([P/y] N) l <> NONE /\
          tpm_rel (subterm' Y ([P/y] N) l) ([P/y] (subterm' Y N l))’
 >- (STRIP_TAC \\
     CONJ_ASM1_TAC >- PROVE_TAC [subterm_tpm_cong] \\
  (* applying tpm_rel_cong and subterm_tpm_cong *)
     Suff ‘tpm_rel (subterm' Z ([P/y] N) l) ([P/y] (subterm' Y N l)) <=>
           tpm_rel (subterm' Y ([P/y] N) l) ([P/y] (subterm' Y N l))’ >- rw [] \\
     MATCH_MP_TAC tpm_rel_cong >> simp [] \\
     PROVE_TAC [subterm_tpm_cong])
 (* applying IH, finally *)
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘l’ >> simp []
 >> CONJ_TAC >- rw [Abbr ‘Y’] (* y IN Y *)
 (* applying ltree_paths_inclusive *)
 >> CONJ_ASM1_TAC (* l IN ltree_paths ... *)
 >- (MATCH_MP_TAC ltree_paths_inclusive \\
     Q.EXISTS_TAC ‘t’ >> art [])
 (* final goal *)
 >> MATCH_MP_TAC LESS_EQ_TRANS
 >> Q.EXISTS_TAC ‘w’ >> art []
 >> qunabbrevl_tac [‘N’, ‘w’]
 (* applying subterm_width_alt *)
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::t’] subterm_width_alt)
 >> simp [] >> DISCH_THEN K_TAC
 >> qabbrev_tac ‘p = h::t’
 >> Know ‘IMAGE (hnf_children_size o principle_hnf)
                {subterm' X M p' | p' <<= FRONT p} =
          {hnf_children_size (principle_hnf (subterm' X M p')) | p' <<= FRONT p}’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       rename1 ‘q <<= FRONT p’ \\
       Q.EXISTS_TAC ‘q’ >> rw [],
       (* goal 2 (of 2) *)
       rename1 ‘q <<= FRONT p’ \\
       Q.EXISTS_TAC ‘subterm' X M q’ >> art [] \\
       Q.EXISTS_TAC ‘q’ >> art [] ])
 >> Rewr'
 >> qunabbrev_tac ‘p’
 (* if t = [], then l = [] *)
 >> Cases_on ‘t = []’ >- fs []
 >> Cases_on ‘l = []’ >> rw []
 (* applying subterm_width_alt again *)
 >> MP_TAC (Q.SPECL [‘X UNION set vs’, ‘EL h args’, ‘l’] subterm_width_alt)
 >> simp [] >> DISCH_THEN K_TAC
 (* applying SUBSET_MAX_SET *)
 >> MATCH_MP_TAC SUBSET_MAX_SET
 >> CONJ_TAC (* FINITE #1 *)
 >- (MATCH_MP_TAC IMAGE_FINITE \\
    ‘{subterm' Y (EL h args) p' | p' <<= FRONT l} =
       IMAGE (subterm' Y (EL h args)) {p' | p' <<= FRONT l}’
       by rw [Once EXTENSION] >> POP_ORW \\
     MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 >> CONJ_TAC (* FINITE #2 *)
 >- (‘{hnf_children_size (principle_hnf (subterm' X M p')) | p' <<= FRONT (h::t)} =
         IMAGE (\p'. hnf_children_size (principle_hnf (subterm' X M p')))
               {p' | p' <<= FRONT (h::t)}’
       by rw [Once EXTENSION] >> POP_ORW \\
     MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 >> rw [SUBSET_DEF] (* this asserts ‘p' <<= FRONT l’ *)
 >> Q.EXISTS_TAC ‘h::p'’
 >> ‘FRONT (h::t) <> []’ by rw []
 >> Know ‘h::p' <<= FRONT (h::t)’
 >- (simp [] >> Cases_on ‘t’ >> fs [] \\
     MATCH_MP_TAC IS_PREFIX_TRANS \\
     Q.EXISTS_TAC ‘FRONT l’ >> rw [] \\
     MATCH_MP_TAC IS_PREFIX_FRONT_MONO >> rw [])
 >> Rewr
 (* Michael Norrish's tactics *)
 >> CONV_TAC (UNBETA_CONV “subterm X M (h::p')”)
 >> qmatch_abbrev_tac ‘f _’
 >> RW_TAC bool_ss [subterm_of_solvables]
 >> simp [Abbr ‘f’, hnf_children_hnf]
QED

(* NOTE: ‘y IN X’ must hold to make sure that ‘~MEM y vs’, where ‘set vs’ is disjoint
          with X, otherwise disaster happens.

   How to make sure ‘y IN X’? When calling this theorem, X should be a combination of
   the following sets:

   1. The original X from the caller theorem, which is arbitrary.
   2. FV M, the free variables of M, which contains ‘FV M0’ (principle_hnf of M)
   3. ‘set vs’, which is defined by ‘NEWS n (X UNION FV M)’

   The head variable ‘y’ of M0 (= LAMl vs (VAR y @* args)) must come from 2 and 3
 *)
Theorem subterm_subst_cong :
    !p X M y P d. FINITE X /\ y IN X /\
                  p IN ltree_paths (BTe X M) /\ subterm X M p <> NONE /\
                  P = permutator d /\ subterm_width M p <= d ==>
                  subterm X ([P/y] M) p <> NONE /\
                  tpm_rel (subterm' X ([P/y] M) p) ([P/y] (subterm' X M p))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Cases_on ‘p = []’ >- rw []
 >> MATCH_MP_TAC subterm_subst_cong_lemma
 >> Q.EXISTS_TAC ‘p’ >> rw []
QED

(* Lemma 10.3.6 (ii) [1, p.247]:

   NOTE: The construction of ‘pi’ needs a fixed ltree path ‘p’, so that we can
   collect the maximum number of children in all nodes along ‘p’.  In another
   word, there exists no universal ‘pi’ for which the conclusion holds for
   arbitrary ‘p’.

   NOTE2: Added ‘subterm X M p <> NONE’ to antecedents so that ‘subterm' X M p’
   is defined/specified. ‘subterm X (apply pi M) p <> NONE’ can be derived.

   NOTE3: ‘p <> []’ must be added into antecedents, otherwise the statement
   becomes:

   [...] |- !X M. ?pi. Boehm_transform pi /\ is_ready (apply pi M) /\
                       ?fm. apply pi M == fm ' M

   which is impossible if M is not already "is_ready".

   NOTE4: The precise forms of Z and Z' in the conclusion, are:

          Z  = X UNION FV M UNION set vs
          Z' = X UNION FV M

   where  vs = NEWS (LAMl_size (principle_hnf M) (X UNION FV M)) = f (X,M)
         (vs is function of X and M, assuming M is solvable, otherwise trivial.)

   NOTE5: It's possible that the two terms in the final conclusion:

   1. subterm' Z (apply pi M) p
   2. fm ' (subterm' Z' M p)

   are not equal, nor are they beta-equivalent, but they differ by a tpm!

   NOTE6: In general ‘apply pi M’ is not solvable even if M is solable (see also
         [Boehm_apply_unsolvable], but in this case it is, and this is needed in
         [Boehm_out_lemma] when rewriting ‘apply pi M’ to explicit forms using
         [is_ready_alt] (assuming M is solvable). The extra conclusion is added:
         ‘solvable M ==> solvable (apply pi M)’, which is not provable outside
          the proof of this lemma.

   NOTE7: The core textbook proof steps of this lemma is actually in the proof of
         [subterm_subst_cong], which has to have a ‘tpm_rel’ in the conclusion.
          But the conclusion of the present lemma may still be ‘=’, because ‘tpm’
          may be represent by a ssub (fm), which can be combined with [P/y].

   NOTE8: Instead of ssub, the conclusion has used ‘ISUB’. This is because later,
          in [Boehm_out_lemma], we need to concatenate two ISUBs into a single one,
          but there's no clear relationship on their keys. ISUB is straightforward
          for this purposes.
 *)
Theorem Boehm_transform_exists_lemma :
    !X M p. FINITE X /\
            p <> [] /\ p IN ltree_paths (BTe X M) /\ subterm X M p <> NONE ==>
           ?pi. Boehm_transform pi /\
                solvable (apply pi M) /\ is_ready (apply pi M) /\
               ?Z v N. Z = X UNION FV M /\ closed N /\
                       subterm Z (apply pi M) p <> NONE /\
                       tpm_rel (subterm' Z (apply pi M) p) ([N/v] (subterm' Z M p))
Proof
    rpt STRIP_TAC
 >> ‘(!q. q <<= p ==> subterm X M q <> NONE) /\
      !q. q <<= FRONT p ==> solvable (subterm' X M q)’
         by METIS_TAC [subterm_solvable_lemma]
 >> Know ‘solvable M’
 >- (POP_ASSUM (MP_TAC o Q.SPEC ‘[]’) >> rw [])
 >> DISCH_TAC
 (* M0 is now meaningful since M is solvable *)
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> ‘hnf M0’ by PROVE_TAC [hnf_principle_hnf, solvable_iff_has_hnf]
 >> qabbrev_tac ‘n = LAMl_size M0’
 (* NOTE: here the excluded list must contain ‘FV M’. Just ‘FV M0’ doesn't
          work later, when calling the important [principle_hnf_denude_thm].
          This is conflicting with BT_generator_def and subterm_def.
  *)
 >> qabbrev_tac ‘vs = NEWS n (X UNION FV M)’
 >> Know ‘ALL_DISTINCT vs /\ DISJOINT (set vs) (X UNION FV M) /\ LENGTH vs = n’
 >- (rw [Abbr ‘vs’, NEWS_def])
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [DISJOINT_UNION']))
 (* applying the shared hnf_tac to decompose M0 *)
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR (TAKE n vs))’
 >> Know ‘?y args. M0 = LAMl (TAKE n vs) (VAR y @* args)’
 >- (qunabbrev_tac ‘n’ >> irule (iffLR hnf_cases_shared) >> rw [] \\
     MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘FV M’ >> art [] \\
     qunabbrev_tac ‘M0’ >> MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> STRIP_TAC
 (* eliminate ‘TAKE n vs’ *)
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (REV_FULL_SIMP_TAC std_ss o wrap)
 >> Know ‘M1 = VAR y @* args’
 >- (qunabbrev_tac ‘M1’ >> POP_ORW \\
     MATCH_MP_TAC principle_hnf_beta_reduce >> rw [hnf_appstar])
 >> DISCH_TAC
 >> qabbrev_tac ‘m = LENGTH args’
 (* using ‘subterm_width’ and applying subterm_width_thm *)
 >> qabbrev_tac ‘d = subterm_width M p’
 >> Know ‘m <= d’
 >- (MP_TAC (Q.SPECL [‘X’, ‘M’, ‘p’, ‘[]’] subterm_width_thm) \\
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
 >- (‘hnf M1’ by rw [hnf_appstar] \\
     ‘solvable M1’ by rw [solvable_iff_has_hnf, hnf_has_hnf] \\
     Suff ‘M0 @* MAP VAR vs == M1’ >- PROVE_TAC [lameq_solvable_cong] \\
     rw [])
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
 >> qabbrev_tac ‘l = NEWS (d - m + 1) Z’
 >> Know ‘ALL_DISTINCT l /\ DISJOINT (set l) Z /\ LENGTH l = d - m + 1’
 >- (rw [Abbr ‘l’, NEWS_def])
 >> STRIP_TAC
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
 >- (simp [Abbr ‘p3’, Abbr ‘P’, rightctxt_thm, MAP_SNOC, Boehm_apply_MAP_rightctxt'] \\
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
 >- (Q.PAT_X_ASSUM ‘apply (p3 ++ p2 ++ p1) M == _’ MP_TAC \\
     simp [Boehm_apply_APPEND] \\
     Q.PAT_X_ASSUM ‘Boehm_transform (p3 ++ p2 ++ p1)’ K_TAC \\
     Q.PAT_X_ASSUM ‘Boehm_transform p1’ K_TAC \\
     Q.PAT_X_ASSUM ‘apply p1 M0 == M1’ K_TAC \\
     simp [Abbr ‘p1’, Boehm_apply_MAP_rightctxt'] \\
     Q.PAT_X_ASSUM ‘Boehm_transform p2’ K_TAC \\
     Q.PAT_X_ASSUM ‘apply p2 M1 = P @* args'’ K_TAC \\
     simp [Abbr ‘p2’] \\
     Q.PAT_X_ASSUM ‘Boehm_transform p3’ K_TAC \\
     Q.PAT_X_ASSUM ‘apply p3 (P @* args') == _’ K_TAC \\
     simp [Abbr ‘p3’, Boehm_apply_MAP_rightctxt'] \\
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
         >- (MATCH_MP_TAC lemma14b >> fs [MEM_SNOC]) >> Rewr' \\
         simp [Abbr ‘P’, GSYM appstar_APPEND] \\
         MATCH_MP_TAC principle_hnf_permutator >> rw []) >> Rewr' \\
  (* applying principle_hnf_substitutive *)
     MATCH_MP_TAC principle_hnf_substitutive \\
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
         MATCH_MP_TAC hnf_has_hnf \\
         rw [hnf_appstar]) \\
     CONJ_TAC (* has_hnf #2 *)
     >- (REWRITE_TAC [GSYM solvable_iff_has_hnf] \\
         Suff ‘solvable (VAR b @* args' @* MAP VAR as)’
         >- PROVE_TAC [lameq_solvable_cong] \\
         REWRITE_TAC [solvable_iff_has_hnf] \\
         MATCH_MP_TAC hnf_has_hnf \\
         rw [hnf_appstar]) \\
     CONJ_TAC (* has_hnf # 3 *)
     >- (simp [appstar_SUB, MAP_SNOC] \\
         Know ‘MAP [P/y] (MAP VAR as) = MAP VAR as’
         >- (Q.PAT_X_ASSUM ‘LENGTH as = _’ K_TAC \\
             rw [LIST_EQ_REWRITE, EL_MAP] \\
             MATCH_MP_TAC lemma14b >> rw [] \\
             Q.PAT_X_ASSUM ‘~MEM y (SNOC b as)’ MP_TAC \\
             rw [MEM_EL] >> PROVE_TAC []) >> Rewr' \\
         Know ‘[P/y] (VAR b) = VAR b’
         >- (MATCH_MP_TAC lemma14b >> fs [MEM_SNOC]) >> Rewr' \\
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
 (* extra subgoal: solvable (apply (p3 ++ p2 ++ p1) M) *)
 >> CONJ_ASM1_TAC
 >- (Suff ‘solvable (VAR b @* args' @* MAP VAR as)’
     >- PROVE_TAC [lameq_solvable_cong] \\
     REWRITE_TAC [solvable_iff_has_hnf] \\
     MATCH_MP_TAC hnf_has_hnf >> rw [hnf_appstar])
 (* applying is_ready_alt *)
 >> CONJ_TAC
 >- (simp [is_ready_alt] \\
     qexistsl_tac [‘b’, ‘args' ++ MAP VAR as’] \\
     CONJ_TAC >- (MP_TAC (Q.SPEC ‘VAR b @* args' @* MAP VAR as’
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
 (* NOTE: for rewriting M to M0 in the goal, Z can be anything. *)
 >> Q.ABBREV_TAC ‘Y = X UNION FV M’
 >> ‘FINITE Y’ by rw [Abbr ‘Y’]
 (* RHS rewriting from M to M0 *)
 >> Know ‘subterm Y M0 p = subterm Y M p’
 >- (qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC subterm_of_principle_hnf >> art [])
 >> DISCH_THEN (ONCE_REWRITE_TAC o wrap o SYM)
 (* LHS rewriting from M to M0 *)
 >> Know ‘subterm Y (apply (p3 ++ p2 ++ p1) M) p =
          subterm Y (VAR b @* args' @* MAP VAR as) p’
 >- (Q.PAT_X_ASSUM ‘_ = VAR b @* args' @* MAP VAR as’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     qabbrev_tac ‘t = apply (p3 ++ p2 ++ p1) M’ \\
     Suff ‘subterm Y (principle_hnf t) p = subterm Y t p’ >- rw [] \\
     MATCH_MP_TAC subterm_of_principle_hnf >> art [])
 >> Rewr'
 (* stage cleanups *)
 >> Q.PAT_X_ASSUM ‘solvable (apply (p3 ++ p2 ++ p1) M)’          K_TAC
 >> Q.PAT_X_ASSUM ‘principle_hnf (apply (p3 ++ p2 ++ p1) M) = _’ K_TAC
 >> Q.PAT_X_ASSUM ‘apply (p3 ++ p2 ++ p1) M == _’                K_TAC
 >> Q.PAT_X_ASSUM ‘Boehm_transform (p3 ++ p2 ++ p1)’             K_TAC
 (* stage work, now ‘M’ is eliminated from both sides! *)
 >> Cases_on ‘p’ >- FULL_SIMP_TAC std_ss []
 >> Know ‘h < m’
 >- (Q.PAT_X_ASSUM ‘subterm X M (h::t) <> NONE’ MP_TAC \\
     RW_TAC std_ss [subterm_of_solvables] >> fs [])
 >> DISCH_TAC
 (* applying subterm_of_absfree_hnf *)
 >> MP_TAC (Q.SPECL [‘Y’, ‘VAR b @* args' @* MAP VAR as’, ‘h’, ‘t’]
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
 >> Know ‘subterm Y (LAMl vs (VAR y @* args)) (h::t) =
          subterm Z (EL h args) t’
 >- (MP_TAC (Q.SPECL [‘Y’, ‘LAMl vs (VAR y @* args)’, ‘h’, ‘t’] subterm_of_hnf) \\
     simp [hnf_LAMl, hnf_appstar] \\
     DISCH_THEN K_TAC (* already used *) \\
     Q.PAT_X_ASSUM ‘M0 = LAMl vs (VAR y @* args)’ (REWRITE_TAC o wrap o SYM) \\
     Know ‘Y UNION FV M0 = Y’
     >- (Know ‘FV M0 SUBSET FV M’ >- rw [Abbr ‘M0’, principle_hnf_FV_SUBSET'] \\
         qunabbrev_tac ‘Y’ >> SET_TAC []) >> Rewr' \\
     simp [hnf_children_hnf])
 >> Rewr'
 (* Now: subterm' Z (EL h args') t == [P/y] (subterm' Z (EL h args) t)

    First of all, those assumptions about p1,p2,p3 are no more needed.
  *)
 >> Q.PAT_X_ASSUM ‘Boehm_transform p1’         K_TAC
 >> Q.PAT_X_ASSUM ‘apply p1 M0 == M1’          K_TAC
 >> qunabbrev_tac ‘p1’
 >> Q.PAT_X_ASSUM ‘Boehm_transform p2’         K_TAC
 >> Q.PAT_X_ASSUM ‘apply p2 M1 = P @* args'’   K_TAC
 >> qunabbrev_tac ‘p2’
 >> Q.PAT_X_ASSUM ‘Boehm_transform p3’         K_TAC
 >> Q.PAT_X_ASSUM ‘apply p3 (P @* args') == _’ K_TAC
 >> qunabbrev_tac ‘p3’
 >> Q.PAT_X_ASSUM ‘h::t <> []’                 K_TAC (* too obvious *)
 >> qabbrev_tac ‘N  = EL h args’
 >> qabbrev_tac ‘N' = EL h args'’
 (* eliminating N' *)
 >> ‘N' = [P/y] N’ by (simp [EL_MAP, Abbr ‘m’, Abbr ‘N’, Abbr ‘N'’, Abbr ‘args'’])
 >> POP_ORW
 >> qunabbrev_tac ‘N'’
 (* cleanup args' *)
 >> Q.PAT_X_ASSUM ‘!i. i < m ==> FV (EL i args') SUBSET FV (EL i args)’ K_TAC
 >> Q.PAT_X_ASSUM ‘LENGTH args' = m’ K_TAC
 >> qunabbrev_tac ‘args'’
 (* cleanup l, as and b *)
 >> Q.PAT_X_ASSUM ‘ALL_DISTINCT l’             K_TAC
 >> NTAC 2 (Q.PAT_X_ASSUM ‘DISJOINT (set l) _’ K_TAC)
 >> Q.PAT_X_ASSUM ‘LENGTH l = q - m + 1’       K_TAC
 >> Q.PAT_X_ASSUM ‘l <> []’                    K_TAC
 >> Q.PAT_X_ASSUM ‘l = SNOC b as’              K_TAC
 >> Q.PAT_X_ASSUM ‘~MEM y l’                   K_TAC
 >> Q.PAT_X_ASSUM ‘LENGTH as = q - m’          K_TAC
 >> qunabbrevl_tac [‘l’, ‘as’, ‘b’]
 (* NOTE: this is a key requirements for applying subterm_subst_cong *)
 >> Know ‘y IN Z’
 >- (qunabbrevl_tac [‘Y’, ‘Z’] \\
     Suff ‘y IN FV M UNION set vs’ >- SET_TAC [] \\
    ‘y IN FV M1’ by rw [FV_appstar] \\
     Suff ‘FV M1 SUBSET FV M UNION set vs’ >- rw [SUBSET_DEF] \\
     qunabbrev_tac ‘M1’ \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘FV (M0 @* MAP VAR vs)’ \\
     CONJ_TAC >- (MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art []) \\
     Q.PAT_X_ASSUM ‘M0 = LAMl vs (VAR y @* args)’ K_TAC \\
     simp [FV_appstar] \\
     Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principle_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 (* stage work, there's the textbook choice *)
 >> qexistsl_tac [‘y’, ‘P’] >> art []
 >> REWRITE_TAC [GSYM SUB_ISUB_SINGLETON]
 (* preparing for subterm_subst_cong *)
 >> Suff ‘subterm Z ([P/y] N) t <> NONE /\
          tpm_rel (subterm' Z ([P/y] N) t) ([P/y] (subterm' Z N t))’
 >- (STRIP_TAC \\
     CONJ_ASM1_TAC >- PROVE_TAC [subterm_tpm_cong] \\
  (* applying tpm_rel_cong and subterm_tpm_cong *)
     Suff ‘tpm_rel (subterm' Y ([P/y] N) t) ([P/y] (subterm' Z N t)) <=>
           tpm_rel (subterm' Z ([P/y] N) t) ([P/y] (subterm' Z N t))’ >- rw [] \\
     MATCH_MP_TAC tpm_rel_cong >> simp [] \\
     PROVE_TAC [subterm_tpm_cong])
 (* applying subterm_subst_cong *)
 >> MATCH_MP_TAC subterm_subst_cong
 >> Q.EXISTS_TAC ‘d’
 >> simp [Abbr ‘P’]
 (* NOTE: Here, we need the following new lemma:

   |- !X Y. ltree_paths (BTe X M) = ltree_paths (BTe Y M)

   to convert ‘subterm X M (h::t) <> NONE’ to ‘subterm Z M (h::t) <> NONE’.
  *)
 >> CONJ_ASM1_TAC (* t IN ltree_paths ... *)
 >- (Q.PAT_X_ASSUM ‘h::t IN ltree_paths (BTe X M)’ MP_TAC \\
    ‘ltree_paths (BTe X M) = ltree_paths (BTe Y M)’
      by PROVE_TAC [BT_ltree_paths_unique] >> POP_ORW \\
     simp [ltree_paths_def, ltree_lookup] \\
     Know ‘BTe Y M = ltree_unfold BT_generator (Y,M)’ >- rw [BT_def] \\
     Q.PAT_X_ASSUM ‘M0 = _’ K_TAC \\
     simp [Once ltree_unfold, BT_generator_def, LNTH_fromList] \\
     Know ‘Y UNION FV M0 = Y’
     >- (Know ‘FV M0 SUBSET FV M’ >- rw [Abbr ‘M0’, principle_hnf_FV_SUBSET'] \\
         qunabbrev_tac ‘Y’ >> SET_TAC []) >> Rewr' \\
     simp [hnf_children_hnf] \\
     simp [GSYM BT_def, EL_MAP, hnf_children_hnf])
 (* stage work *)
 >> CONJ_ASM1_TAC (* subterm Z N t <> NONE *)
 >- (Q.PAT_X_ASSUM ‘subterm X M (h::t) <> NONE’ MP_TAC \\
    ‘subterm X M (h::t) <> NONE <=>
     subterm Y M (h::t) <> NONE’ by PROVE_TAC [subterm_tpm_cong] >> POP_ORW \\
     Q.PAT_X_ASSUM ‘M0 = _’ K_TAC \\
     simp [subterm_of_solvables] \\
     Know ‘Y UNION FV M0 = Y’
     >- (Know ‘FV M0 SUBSET FV M’ >- rw [Abbr ‘M0’, principle_hnf_FV_SUBSET'] \\
         qunabbrev_tac ‘Y’ >> SET_TAC []) >> Rewr' \\
     simp [hnf_children_hnf])
 (* final goal: subterm_width (EL h args) t <= d *)
 >> qunabbrev_tac ‘d’
 (* applying subterm_width_alt *)
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::t’] subterm_width_alt)
 >> simp [] >> DISCH_THEN K_TAC
 >> qabbrev_tac ‘p = h::t’
 >> Know ‘IMAGE (hnf_children_size o principle_hnf)
                {subterm' X M p' | p' <<= FRONT p} =
          {hnf_children_size (principle_hnf (subterm' X M p')) | p' <<= FRONT p}’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       rename1 ‘q <<= FRONT p’ \\
       Q.EXISTS_TAC ‘q’ >> rw [],
       (* goal 2 (of 2) *)
       rename1 ‘q <<= FRONT p’ \\
       Q.EXISTS_TAC ‘subterm' X M q’ >> art [] \\
       Q.EXISTS_TAC ‘q’ >> art [] ])
 >> Rewr'
 >> qunabbrev_tac ‘p’
 >> Cases_on ‘t = []’ >- rw []
 (* applying subterm_width_alt again *)
 >> MP_TAC (Q.SPECL [‘Z’, ‘N’, ‘t’] subterm_width_alt)
 >> simp [] >> DISCH_THEN K_TAC
 (* applying SUBSET_MAX_SET *)
 >> MATCH_MP_TAC SUBSET_MAX_SET
 >> CONJ_TAC
 >- (MATCH_MP_TAC IMAGE_FINITE \\
   ‘{subterm' Z N p' | p' <<= FRONT t} =
    IMAGE (subterm' Z N) {p' | p' <<= FRONT t}’
      by rw [Once EXTENSION] >> POP_ORW \\
    MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 >> CONJ_TAC
 >- (‘{hnf_children_size (principle_hnf (subterm' X M p')) |
       p' <<= FRONT (h::t)} =
      IMAGE (\p'. hnf_children_size (principle_hnf (subterm' X M p')))
            {p' | p' <<= FRONT (h::t)}’
        by rw [Once EXTENSION] >> POP_ORW \\
     MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_prefix])
 >> ‘hnf_children_size M0 = m’ by rw [Abbr ‘m’]
 >> Q.PAT_X_ASSUM ‘M0 = _’ K_TAC
 >> rw [SUBSET_DEF] (* this asserts ‘p' <<= FRONT t’ *)
 >> Q.EXISTS_TAC ‘h::p'’
 >> ‘FRONT (h::t) <> []’ by rw []
 >> Know ‘h::p' <<= FRONT (h::t)’
 >- (simp [] >> Cases_on ‘t’ >> fs [])
 >> Rewr
 >> Suff ‘hnf_children_size (principle_hnf (subterm' X M (h::p'))) =
          hnf_children_size (principle_hnf (subterm' Y M (h::p')))’
 >- (Rewr' \\
     CONV_TAC (UNBETA_CONV “subterm Y M (h::p')”) \\
     qmatch_abbrev_tac ‘f _’ \\
     RW_TAC std_ss [subterm_of_solvables] \\
     simp [Abbr ‘f’, hnf_children_hnf] \\
     Know ‘Y UNION FV M0 = Y’
     >- (Know ‘FV M0 SUBSET FV M’ >- rw [Abbr ‘M0’, principle_hnf_FV_SUBSET'] \\
         qunabbrev_tac ‘Y’ >> SET_TAC []) >> Rewr' \\
     simp [hnf_children_hnf])
 (* applying subterm_hnf_children_size_cong *)
 >> MATCH_MP_TAC subterm_hnf_children_size_cong >> art []
 (* subgoals: subterm X M (h::p') <> NONE /\ solvable (subterm' X M (h::p')) *)
 >> reverse CONJ_TAC
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw [] \\
     Cases_on ‘t’ >> fs [])
 (* final goal: subterm X M (h::p') <> NONE *)
 >> FIRST_X_ASSUM MATCH_MP_TAC >> rw []
 >> MATCH_MP_TAC IS_PREFIX_TRANS
 >> Q.EXISTS_TAC ‘FRONT t’ >> art []
 >> MATCH_MP_TAC IS_PREFIX_BUTLAST' >> art []
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
             MATCH_MP_TAC (GSYM SNOC_LAST_FRONT) >> rw [Abbr ‘l’]) \\
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
 >> ‘hnf M0 /\ hnf N0’ by PROVE_TAC [hnf_principle_hnf, solvable_iff_has_hnf]
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

     NOTE: This Z = [z1;z2] contains two fresh variables fixing the textbook proof,
           where [1, p.254] the iterated substition "[LAMl as P/y1] [LAMl as' Q/y2]"
           must be fixed to act as a simultaneous substitition:

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
       CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> POP_ASSUM (REWRITE_TAC o wrap) \\
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
       CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> POP_ASSUM (REWRITE_TAC o wrap) \\
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
           MATCH_MP_TAC lemma14b >> rw [FV_SUB] \\
           CCONTR_TAC >> ‘MEM y2 Z’ by METIS_TAC [] \\
           Q.PAT_X_ASSUM ‘DISJOINT (set Z) (FV P UNION FV Q)’ MP_TAC \\
           rw [DISJOINT_ALT'] >> METIS_TAC []) >> Rewr' \\
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
       CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> POP_ASSUM (REWRITE_TAC o wrap) \\
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
       CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> POP_ASSUM (REWRITE_TAC o wrap) \\
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
 (* applying Boehm_apply_unsolvable *)
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC Boehm_apply_unsolvable >> art [])
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
val _ = html_theory "boehm";

(* References:

   [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
       College Publications, London (1984).
 *)
