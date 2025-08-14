(* ========================================================================== *)
(* FILE    : boehmScript.sml (aka chap10Script.sml)                           *)
(* TITLE   : (Effective) Böhm Trees (Barendregt 1984 [1], Chapter 10)         *)
(*                                                                            *)
(* AUTHORS : 2023-2024 The Australian National University (Chun Tian)         *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

(* core theories *)
open optionTheory arithmeticTheory pred_setTheory listTheory rich_listTheory
     llistTheory relationTheory ltreeTheory pathTheory posetTheory hurdUtils
     pairTheory finite_mapTheory topologyTheory combinTheory tautLib listLib
     string_numTheory numLib BasicProvers;

(* local theories *)
open basic_swapTheory nomsetTheory termTheory appFOLDLTheory NEWLib chap2Theory
     chap3Theory reductionEval head_reductionTheory head_reductionLib
     standardisationTheory solvableTheory horeductionTheory takahashiS3Theory;

(* enable basic monad support *)
open monadsyntax;
val _ = enable_monadsyntax ();
val _ = enable_monad "option";

val _ = new_theory "boehm";

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

(* Disable some conflicting overloads from labelledTermsTheory *)
Overload FV  = “supp term_pmact”
Overload VAR = “term$VAR”

(*---------------------------------------------------------------------------*
 *  Boehm Trees (and subterms) - name after Corrado Böhm [2]                 *
 *---------------------------------------------------------------------------*)

(* The type of Boehm trees:

   NOTE: For each ltree node, ‘NONE’ represents {\bot} for unsolvable terms, and
  ‘SOME (vs,y)’ represents ‘LAMl vs (VAR y)’. There are at least two advantages:

   1. ‘set vs’ is the set of binding variables at that ltree node.
   2. ‘LAMl vs (VAR y)’ can easily "expand" (w.r.t. eta reduction) into terms
      such as “LAMl (vs ++ [z0;z1]) t” without changing the head variable.
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
         let M0 = principal_hnf M;
              n = LAMl_size M0;
             vs = RNEWS r n X;
             M1 = principal_hnf (M0 @* MAP VAR vs);
             Ms = hnf_children M1;
              y = hnf_headvar M1;
              l = MAP (\e. (e,SUC r)) Ms;
         in
            (SOME (vs,y),fromList l)
      else
            (NONE, LNIL)
End

(* M0 is not needed if M is already an hnf *)
Theorem BT_generator_of_hnf :
    !X M r. FINITE X /\ hnf M ==>
            BT_generator X (M,r) =
           (let
             n = LAMl_size M;
             vs = RNEWS r n X;
             M1 = principal_hnf (M @* MAP VAR vs);
             Ms = hnf_children M1;
             y = hnf_headvar M1;
             l = MAP (\e. (e,SUC r)) Ms
           in
             (SOME (vs,y),fromList l))
Proof
    rpt STRIP_TAC
 >> ‘solvable M’ by PROVE_TAC [hnf_solvable]
 >> RW_TAC std_ss [BT_generator_def]
 >> ‘M0 = M’ by rw [Abbr ‘M0’, principal_hnf_reduce]
 >> POP_ASSUM (fs o wrap)
 >> Q.PAT_X_ASSUM ‘n' = n’   (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs' = vs’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1' = M1’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms' = Ms’ (fs o wrap o SYM)
QED

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
         let M0 = principal_hnf M;
              n = LAMl_size M0;
             vs = RNEWS r n X;
             M1 = principal_hnf (M0 @* MAP VAR vs);
             Ms = hnf_children M1;
              m = LENGTH Ms
         in
             if h < m then subterm X (EL h Ms) p (SUC r)
             else NONE
      else
         NONE
End

(* The use of ‘subterm' X M p r’ assumes that ‘subterm X M p r <> NONE’ *)
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
           solvable M /\ M0 = principal_hnf M /\ vs = RNEWS r n X
       ==> DISJOINT (set vs) (FV M0)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC DISJOINT_SUBSET
 >> Q.EXISTS_TAC ‘FV M’
 >> reverse CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘M0 = _’ (REWRITE_TAC o wrap) \\
     MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art [])
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
           M0 = principal_hnf M /\
            n = LAMl_size M0 /\
           vs = RNEWS r n' X /\ n <= n'
       ==> solvable (M0 @* MAP VAR vs)
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> ‘hnf M0’ by PROVE_TAC [hnf_principal_hnf']
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n' :num”)) ‘X’
 >> Know ‘?y args. M0 = LAMl (TAKE n vs) (VAR y @* args)’
 >- (rw [Abbr ‘n’] >> irule (iffLR hnf_cases_shared) >> rw [] \\
     MATCH_MP_TAC subterm_disjoint_lemma' \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘LENGTH vs’] >> rw [])
 >> STRIP_TAC
 >> qabbrev_tac ‘xs = TAKE n vs’
 >> qabbrev_tac ‘m = hnf_children_size M0’
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
 >> Know ‘M1 = VAR y @* args @* DROP n (MAP VAR vs)’
 >- (simp [Abbr ‘M1’] \\
     qabbrev_tac ‘t = VAR y @* args’ \\
     simp [GSYM MAP_DROP] \\
     Know ‘MAP VAR vs = MAP VAR xs ++ MAP VAR (DROP n vs)’
     >- (REWRITE_TAC [GSYM MAP_APPEND] >> AP_TERM_TAC \\
         rw [Abbr ‘xs’, TAKE_DROP]) >> Rewr' \\
     REWRITE_TAC [appstar_APPEND] \\
     qabbrev_tac ‘l = MAP VAR (DROP n vs)’ \\
     MATCH_MP_TAC principal_hnf_beta_reduce_ext \\
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
 >> MATCH_MP_TAC hnf_solvable
 >> simp [Abbr ‘t’, GSYM appstar_APPEND, hnf_appstar]
QED

Theorem solvable_appstar' :
    !X M r M0 n vs.
           FINITE X /\ FV M SUBSET X UNION RANK r /\
           solvable M /\
           M0 = principal_hnf M /\
            n = LAMl_size M0 /\
           vs = RNEWS r n X
       ==> solvable (M0 @* MAP VAR vs)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC solvable_appstar
 >> qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘n’] >> simp []
QED

(* Essentially, ‘hnf_children_size (principal_hnf M)’ is irrelevant with
   the excluding list. This lemma shows the equivalence in defining ‘m’.
 *)
Theorem hnf_children_size_alt :
    !X M r M0 n vs M1 Ms.
         FINITE X /\ FV M SUBSET X UNION RANK r /\ solvable M /\
         M0 = principal_hnf M /\
          n = LAMl_size M0 /\
         vs = RNEWS r n X /\
         M1 = principal_hnf (M0 @* MAP VAR vs) /\
         Ms = hnf_children M1
     ==> hnf_children_size M0 = LENGTH Ms
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
QED

Theorem subterm_of_solvables :
    !X M h p r. solvable M ==>
       subterm X M (h::p) r =
         let M0 = principal_hnf M;
              n = LAMl_size M0;
             vs = RNEWS r n X;
             M1 = principal_hnf (M0 @* MAP VAR vs);
             Ms = hnf_children M1;
              m = LENGTH Ms
         in
            if h < m then subterm X (EL h Ms) p (SUC r) else NONE
Proof
    rw [subterm_def]
QED

Theorem subterm_of_unsolvables :
    !X M p r. unsolvable M /\ p <> [] ==> subterm X M p r = NONE
Proof
    rpt STRIP_TAC
 >> Cases_on ‘p’ >> fs []
 >> rw [subterm_def]
QED

(* NOTE: With [hnf_children_size_alt] now we are ready to prove this alternative
         definition of ‘subterm’.
 *)
Theorem subterm_alt :
    !X M h p r. FINITE X /\ FV M SUBSET X UNION RANK r ==>
       subterm X M (h::p) r =
       if solvable M then
         let M0 = principal_hnf M;
              n = LAMl_size M0;
              m = hnf_children_size M0;
             vs = RNEWS r n X;
             M1 = principal_hnf (M0 @* MAP VAR vs);
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
val _ = TeX_notation {hol = "bot", TeX = ("\\HOLTokenBottom}", 1)};
val _ = TeX_notation {hol = UTF8.chr 0x22A5, TeX = ("\\HOLTokenBottom", 1) };

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

Theorem BT_of_principal_hnf :
    !X M r. solvable M ==> BT' X (principal_hnf M) r = BT' X M r
Proof
    reverse (RW_TAC std_ss [BT_def, BT_generator_def, ltree_unfold])
 >- (Q.PAT_X_ASSUM ‘unsolvable M0’ MP_TAC >> simp [] \\
     MATCH_MP_TAC hnf_solvable \\
     rw [Abbr ‘M0’, hnf_principal_hnf'])
 >> ‘M0' = M0’ by rw [Abbr ‘M0'’, Abbr ‘M0’, principal_hnf_stable']
 >> qunabbrev_tac ‘M0'’
 >> POP_ASSUM (rfs o wrap)
 >> ‘principal_hnf M0 = M0’ by rw [Abbr ‘M0’, principal_hnf_stable']
 >> POP_ASSUM (rfs o wrap)
QED

(* This proof without other antecedents is based on principal_hnf_hreduce *)
Theorem hreduce_BT_cong :
    !X M N r. M -h->* N ==> BT' X M r = BT' X N r
Proof
    rpt STRIP_TAC
 >> ‘M == N’ by PROVE_TAC [hreduces_lameq]
 >> reverse (Cases_on ‘solvable M’)
 >- (‘unsolvable N’ by PROVE_TAC [lameq_solvable_cong] \\
     rw [BT_of_unsolvables])
 >> ‘solvable N’ by PROVE_TAC [lameq_solvable_cong]
 >> ‘principal_hnf M = principal_hnf N’ by PROVE_TAC [principal_hnf_hreduce]
 >> Q_TAC (UNBETA_TAC [BT_def, BT_generator_def, Once ltree_unfold]) ‘BT' X M r’
 >> Q_TAC (UNBETA_TAC [BT_def, BT_generator_def, Once ltree_unfold]) ‘BT' X N r’
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
                    “y :string”, “args :term list”)) ‘M1’
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
     MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art [])
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
           M0 = principal_hnf M /\
            n = LAMl_size M0 /\
            m = hnf_children_size M0 /\
           vs = RNEWS r n' X /\ n <= n' /\
           M1 = principal_hnf (M0 @* MAP VAR vs) /\
           Ms = hnf_children M1 /\ h < m
       ==> FV (EL h Ms) SUBSET X UNION RANK (SUC r)
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> ‘hnf M0’ by PROVE_TAC [hnf_principal_hnf']
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n' :num”)) ‘X’
 >> Know ‘?y args. M0 = LAMl (TAKE n vs) (VAR y @* args)’
 >- (rw [Abbr ‘n’] >> irule (iffLR hnf_cases_shared) >> rw [] \\
     MATCH_MP_TAC subterm_disjoint_lemma' \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘LENGTH vs’] >> rw [])
 >> STRIP_TAC
 >> qabbrev_tac ‘xs = TAKE n vs’
 >> qabbrev_tac ‘m = hnf_children_size M0’
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
 >> Know ‘M1 = VAR y @* args @* DROP n (MAP VAR vs)’
 >- (simp [Abbr ‘M1’] \\
     qabbrev_tac ‘t = VAR y @* args’ \\
     simp [GSYM MAP_DROP] \\
     Know ‘MAP VAR vs = MAP VAR xs ++ MAP VAR (DROP n vs)’
     >- (REWRITE_TAC [GSYM MAP_APPEND] >> AP_TERM_TAC \\
         rw [Abbr ‘xs’, TAKE_DROP]) >> Rewr' \\
     REWRITE_TAC [appstar_APPEND] \\
     qabbrev_tac ‘l = MAP VAR (DROP n vs)’ \\
     MATCH_MP_TAC principal_hnf_beta_reduce_ext \\
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
     MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art [])
 >> Q.PAT_X_ASSUM ‘M0 = LAMl xs (VAR y @* args)’ K_TAC
 >> rw [SUBSET_DEF, FV_appstar]
 >> Know ‘x IN FV M UNION set vs’
 >- (POP_ASSUM MP_TAC \\
     Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art [])
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
           M0 = principal_hnf M /\
            n = LAMl_size M0 /\
            m = hnf_children_size M0 /\
           vs = RNEWS r n X /\
           M1 = principal_hnf (M0 @* MAP VAR vs) /\
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
           M0 = principal_hnf M /\
            n = LAMl_size M0 /\
           vs = RNEWS r n X /\
           M1 = principal_hnf (M0 @* MAP VAR vs) /\
           Ms = hnf_children M1 /\
            m = LENGTH Ms /\
            h < m
       ==> FV (EL h Ms) SUBSET FV M UNION set vs
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
 >> ‘DISJOINT (set vs) (FV M0)’ by PROVE_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> rfs []
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> qunabbrev_tac ‘M1’
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
 >> ‘hnf M1’ by rw [hnf_appstar]
 >> Q.PAT_X_ASSUM ‘M0 = _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = _’ (ASSUME_TAC o SYM)
 >> ‘hnf_children M1 = args’ by rw [hnf_children_hnf]
 >> POP_ASSUM (rfs o wrap)
 >> Know ‘FV (principal_hnf (M0 @* MAP VAR vs)) SUBSET FV (M0 @* MAP VAR vs)’
 >- (MATCH_MP_TAC principal_hnf_FV_SUBSET' \\
    ‘solvable M1’ by rw [hnf_solvable] \\
     Suff ‘M0 @* MAP VAR vs == M1’ >- PROVE_TAC [lameq_solvable_cong] \\
     rw [])
 >> simp []
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
 >> DISCH_TAC
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M0 UNION set vs’
 >> reverse CONJ_TAC
 >- (Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art [])
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
           M0 = principal_hnf M /\
            n = LAMl_size M0 /\
           vs = RNEWS r n X /\
           M1 = principal_hnf (M0 @* MAP VAR vs)
       ==> hnf_headvar M1 IN X UNION RANK (SUC r)
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> qabbrev_tac ‘n  = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
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
                 MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art [])
 >> REWRITE_TAC [FV_appstar_MAP_VAR]
 >> Q.PAT_X_ASSUM ‘M0 = _’ K_TAC
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘FV M UNION set vs’
 >> CONJ_TAC >- (Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
                 qunabbrev_tac ‘M0’ \\
                 MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art [])
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
           M0 = principal_hnf M /\
            n = LAMl_size M0 /\
           vs = RNEWS r n' X /\ n <= n' /\
           M1 = principal_hnf (M0 @* MAP VAR vs)
       ==> hnf_headvar M1 IN FV M UNION set (TAKE n vs)
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n' :num”)) ‘X’
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
 >> ‘DISJOINT (set vs) (FV M0)’ by PROVE_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> rfs []
 >> qabbrev_tac ‘xs = TAKE n vs’
 >> Q.PAT_X_ASSUM ‘M1 = _’ K_TAC
 >> Q.PAT_X_ASSUM ‘M0 = _’ (ASSUME_TAC o SYM) >> simp []
 (* redefine M1 *)
 >> qunabbrev_tac ‘M1’
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
 (* applying principal_hnf_beta_reduce_ext *)
 >> Know ‘M1 = VAR y @* args @* DROP n (MAP VAR vs)’
 >- (qunabbrev_tac ‘M1’ \\
     qabbrev_tac ‘t = VAR y @* args’ \\
     rw [GSYM MAP_DROP] \\
     Know ‘MAP VAR vs = MAP VAR xs ++ MAP VAR (DROP n vs)’
     >- (REWRITE_TAC [GSYM MAP_APPEND] >> AP_TERM_TAC \\
         rw [Abbr ‘xs’, TAKE_DROP]) >> Rewr' \\
     REWRITE_TAC [appstar_APPEND] \\
     qabbrev_tac ‘l = MAP VAR (DROP n vs)’ \\
     MATCH_MP_TAC principal_hnf_beta_reduce_ext \\
     rw [Abbr ‘t’, hnf_appstar])
 >> DISCH_TAC
 >> ‘hnf M1’ by rw [hnf_appstar]
 >> Q.PAT_X_ASSUM ‘M1 = _’ (ASSUME_TAC o SYM)
 >> Know ‘hnf_headvar M1 = y’
 >- (POP_ASSUM (REWRITE_TAC o wrap o SYM) \\
     simp [GSYM appstar_APPEND])
 >> Rewr'
 >> qabbrev_tac ‘M1' = principal_hnf (M0 @* MAP VAR xs)’
 >> Know ‘M1' = VAR y @* args’
 >- (qunabbrev_tac ‘M1'’ \\
     qabbrev_tac ‘t = VAR y @* args’ \\
     Q.PAT_X_ASSUM ‘_ = M0’ (REWRITE_TAC o wrap o SYM) \\
     MATCH_MP_TAC principal_hnf_beta_reduce \\
     rw [Abbr ‘t’, hnf_appstar])
 >> DISCH_THEN (ASSUME_TAC o SYM)
 >> Know ‘FV (principal_hnf (M0 @* MAP VAR xs)) SUBSET FV (M0 @* MAP VAR xs)’
 >- (MATCH_MP_TAC principal_hnf_FV_SUBSET' \\
    ‘solvable M1'’ by rw [hnf_solvable, hnf_appstar] \\
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
 >> MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []
QED

Theorem subterm_headvar_lemma' :
    !X M r M0 n vs M1.
           FINITE X /\ FV M SUBSET X UNION RANK r /\
           solvable M /\
           M0 = principal_hnf M /\
            n = LAMl_size M0 /\
           vs = RNEWS r n X /\
           M1 = principal_hnf (M0 @* MAP VAR vs)
       ==> hnf_headvar M1 IN FV M UNION set vs
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
 >> ‘vs = TAKE n vs’ by rw [] >> POP_ORW
 >> MATCH_MP_TAC subterm_headvar_lemma_alt
 >> qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’] >> simp []
QED

(* NOTE: This theorem indicates that ‘m = LENGTH Ms’ is more natural. *)
Theorem BT_ltree_el_NIL :
    !X M r. ltree_el (BT' X M r) [] =
          if solvable M then
             let
               M0 = principal_hnf M;
                n = LAMl_size M0;
               vs = RNEWS r n X;
               M1 = principal_hnf (M0 @* MAP VAR vs);
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
Theorem BT_ltree_el_NIL_alt :
    !X M r. FINITE X /\ FV M SUBSET X UNION RANK r ==>
          ltree_el (BT' X M r) [] =
          if solvable M then
             let
               M0 = principal_hnf M;
                n = LAMl_size M0;
                m = hnf_children_size M0;
               vs = RNEWS r n X;
               M1 = principal_hnf (M0 @* MAP VAR vs);
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
 *  Boehm trees of beta/eta equivalent terms
 *---------------------------------------------------------------------------*)

(* Proposition 10.1.6 [1, p.219]

   M -h->* M0
  /          \b*
 ==          +---[lameq_CR] y1 = y2, n1 = n2, m1 = m2
  \         /b*
   N -h->* Ns

   NOTE: ‘FV M SUBSET X UNION RANK r’ is not necessary for finishing this
   proof (because no induction is involved), only ‘FV M SUBSET X’ is enough.
   But later applications needs the ranked antecedents.
 *)
Theorem lameq_BT_cong :
    !X M N r. FINITE X /\
              FV M SUBSET X UNION RANK r /\
              FV N SUBSET X UNION RANK r /\
              M == N ==> BT' X M r = BT' X N r
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
     ‘\x y. ?P Q r. FV P SUBSET X UNION RANK r /\
                    FV Q SUBSET X UNION RANK r /\
                    P == Q /\ x = BT' X P r /\ y = BT' X Q r’
 >> BETA_TAC
 >> CONJ_TAC >- (qexistsl_tac [‘M’, ‘N’, ‘r’] >> simp [])
 (* stage work *)
 >> qx_genl_tac [‘a1’, ‘ts1’, ‘a2’, ‘ts2’] >> STRIP_TAC
 >> qabbrev_tac ‘P0 = principal_hnf P’
 >> qabbrev_tac ‘Q0 = principal_hnf Q’
 >> qabbrev_tac ‘n  = LAMl_size P0’
 >> qabbrev_tac ‘n' = LAMl_size Q0’
 >> qabbrev_tac ‘vs  = RNEWS r' n  X’
 >> qabbrev_tac ‘vs' = RNEWS r' n' X’
 >> qabbrev_tac ‘P1 = principal_hnf (P0 @* MAP VAR vs)’
 >> qabbrev_tac ‘Q1 = principal_hnf (Q0 @* MAP VAR vs')’
 >> qabbrev_tac ‘Ps = hnf_children P1’
 >> qabbrev_tac ‘Qs = hnf_children Q1’
 >> qabbrev_tac ‘y  = hnf_head P1’
 >> qabbrev_tac ‘y' = hnf_head Q1’
 (* applying ltree_unfold *)
 >> Q.PAT_X_ASSUM ‘_ = BT' X Q r'’ MP_TAC
 >> simp [BT_def, Once ltree_unfold, BT_generator_def]
 >> Q.PAT_X_ASSUM ‘_ = BT' X P r'’ MP_TAC
 >> simp [BT_def, Once ltree_unfold, BT_generator_def]
 >> NTAC 2 STRIP_TAC
 (* easy case: unsolvable P (and Q) *)
 >> reverse (Cases_on ‘solvable P’)
 >- (‘unsolvable Q’ by PROVE_TAC [lameq_solvable_cong] >> fs [] \\
     rw [llist_rel_def, LLENGTH_MAP])
 (* now both P and Q are solvable *)
 >> ‘solvable Q’ by PROVE_TAC [lameq_solvable_cong]
 >> fs []
 (* applying lameq_principal_hnf_size_eq' *)
 >> Know ‘n = n' /\ vs = vs'’
 >- (reverse CONJ_ASM1_TAC >- rw [Abbr ‘vs’, Abbr ‘vs'’] \\
     qunabbrevl_tac [‘n’, ‘n'’, ‘P0’, ‘Q0’] \\
     MATCH_MP_TAC lameq_principal_hnf_size_eq' >> art [])
 (* clean up now duplicated abbreviations: n' and vs' *)
 >> qunabbrevl_tac [‘n'’, ‘vs'’]
 >> DISCH_THEN (rfs o wrap o GSYM)
 (* proving y = y' *)
 >> STRONG_CONJ_TAC
 >- (MP_TAC (Q.SPECL [‘r'’, ‘X’, ‘P’, ‘Q’, ‘P0’, ‘Q0’, ‘n’, ‘vs’, ‘P1’, ‘Q1’]
                     lameq_principal_hnf_head_eq) \\
     simp [GSYM solvable_iff_has_hnf])
 >> DISCH_THEN (rfs o wrap o GSYM)
 >> qunabbrevl_tac [‘y’, ‘y'’]
 (* applying lameq_principal_hnf_thm' *)
 >> MP_TAC (Q.SPECL [‘r'’, ‘X’, ‘P’, ‘Q’, ‘P0’, ‘Q0’, ‘n’, ‘vs’, ‘P1’, ‘Q1’]
                     lameq_principal_hnf_thm)
 >> simp [GSYM solvable_iff_has_hnf]
 >> rw [llist_rel_def, LLENGTH_MAP, EL_MAP]
 >> Cases_on ‘i < LENGTH Ps’ >> fs [LNTH_fromList, EL_MAP]
 >> Q.PAT_X_ASSUM ‘(EL i Ps,SUC r') = z’  (ONCE_REWRITE_TAC o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘(EL i Qs,SUC r') = z'’ (ONCE_REWRITE_TAC o wrap o SYM)
 >> qexistsl_tac [‘EL i Ps’, ‘EL i Qs’, ‘SUC r'’] >> simp []
 >> qabbrev_tac ‘n = LAMl_size Q0’
 >> qabbrev_tac ‘m = LENGTH Qs’
 >> CONJ_TAC (* 2 symmetric subgoals *)
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC subterm_induction_lemma' \\
      qexistsl_tac [‘P’,‘P0’, ‘n’, ‘m’, ‘vs’, ‘P1’] >> simp [] \\
      qunabbrev_tac ‘vs’ \\
      Q_TAC (RNEWS_TAC (“vs :string list”, “r' :num”, “n :num”)) ‘X’ \\
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
      Q_TAC (RNEWS_TAC (“vs :string list”, “r' :num”, “n :num”)) ‘X’ \\
     ‘DISJOINT (set vs) (FV Q0)’ by METIS_TAC [subterm_disjoint_lemma'] \\
      Q_TAC (HNF_TAC (“Q0 :term”, “vs :string list”,
                      “y  :string”, “args :term list”)) ‘Q1’ \\
     ‘TAKE (LAMl_size Q0) vs = vs’ by rw [] \\
      POP_ASSUM (rfs o wrap) \\
      qunabbrev_tac ‘m’ \\
      AP_TERM_TAC >> simp [Abbr ‘Qs’] ]
QED

(*---------------------------------------------------------------------------*
 *  More subterm properties
 *---------------------------------------------------------------------------*)

Theorem subterm_of_hnf :
    !X M h p r. FINITE X /\ hnf M ==>
      subterm X M (h::p) r =
        let  n = LAMl_size M;
            vs = RNEWS r n X;
            M1 = principal_hnf (M @* MAP VAR vs);
            Ms = hnf_children M1;
             m = LENGTH Ms;
        in
            if h < m then subterm X (EL h Ms) p (SUC r) else NONE
Proof
    rpt STRIP_TAC
 >> ‘solvable M’ by PROVE_TAC [hnf_solvable]
 >> RW_TAC std_ss [subterm_of_solvables]
 >> ‘M0 = M’ by rw [Abbr ‘M0’, principal_hnf_reduce]
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
            M1 = principal_hnf (M @* MAP VAR vs);
            Ms = hnf_children M1
        in
            if h < m then subterm X (EL h Ms) p (SUC r) else NONE
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘solvable M’ by PROVE_TAC [hnf_solvable]
 >> RW_TAC std_ss [subterm_alt]
 >> ‘M0 = M’ by rw [Abbr ‘M0’, principal_hnf_reduce]
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
 >> ‘solvable M’ by PROVE_TAC [hnf_solvable]
 >> RW_TAC std_ss [subterm_of_solvables]
 >> ‘M0 = M’ by rw [Abbr ‘M0’, principal_hnf_reduce]
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

Theorem subterm_of_principal_hnf :
    !X M p r. solvable M /\ p <> [] ==>
              subterm X (principal_hnf M) p r = subterm X M p r
Proof
    rpt STRIP_TAC
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> Cases_on ‘p’ >> fs []
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> ‘solvable M0’ by PROVE_TAC [solvable_principal_hnf]
 >> RW_TAC std_ss [subterm_of_solvables]
 >> ‘M0' = M0’ by rw [Abbr ‘M0'’, Abbr ‘M0’, principal_hnf_stable']
 >> POP_ASSUM (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘n = n'’   (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
QED

Theorem hreduce_subterm_cong :
    !X M N p r. M -h->* N /\ p <> [] ==> subterm X M p r = subterm X N p r
Proof
    rpt STRIP_TAC
 >> ‘M == N’ by PROVE_TAC [hreduces_lameq]
 >> reverse (Cases_on ‘solvable M’)
 >- (‘unsolvable N’ by PROVE_TAC [lameq_solvable_cong] \\
     rw [subterm_of_unsolvables])
 >> ‘solvable N’ by PROVE_TAC [lameq_solvable_cong]
 >> ‘principal_hnf M = principal_hnf N’ by PROVE_TAC [principal_hnf_hreduce]
 >> Cases_on ‘p’ >> fs []
 >> rw [subterm_def]
QED

Theorem BT_ltree_el_eq_none :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r ==>
             (ltree_el (BT' X M r) p = NONE <=> subterm X M p r = NONE)
Proof
    Suff ‘!X. FINITE X ==>
              !p M r. FV M SUBSET X UNION RANK r ==>
                     (ltree_el (BT' X M r) p = NONE <=>
                      subterm X M p r = NONE)’
 >- METIS_TAC []
 >> Q.X_GEN_TAC ‘X’ >> DISCH_TAC
 >> Induct_on ‘p’
 >- rw [BT_ltree_el_NIL]
 >> rpt STRIP_TAC
 >> reverse (Cases_on ‘solvable M’)
 >- rw [subterm_def, BT_of_unsolvables, ltree_el_def]
 (* stage work *)
 >> rw [subterm_def, BT_def, BT_generator_def, Once ltree_unfold, ltree_el_def,
        IF_NONE_EQUALS_OPTION]
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> qabbrev_tac ‘n  = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> qabbrev_tac ‘m = LENGTH args’
 >> simp [LNTH_fromList, GSYM BT_def, EL_MAP]
 >> Cases_on ‘h < m’ >> simp []
 >> qabbrev_tac ‘N = EL h args’
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> qunabbrev_tac ‘N’
 >> MATCH_MP_TAC subterm_induction_lemma'
 >> qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []
QED

Theorem BT_ltree_paths_thm :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r ==>
             (p IN ltree_paths (BT' X M r) <=> subterm X M p r <> NONE)
Proof
    rw [ltree_paths_alt_ltree_el, BT_ltree_el_eq_none]
QED

(* NOTE: p <> [] is required as ‘[] IN ltree_paths (BT' X M r)’ always holds. *)
Theorem ltree_paths_imp_solvable :
    !p X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\ p <> [] /\
              p IN ltree_paths (BT' X M r) ==> solvable M
Proof
    rw [ltree_paths_def]
 >> Cases_on ‘p’ >> fs []
 >> CCONTR_TAC
 >> fs [BT_of_unsolvables, ltree_lookup_def]
QED

(* NOTE: This theorem connects ‘ltree_el’ and ‘ltree_lookup’ for Boehm trees

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
                    “y :string”, “args :term list”)) ‘M1’
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
                    “y :string”, “args :term list”)) ‘M1’
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
 >> ‘p IN ltree_paths (BT' X M r)’ by PROVE_TAC [BT_ltree_paths_thm]
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

   Then M0 := principal_hnf N has the explicit form: ‘LAMl vs (VAR y @* Ms)’,
   and ‘LENGTH Ms = k’ (NOTE: vs, y and k come from ‘ltree_el (BT X M) p’.

 *)
Theorem BT_subterm_thm :
    !p X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              subterm X M p r <> NONE /\ solvable (subterm' X M p r)
        ==> do (N,r') <- subterm X M p r;
               (t,m') <- ltree_el (BT' X M r) p;
               (xs,y) <- t;
                   m <- m';
                  M0 <<- principal_hnf N;
                   n <<- LAMl_size M0;
                  vs <<- RNEWS r' n X;
                  M1 <<- principal_hnf (M0 @* MAP VAR vs);
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
 >> ‘p IN ltree_paths (BT' X M r)’ by PROVE_TAC [BT_ltree_paths_thm]
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
 >> ‘subterm X M p r <> NONE’ by PROVE_TAC [BT_ltree_paths_thm]
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
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> qabbrev_tac ‘n  = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
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
                    “y :string”, “args :term list”)) ‘M1’
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
                    “y :string”, “args :term list”)) ‘M1’
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
    rpt STRIP_TAC
 >> Suff ‘subterm X M p r <> NONE <=> subterm X N p r <> NONE’ >- rw []
 >> Know ‘subterm X M p r <> NONE <=> p IN ltree_paths (BT' X M r)’
 >- (MATCH_MP_TAC (GSYM BT_ltree_paths_thm) >> art [])
 >> Rewr'
 >> Know ‘subterm X N p r <> NONE <=> p IN ltree_paths (BT' X N r)’
 >- (MATCH_MP_TAC (GSYM BT_ltree_paths_thm) >> art [])
 >> Rewr'
 >> PROVE_TAC [lameq_BT_cong]
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
     MATCH_MP_TAC lameq_principal_hnf_size_eq' >> art [])
 (* clean up now duplicated abbreviations: n' and vs' *)
 >> qunabbrevl_tac [‘n'’, ‘vs'’]
 >> DISCH_THEN (rfs o wrap o GSYM)
 (* applying lameq_principal_hnf_thm' *)
 >> MP_TAC (Q.SPECL [‘r’, ‘X’, ‘M’, ‘N’, ‘M0’, ‘M0'’, ‘n’, ‘vs’, ‘M1’, ‘M1'’]
                     lameq_principal_hnf_thm') >> simp []
 >> RW_TAC std_ss [Abbr ‘m’, Abbr ‘m'’]
 (* preparing for hnf_children_FV_SUBSET *)
 >> qabbrev_tac ‘n = LAMl_size M0'’
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0) /\ DISJOINT (set vs) (FV M0')’
      by METIS_TAC [subterm_disjoint_lemma']
 (* NOTE: the next two HNF_TAC will refine M1 and M1' *)
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> Q_TAC (HNF_TAC (“M0':term”, “vs :string list”,
                    “y' :string”, “args':term list”)) ‘M1'’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 (* refine P1 and Q1 again for clear assumptions using them *)
 >> qunabbrevl_tac [‘M1’, ‘M1'’]
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
 >> qabbrev_tac ‘M1' = principal_hnf (M0' @* MAP VAR vs)’
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
    !X Y p M pi r r'.
       FINITE X /\ FINITE Y /\ FV M SUBSET X UNION RANK r /\
       FV (tpm pi M) SUBSET Y UNION RANK r' /\
       set (MAP FST pi) SUBSET RANK r /\
       set (MAP SND pi) SUBSET RANK r' /\ r <= r' ==>
      (subterm X M p r = NONE <=>
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
 >> qabbrev_tac ‘M0' = principal_hnf (tpm pi M)’
 >> Know ‘M0' = tpm pi M0’
 >- (qunabbrevl_tac [‘M0’, ‘M0'’] \\
     MATCH_MP_TAC principal_hnf_tpm' >> art [])
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
 >> Q.PAT_X_ASSUM ‘tpm pi M0 = principal_hnf (tpm pi M)’ (rfs o wrap o SYM)
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
     rw [Abbr ‘M0’, principal_hnf_tpm'])
 >> DISCH_TAC
 >> ‘LENGTH vs1 = n’ by rw [Abbr ‘vs1’, LENGTH_listpm]
 (* stage work, now defining vs2 manually by primitives *)
 >> qabbrev_tac ‘Z = X UNION Y UNION set vs UNION set vs1’
 >> qabbrev_tac ‘z = SUC (string_width Z)’
 (* NOTE: vs is in rank r; vs1 seems also in the same rank *)
 >> qabbrev_tac ‘vs2 = alloc r z n’
 (* properties of vs2 *)
 >> Know ‘DISJOINT (set vs2) Z’
 >- (rw [Abbr ‘vs2’, Abbr ‘z’, DISJOINT_ALT', alloc_def, MEM_GENLIST] \\
     ONCE_REWRITE_TAC [TAUT ‘~P \/ ~R <=> P /\ R ==> F’] \\
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
     rw [DISJOINT_ALT, RANK, alloc_def, MEM_GENLIST] \\
     rw [n2s_11])
 >> DISCH_TAC
 >> ‘ALL_DISTINCT vs2 /\ LENGTH vs2 = n’ by rw [Abbr ‘vs2’, alloc_thm]
 (* stage work *)
 >> Know ‘DISJOINT (set vs2) (FV M0)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘FV M’ >> art [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘M2 = principal_hnf (M0 @* MAP VAR vs2)’
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
                   MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) \\
     ‘FV M0 UNION set vs2 = FV (M0 @* MAP VAR vs2)’ by rw [] >> POP_ORW \\
      qunabbrev_tac ‘M2’ \\
      MATCH_MP_TAC principal_hnf_FV_SUBSET' \\
      ‘solvable (VAR y @* args)’ by rw [hnf_solvable, hnf_appstar] \\
      Suff ‘M0 @* MAP VAR vs2 == VAR y @* args’
      >- PROVE_TAC [lameq_solvable_cong] \\
      rw []))
 >> STRIP_TAC
 (* rewriting M1 and M1' (much harder) by tpm of M2 *)
 >> Know ‘M1 = tpm (ZIP (vs2,vs)) M2’
 >- (simp [Abbr ‘M1’] \\
     MATCH_MP_TAC principal_hnf_tpm_reduce' \\
     Q.PAT_X_ASSUM ‘M2 = VAR y @* args’
        (ONCE_REWRITE_TAC o wrap o SYM) >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘p1 = ZIP (vs2,vs)’
 >> Know ‘M1' = tpm pi (principal_hnf (M0 @* MAP VAR vs1))’
 >- (qunabbrev_tac ‘M1'’ \\
     MATCH_MP_TAC principal_hnf_tpm >> art [] \\
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
     MATCH_MP_TAC principal_hnf_tpm_reduce' \\
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
     >- (‘solvable M2’ by rw [hnf_solvable] \\
         ‘M0 @* MAP VAR vs2 == M2’ by rw [] \\
         qunabbrev_tac ‘M2’ \\
         MATCH_MP_TAC principal_hnf_FV_SUBSET' \\
         PROVE_TAC [lameq_solvable_cong]) \\
    ‘FV (M0 @* MAP VAR vs2) = FV M0 UNION set vs2’ by rw [] >> POP_ORW \\
     DISCH_TAC \\
     Know ‘FV M0 UNION set vs2 SUBSET FV M UNION set vs2’
     >- (Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) \\
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
     >- (‘solvable M2’ by rw [hnf_solvable] \\
         ‘M0 @* MAP VAR vs2 == M2’ by rw [] \\
         qunabbrev_tac ‘M2’ \\
         MATCH_MP_TAC principal_hnf_FV_SUBSET' \\
         PROVE_TAC [lameq_solvable_cong]) \\
    ‘FV (M0 @* MAP VAR vs2) = FV M0 UNION set vs2’ by rw [] >> POP_ORW \\
     DISCH_TAC \\
     Know ‘FV M0 UNION set vs2 SUBSET FV M UNION set vs2’
     >- (Suff ‘FV M0 SUBSET FV M’ >- SET_TAC [] \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) \\
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
                  set (MAP SND pi) SUBSET RANK r' /\ r <= r'
              ==> FV (tpm pi M) SUBSET X UNION RANK r'
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC FV_tpm_lemma
 >> Q.EXISTS_TAC ‘r’ >> art []
 >> ASM_SET_TAC []
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
 >> MP_TAC (Q.SPECL [‘X’, ‘Y’, ‘M’, ‘p’, ‘r’, ‘r'’] subterm_tpm_cong) >> rw []
 >> fs [tpm_rel_alt, solvable_tpm]
QED

Theorem subterm_solvable_cong' :
    !X Y M r r'.
       FINITE X /\ FINITE Y /\
       FV M SUBSET X UNION RANK r /\
       FV M SUBSET Y UNION RANK r' ==>
       !p. p IN ltree_paths (BT' X M r) ==>
          (solvable (subterm' X M p r) <=> solvable (subterm' Y M p r'))
Proof
    rpt STRIP_TAC
 >> ‘subterm X M p r <> NONE’ by PROVE_TAC [BT_ltree_paths_thm]
 >> MP_TAC (Q.SPECL [‘X’, ‘Y’, ‘M’, ‘p’, ‘r’, ‘r'’] subterm_tpm_cong) >> rw []
 >> fs [tpm_rel_alt, solvable_tpm]
QED

Theorem subterm_hnf_children_size_cong :
    !X Y M p r r'. FINITE X /\ FINITE Y /\
         FV M SUBSET X UNION RANK r /\
         FV M SUBSET Y UNION RANK r' /\
         subterm X M p r <> NONE /\ solvable (subterm' X M p r) ==>
         hnf_children_size (principal_hnf (subterm' X M p r)) =
         hnf_children_size (principal_hnf (subterm' Y M p r'))
Proof
    rpt STRIP_TAC
 >> ‘subterm Y M p r' <> NONE /\
     tpm_rel (subterm' X M p r) (subterm' Y M p r')’
       by METIS_TAC [subterm_tpm_cong]
 >> fs [tpm_rel_def]
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
 >> qabbrev_tac ‘N = subterm' X M p r’
 >> rw [principal_hnf_tpm']
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
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> simp [principal_hnf_tpm']
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
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
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw [] >> POP_ASSUM (rfs o wrap)
 >> Know ‘principal_hnf (tpm pi (LAMl vs (VAR y @* args) @* MAP VAR vs)) =
          tpm pi (principal_hnf (LAMl vs (VAR y @* args) @* MAP VAR vs))’
 >- (MATCH_MP_TAC principal_hnf_tpm' \\
    ‘LAMl vs (VAR y @* args) @* MAP VAR vs == VAR y @* args’
       by PROVE_TAC [lameq_LAMl_appstar_VAR] \\
     Suff ‘solvable (VAR y @* args)’ >- PROVE_TAC [lameq_solvable_cong] \\
     MATCH_MP_TAC hnf_solvable >> simp [hnf_appstar])
 >> Rewr'
 >> simp [principal_hnf_beta_reduce, hnf_appstar, tpm_appstar]
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
 >> gs [Abbr ‘M0'’, principal_hnf_tpm']
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
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw [] >> POP_ASSUM (rfs o wrap)
 >> simp [Abbr ‘M1'’, Abbr ‘Ms’, Abbr ‘Ms'’, Abbr ‘l’, Abbr ‘l'’]
 >> Know ‘principal_hnf (tpm pi (LAMl vs (VAR y @* args) @* MAP VAR vs)) =
          tpm pi (principal_hnf (LAMl vs (VAR y @* args) @* MAP VAR vs))’
 >- (MATCH_MP_TAC principal_hnf_tpm' \\
    ‘LAMl vs (VAR y @* args) @* MAP VAR vs == VAR y @* args’
       by PROVE_TAC [lameq_LAMl_appstar_VAR] \\
     Suff ‘solvable (VAR y @* args)’ >- PROVE_TAC [lameq_solvable_cong] \\
     MATCH_MP_TAC hnf_solvable \\
     simp [hnf_appstar])
 >> Rewr'
 >> simp [principal_hnf_beta_reduce, hnf_appstar, tpm_appstar]
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

Theorem BT_ltree_paths_cong :
    !X Y M r r'. FINITE X /\ FINITE Y /\
                 FV M SUBSET X UNION RANK r /\
                 FV M SUBSET Y UNION RANK r'
             ==> ltree_paths (BT' X M r) = ltree_paths (BT' Y M r')
Proof
    rw [Once EXTENSION, BT_ltree_paths_thm]
 >> MATCH_MP_TAC (cj 1 subterm_tpm_cong) >> art []
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

   NOTE: ‘apply [f3;f2;f1] M = (f3 o f2 o f1) M = f3 (f2 (f1 M))’. [] = id.
 *)
Definition apply_transform_def :
    apply_transform (pi :transform) = FOLDR $o I pi
End

Overload apply = “apply_transform”
Overload apply = “\pi (Ms :term list). MAP (apply pi) Ms”
Overload apply = “\pi (Ms :term set).  IMAGE (apply pi) Ms”

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
    (apply [] = (I :term -> term)) /\
    (!f pi M. apply (f::pi) (M :term) = f (apply pi M)) /\
    (!f pi M. apply (SNOC f pi) (M :term) = apply pi (f M))
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

Theorem Boehm_apply_lameta_cong :
    !pi M N. Boehm_transform pi /\ lameta M N ==> lameta (apply pi M) (apply pi N)
Proof
    SNOC_INDUCT_TAC >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> fs [solving_transform_def]
 >- rw [lameta_rules]
 >> MATCH_MP_TAC lameta_subst >> art []
QED

Theorem Boehm_transform_APPEND :
    !p1 p2. Boehm_transform p1 /\ Boehm_transform p2 ==> Boehm_transform (p1 ++ p2)
Proof
    rw [Boehm_transform_def]
QED

Theorem Boehm_apply_APPEND :
    !p1 p2 (M :term). apply (p1 ++ p2) M = apply p1 (apply p2 M)
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

(* |- !M N. solvable (M @@ N) ==> solvable M *)
Theorem solvable_APP_E[local] =
        has_hnf_APP_E |> REWRITE_RULE [GSYM solvable_iff_has_hnf]
                      |> Q.GENL [‘M’, ‘N’]

Theorem unsolvable_apply :
    !pi M. Boehm_transform pi /\ unsolvable M ==> unsolvable (apply pi M)
Proof
    Induct_on ‘pi’ using SNOC_INDUCT >- rw []
 >> simp [FOLDR_SNOC, Boehm_transform_SNOC]
 >> qx_genl_tac [‘t’, ‘M’]
 >> reverse (rw [solving_transform_def])
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> art [] \\
     MATCH_MP_TAC unsolvable_subst >> art [])
 >> FIRST_X_ASSUM MATCH_MP_TAC >> simp []
 >> PROVE_TAC [solvable_APP_E]
QED

Theorem solvable_apply_imp :
    !pi M. Boehm_transform pi /\ solvable (apply pi M) ==> solvable M
Proof
    METIS_TAC [unsolvable_apply]
QED

(* Definition 10.3.5 (ii) *)
Definition head_original_def :
    head_original M0 =
       let n = LAMl_size M0;
          vs = NEWS n (FV M0);
          M1 = principal_hnf (M0 @* MAP VAR vs)
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

(* is_ready' is a more precise version for solvable terms *)
Definition is_ready' :
    is_ready' M <=> is_ready M /\ solvable M
End

(* NOTE: This alternative definition of ‘is_ready’ consumes ‘head_original’
         and eliminated the ‘principal_hnf’ inside it.
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
 >> qabbrev_tac ‘M1 = principal_hnf (N @* MAP VAR vs)’
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
     MATCH_MP_TAC principal_hnf_beta_reduce >> rw [hnf_appstar])
 >> DISCH_THEN (fn th => fs [th, hnf_head_hnf, hnf_children_hnf])
 (* stage work *)
 >> qexistsl_tac [‘y’, ‘args’] >> art []
QED

(* NOTE: this proof relies on the new [NOT_AND'] in boolSimps.BOOL_ss *)
Theorem is_ready_alt' :
    !M. is_ready' M <=> solvable M /\
                        ?y Ns. M -h->* VAR y @* Ns /\ EVERY (\e. y # e) Ns
Proof
    rw [is_ready', is_ready_alt, RIGHT_AND_OVER_OR]
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
                           hnf_children_size (principal_hnf (FST (THE N)))
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
                           LAMl_size (principal_hnf (FST (THE N)))
                        else 0) {q | q <<= p})
End

Theorem subterm_width_nil :
    !M. subterm_width M [] = if solvable M then
                                hnf_children_size (principal_hnf M)
                             else 0
Proof
    rw [subterm_width_def]
QED

Theorem subterm_length_nil :
    !M. subterm_length M [] = if solvable M then
                                 LAMl_size (principal_hnf M)
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
                              hnf_children_size (principal_hnf (FST (THE N)))
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
      simp [principal_hnf_tpm'],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC ‘q’ >> art [] \\
      MP_TAC (Q.SPECL [‘X’, ‘FV M’, ‘M’, ‘q’, ‘r’, ‘0’] subterm_tpm_cong) \\
      rw [tpm_rel_alt] >> gs [] \\
      simp [principal_hnf_tpm'] ]
QED

Theorem subterm_length_thm :
    !X M p r.
       FINITE X /\ FV M SUBSET X UNION RANK r ==>
       subterm_length M p =
       MAX_SET (IMAGE (\q. let N = subterm X M q r in
                           if N <> NONE /\ solvable (FST (THE N)) then
                              LAMl_size (principal_hnf (FST (THE N)))
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
      simp [principal_hnf_tpm'],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC ‘q’ >> art [] \\
      MP_TAC (Q.SPECL [‘X’, ‘FV M’, ‘M’, ‘q’, ‘r’, ‘0’] subterm_tpm_cong) \\
      rw [tpm_rel_alt] >> gs [] \\
      simp [principal_hnf_tpm'] ]
QED

Theorem subterm_width_first :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\ solvable M
          ==> hnf_children_size (principal_hnf M) <= subterm_width M p
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
          ==> LAMl_size (principal_hnf M) <= subterm_length M p
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
   ==> hnf_children_size (principal_hnf (subterm' X M q r)) <= subterm_width M p
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
   ==> LAMl_size (principal_hnf (subterm' X M q r)) <= subterm_length M p
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
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> ‘M0 == M’ by rw [Abbr ‘M0’, lameq_principal_hnf']
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
     >- (simp [SUB_THM] \\
         MATCH_MP_TAC hnf_solvable >> rw [hnf_appstar]) \\
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
 (* applying principal_hnf_hreduce, hreduces_hnf_imp_principal_hnf, etc.

    M -h->* M0 = LAMl vs (VAR y @* args)
    [P/v] M -h->* [P/v] (LAMl vs (VAR y @* args))
  *)
 >> Know ‘[P/v] M -h->* [P/v] M0’
 >- (MATCH_MP_TAC hreduce_substitutive \\
     METIS_TAC [principal_hnf_thm'])
 >> simp [LAMl_SUB, appstar_SUB]
 >> reverse (Cases_on ‘y = v’)
 >- (simp [SUB_THM, solvable_iff_has_hnf] \\
     DISCH_TAC \\
     qabbrev_tac ‘args' = MAP [P/v] args’ \\
    ‘hnf (LAMl vs (VAR y @* args'))’ by rw [hnf_appstar] \\
    ‘principal_hnf ([P/v] M) = LAMl vs (VAR y @* args')’
       by METIS_TAC [principal_hnf_thm'] >> POP_ORW \\
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
 >> ‘principal_hnf ([P/v] M) = LAMl ys (VAR y' @* args2)’
       by METIS_TAC [principal_hnf_thm']
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
         M0 = principal_hnf M /\
          n = LAMl_size M0 /\ n <= n' /\
          m = hnf_children_size M0 /\ h < m /\
        vs' = RNEWS r n' X /\
         M1 = principal_hnf (M0 @* MAP VAR vs') /\
         Ms = hnf_children M1 ==>
        (subterm_width M (h::p) <= d <=>
         m <= d /\ subterm_width (EL h Ms) p <= d)
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> qabbrev_tac ‘m = hnf_children_size M0’
 >> Q_TAC (RNEWS_TAC (“vs' :string list”, “r :num”, “n' :num”)) ‘X’
 >> ‘DISJOINT (set vs') (FV M0)’ by PROVE_TAC [subterm_disjoint_lemma']
 >> qabbrev_tac ‘M1' = principal_hnf (M0 @* MAP VAR vs')’
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
 >> ‘hnf M0’ by PROVE_TAC [hnf_principal_hnf']
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
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
     simp [principal_hnf_thm', GSYM appstar_APPEND, hnf_appstar])
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
         M0 = principal_hnf M /\
          n = LAMl_size M0 /\
          m = hnf_children_size M0 /\ h < m /\
         vs = RNEWS r n X /\
         M1 = principal_hnf (M0 @* MAP VAR vs) /\
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
Theorem subterm_width_induction_lemma_alt :
    !X Y M h p r M0 n n' m vs' M1 Ms d.
         FINITE X /\ FV M SUBSET X UNION RANK r /\ 0 < r /\
         FINITE Y /\ FV M SUBSET Y /\
         M0 = principal_hnf M /\ solvable M /\
          n = LAMl_size M0 /\ n <= n' /\
          m = hnf_children_size M0 /\ h < m /\
        vs' = NEWS n' (X UNION Y) /\
         M1 = principal_hnf (M0 @* MAP VAR vs') /\
         Ms = hnf_children M1 ==>
        (subterm_width M (h::p) <= d <=>
         m <= d /\ subterm_width (EL h Ms) p <= d)
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principal_hnf M’
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
     MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘M1' = principal_hnf (M0 @* MAP VAR vs')’
 >> qabbrev_tac ‘Ms = hnf_children M1'’
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::p’, ‘r’] subterm_width_thm) >> simp []
 >> DISCH_THEN K_TAC (* used already *)
 >> ‘hnf M0’ by PROVE_TAC [hnf_principal_hnf']
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
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR zs)’
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
 >> Know ‘principal_hnf (LAMl vs t @* MAP VAR zs) = tpm (ZIP (vs,zs)) t’
 >- (‘hnf t’ by rw [Abbr ‘t’, hnf_appstar] \\
     MATCH_MP_TAC principal_hnf_tpm_reduce' >> art [] \\
     CONJ_TAC >- rw [Once DISJOINT_SYM] \\
     MATCH_MP_TAC subterm_disjoint_lemma \\
     qexistsl_tac [‘X’, ‘r’, ‘n’] >> simp [] \\
     Know ‘FV M0 SUBSET X UNION RANK r’
     >- (Suff ‘FV M0 SUBSET FV M’ >- METIS_TAC [SUBSET_DEF] \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) \\
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
     MATCH_MP_TAC hreduces_hnf_imp_principal_hnf \\
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
         MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) \\
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
       simp [principal_hnf_tpm'],
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
       simp [principal_hnf_tpm'] ])
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
     qabbrev_tac ‘M0 = principal_hnf M’ \\
     qabbrev_tac ‘n = LAMl_size M0’ \\
     Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’ \\
    ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma'] \\
     qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’ \\
     Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                     “y :string”, “args :term list”)) ‘M1’ \\
    ‘TAKE n vs = vs’ by rw [] \\
     POP_ASSUM (rfs o wrap) \\
    ‘M -h->* M0’ by METIS_TAC [principal_hnf_thm'] \\
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
        ‘LENGTH args = hnf_children_size (principal_hnf M)’ by rw [] \\
         POP_ORW \\
         MATCH_MP_TAC subterm_width_first \\
         qexistsl_tac [‘X’, ‘r’] >> art []) >> DISCH_TAC \\
     reverse (Cases_on ‘v = y’)
     >- (simp [] \\
         DISCH_TAC (* [P/v] M -h->* LAMl vs (VAR y @* args') *) \\
        ‘FV P = {}’ by rw [Abbr ‘P’, FV_permutator] \\
        ‘hnf (LAMl vs (VAR y @* args'))’ by rw [hnf_appstar] \\
        ‘principal_hnf ([P/v] M) = LAMl vs (VAR y @* args')’
           by METIS_TAC [principal_hnf_thm'] >> POP_ORW \\
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
    ‘principal_hnf ([P/v] M) =
     LAMl vs (LAMl xs (LAM y (VAR y @* args' @* MAP VAR xs)))’
       by METIS_TAC [principal_hnf_thm'] >> POP_ORW \\
     simp [hnf_children_size_LAMl, GSYM appstar_APPEND])
 (* stage work *)
 >> rpt GEN_TAC >> STRIP_TAC
 >> ‘p IN ltree_paths (BT' X M r)’ by PROVE_TAC [BT_ltree_paths_thm]
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
 (* Now we need to know the exact form of ‘principal_hnf ([P/v] M)’.

    We know that ‘principal_hnf M = M0 = LAMl vs (VAR y @* args)’, which means
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

    In all these cases, ‘h < hnf_children_size (principal_hnf ([P/v] M))’ holds:
    In Case 1 & 2, ‘hnf_children_size (principal_hnf ([P/v] M)) = LENGTH args’.
    In Case 3, ‘hnf_children_size (principal_hnf ([P/v] M)) >= LENGTH args’.
  *)
 >> ‘M -h->* M0’ by METIS_TAC [principal_hnf_thm']
 (* NOTE: we will need to further do head reductions on ‘[P/v] M0’ *)
 >> Know ‘[P/v] M -h->* [P/v] M0’ >- PROVE_TAC [hreduce_substitutive]
 >> ‘DISJOINT (set vs) (FV P)’ by rw [DISJOINT_ALT', FV_permutator, Abbr ‘P’]
 >> simp [LAMl_SUB, appstar_SUB]
  >> qabbrev_tac ‘args' = MAP [P/v] args’
 >> ‘LENGTH args' = LENGTH args’ by rw [Abbr ‘args'’]
 (* LHS rewriting of args', this will introduce M0' = principal_hnf ([P/v] M)
    and a new set of abbreviations (vs', n', ...).
  *)
 >> CONV_TAC (UNBETA_CONV “subterm X ([P/v] M) (h::q) r”)
 >> qmatch_abbrev_tac ‘f _’
 >> ASM_SIMP_TAC std_ss [subterm_of_solvables]
 >> LET_ELIM_TAC
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
    ‘M0' = LAMl vs (VAR y @* args')’ by METIS_TAC [principal_hnf_thm'] \\
    ‘n = n'’ by rw [Abbr ‘n'’] \\
     POP_ASSUM (rfs o wrap o SYM) >> T_TAC \\
     qunabbrev_tac ‘n'’ \\
     Q.PAT_X_ASSUM ‘vs = vs'’ (rfs o wrap o SYM) \\
    ‘hnf (LAMl vs (VAR y @* args))’ by rw [hnf_appstar] \\
     fs [Abbr ‘M1'’, principal_hnf_beta_reduce] \\
     Q.PAT_X_ASSUM ‘args' = Ms’ (fs o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘m' = m’ (fs o wrap o SYM) \\
     fs [Abbr ‘m'’] >> T_TAC \\
  (* applying subterm_width_induction_lemma' *)
     Know ‘subterm_width ([P/v] M) (h::q) <= d <=>
           m <= d /\ subterm_width (EL h args') q <= d’
     >- (MATCH_MP_TAC subterm_width_induction_lemma' \\
         qexistsl_tac [‘X’, ‘r’, ‘M0'’, ‘n’, ‘vs’, ‘VAR y @* args'’] \\
         simp [principal_hnf_beta_reduce] \\
         CONJ_TAC
         >- (rw [FV_SUB] \\
             MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M’ >> art [] \\
             SET_TAC []) \\
         fs [Abbr ‘m’, Abbr ‘args'’] \\
      (* remaining goal: h::q IN ltree_paths (BT' X ([P/v] M) r) *)
         irule (iffRL BT_ltree_paths_thm) >> art [] \\
         reverse CONJ_TAC
         >- (rw [FV_SUB] \\
             MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M’ >> art [] \\
             SET_TAC []) \\
         Q_TAC (UNBETA_TAC [subterm_of_solvables]) ‘subterm X ([P/v] M) (h::q) r’ \\
         simp [principal_hnf_beta_reduce, EL_MAP] \\
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
         qexistsl_tac [‘M’, ‘principal_hnf M’, ‘LENGTH vs’, ‘LENGTH args’,
                       ‘vs’, ‘M1’] \\
         simp [LAMl_size_hnf, Abbr ‘M1’, principal_hnf_beta_reduce]) >> Rewr' \\
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
     simp [principal_hnf_beta_reduce, LAMl_size_hnf, Abbr ‘M1’])
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
       by METIS_TAC [principal_hnf_thm']
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
 >> ‘M1' = VAR z' @* (args' ++ ls)’ by METIS_TAC [principal_hnf_thm]
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
     irule (iffRL BT_ltree_paths_thm) >> simp [] \\
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
     simp [LAMl_size_hnf, principal_hnf_beta_reduce] \\
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
      by PROVE_TAC [BT_ltree_paths_thm]
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
      (MP_TAC o Q.SPEC ‘M’) >> simp []
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
                    subterm_isub_permutator_cong_alt) >> simp []
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
 >> ‘p IN ltree_paths (BT' X M r)’ by PROVE_TAC [BT_ltree_paths_thm]
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
 >> ‘M -h->* M0’ by METIS_TAC [principal_hnf_thm']
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
 (* LHS rewriting of args', this will introduce M0' = principal_hnf ([P/v] M)
    and a new set of abbreviations (vs', n', ...).
  *)
 >> CONV_TAC (UNBETA_CONV “subterm X ([P/v] M) (h::q) r”)
 >> qmatch_abbrev_tac ‘f _’
 >> ASM_SIMP_TAC std_ss [subterm_of_solvables]
 >> LET_ELIM_TAC
 >> Q.PAT_X_ASSUM ‘subterm X (EL h args) q (SUC r) <> NONE’ MP_TAC
 >> simp [Abbr ‘f’, hnf_children_hnf]
 >> DISCH_TAC (* subterm X (EL h args) q (SUC r) <> NONE *)
 >> Q.PAT_X_ASSUM ‘m = m’ K_TAC
 >> reverse (Cases_on ‘y = v’)
 >- (simp [LAMl_SUB, appstar_SUB] \\
     DISCH_TAC (* [P/v] M -h->* LAMl vs (VAR y @* args') *) \\
    ‘hnf (LAMl vs (VAR y @* args'))’ by rw [hnf_appstar] \\
    ‘M0' = LAMl vs (VAR y @* args')’ by METIS_TAC [principal_hnf_thm'] \\
    ‘n = n'’ by rw [Abbr ‘n'’] \\
     POP_ASSUM (rfs o wrap o SYM) >> T_TAC \\
     qunabbrev_tac ‘n'’ \\
     Q.PAT_X_ASSUM ‘vs = vs'’ (rfs o wrap o SYM) \\
    ‘hnf (LAMl vs (VAR y @* args))’ by rw [hnf_appstar] \\
     fs [Abbr ‘M1'’, principal_hnf_beta_reduce] \\
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
         simp [principal_hnf_beta_reduce, LAMl_size_hnf, Abbr ‘M1’]) \\
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
             MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) \\
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
     Know ‘principal_hnf ([VAR v'/v] M) = [VAR v'/v] M0 <=>
           [VAR v'/v] M -h->* [VAR v'/v] M0 /\ hnf ([VAR v'/v] M0)’
     >- (MATCH_MP_TAC principal_hnf_thm' \\
         simp [GSYM fresh_tpm_subst']) >> Rewr' \\
     simp [LAMl_SUB, appstar_SUB, hnf_appstar])
 >> simp [LAMl_SUB, appstar_SUB]
 >> DISCH_THEN (ASSUME_TAC o SYM)
 >> ‘n' = n’ by rw [Abbr ‘n'’]
 >> POP_ASSUM (fs o wrap)
 >> qunabbrev_tac ‘n'’
 (* stage work *)
 >> fs [Abbr ‘vs'’]
 (* applying principal_hnf_beta_reduce *)
 >> Know ‘M1' = VAR v' @* args'’
 >- (qunabbrev_tac ‘M1'’ \\
     POP_ASSUM (REWRITE_TAC o wrap o SYM) \\
     simp [] \\
     MATCH_MP_TAC principal_hnf_beta_reduce >> simp [hnf_appstar])
 >> DISCH_THEN (ASSUME_TAC o SYM)
 >> ‘Ms = args'’ by rw [Abbr ‘Ms’]
 >> ‘m' = m’ by rw [Abbr ‘m'’]
 >> simp [Abbr ‘args'’, EL_MAP]
 (* applying IH *)
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘q’ >> simp []
 >> CONJ_TAC (* FV (EL h args) SUBSET ... *)
 >- (qunabbrev_tac ‘Y’ \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [])
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
         MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) \\
     simp [Abbr ‘M1’, FV_LAMl, FV_appstar] \\
     rw [SUBSET_DEF, IN_UNION] \\
     DISJ1_TAC >> DISJ2_TAC \\
     Q.EXISTS_TAC ‘FV (EL h args)’ >> art [] \\
     Q.EXISTS_TAC ‘EL h args’ >> fs [EL_MEM])
 >> DISCH_TAC
 >> CCONTR_TAC >> fs [SUBSET_DEF, IN_UNION]
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
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M)’ by METIS_TAC [subterm_disjoint_lemma]
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
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
 >> ‘M -h->* M0’ by METIS_TAC [principal_hnf_thm']
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
 >> simp [principal_hnf_beta_reduce, hnf_appstar, LMAP_fromList,
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
    ‘principal_hnf ([P/v] M) = M0'’ by METIS_TAC [principal_hnf_thm'] \\
     Q.PAT_X_ASSUM ‘hnf M0'’ K_TAC \\
     Q.PAT_X_ASSUM ‘M0 = LAMl vs (VAR y @* args)’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘M1 = VAR y @* args’ (ASSUME_TAC o SYM) \\
    ‘hnf_children M1 = args’ by rw [hnf_children_hnf] \\
    ‘LAMl_size M0' = n’ by rw [Abbr ‘M0'’, LAMl_size_hnf] \\
    ‘principal_hnf (M0' @* MAP VAR vs) = VAR y @* args'’
       by rw [Abbr ‘M0'’, principal_hnf_beta_reduce, hnf_appstar] \\
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
         simp [principal_hnf_beta_reduce, ltree_paths_def] \\
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

    thus ‘principal_hnf ([P/y] M) = LAMl (vs ++ xs ++ [z]) (VAR z @* ...)’

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
 >> ‘principal_hnf ([P/y] M) = t’ by METIS_TAC [principal_hnf_thm']
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
 >> DISCH_TAC (* principal_hnf ([P/y] M) = ... *)
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
 >> qabbrev_tac ‘M1' = principal_hnf (M0' @* MAP VAR zs)’
 >> Know ‘M1' = tpm (ZIP (xs',ys')) t’
 >- (simp [Abbr ‘M0'’, Abbr ‘M1'’, Abbr ‘vs'’, GSYM APPEND_ASSOC, appstar_APPEND,
           LAMl_APPEND] \\
     Know ‘principal_hnf (LAMl vs (LAMl xs' t) @* MAP VAR vs @* MAP VAR ys') =
           principal_hnf (LAMl xs' t @* MAP VAR ys')’
     >- (MATCH_MP_TAC principal_hnf_hreduce \\
         simp [hreduce_BETA_extended]) >> Rewr' \\
     MATCH_MP_TAC principal_hnf_tpm_reduce' >> art [] \\
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
     simp [principal_hnf_beta_reduce, ltree_paths_def] \\
     CONJ_TAC
     >- (rw [FV_SUB, Abbr ‘P’, FV_permutator] \\
         MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M’ >> art [] \\
         SET_TAC []) \\
     simp [Abbr ‘M0'’])
 >> Rewr'
 >> simp [Abbr ‘Ms’, EL_MAP]
 >> ‘EL h args'' = EL h args'’ by rw [Abbr ‘args''’, EL_APPEND1] >> POP_ORW
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
 >> rpt GEN_TAC >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘ss = _’ (REWRITE_TAC o wrap) >> simp []
 >> Q.PAT_X_ASSUM ‘P = permutator d’ K_TAC
 >> qabbrev_tac ‘P = permutator d’
 >> qabbrev_tac ‘N = [P/h] M’
 >> qabbrev_tac ‘ss = MAP (\y. (P,y)) ys’
 >> MP_TAC (Q.SPECL [‘X’, ‘P’, ‘d’, ‘h’, ‘p’, ‘M’, ‘r’]
                    subterm_width_subst_permutator_cong) >> simp []
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
 >> qx_genl_tac [‘ss'’, ‘M’] >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘ss' = _’ (REWRITE_TAC o wrap)
 >> SIMP_TAC std_ss [GENLIST, ISUB_SNOC]
 >> qabbrev_tac ‘P = \i. permutator (d + i)’ >> fs []
 >> qabbrev_tac ‘ss = GENLIST (\i. (P i,y i)) k’
 >> Q.PAT_X_ASSUM ‘!M'. FV M' SUBSET X UNION RANK r /\ _ ==> _’
      (MP_TAC o Q.SPEC ‘M’) >> simp []
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
 >> rpt GEN_TAC >> STRIP_TAC
 >> ‘!t. tpm ((u,v)::pi) t = tpm [(u,v)] (tpm pi t)’ by rw [Once tpm_CONS]
 >> POP_ORW
 >> qabbrev_tac ‘N = tpm pi M’
 (* applying IH *)
 >> Q.PAT_X_ASSUM ‘!X M p r. P’ (MP_TAC o Q.SPECL [‘X’, ‘M’, ‘p’, ‘r’]) >> simp []
 >> STRIP_TAC
 >> POP_ASSUM (REWRITE_TAC o wrap o SYM)
 >> MATCH_MP_TAC subterm_once_fresh_tpm_cong >> simp []
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
     MATCH_MP_TAC lswapstr_unchanged' >> simp [MAP_ZIP])
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
 >- (qunabbrev_tac ‘N’ >> MATCH_MP_TAC FV_tpm_lemma \\
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
 >> Suff ‘DISJOINT (set xs) (FV N)’ >- rw [DISJOINT_ALT, Abbr ‘xs'’]
 >> POP_ASSUM K_TAC
 >> simp [Abbr ‘N’, Abbr ‘xs'’, Abbr ‘ys'’]
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

   NOTE: ‘p <> []’ must be added into antecedents, otherwise the statement
   becomes:

   [...] |- !X M. ?pi. Boehm_transform pi /\ is_ready (apply pi M) /\
                       ?fm. apply pi M == fm ' M

   which is impossible if M is not already "is_ready".
 *)
Theorem Boehm_transform_exists_lemma :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              p <> [] /\ subterm X M p r <> NONE ==>
       ?pi. Boehm_transform pi /\
            is_ready' (apply pi M) /\
            FV (apply pi M) SUBSET X UNION RANK (SUC r) /\
            ?v P. closed P /\
              !q. q <<= p /\ q <> [] ==>
                  subterm X (apply pi M) q r <> NONE /\
                  subterm' X (apply pi M) q r = [P/v] (subterm' X M q r)
Proof
    rpt STRIP_TAC
 >> ‘p IN ltree_paths (BT' X M r)’ by PROVE_TAC [BT_ltree_paths_thm]
 >> ‘(!q. q <<= p ==> subterm X M q r <> NONE) /\
      !q. q <<= FRONT p ==> solvable (subterm' X M q r)’
       by (MATCH_MP_TAC subterm_solvable_lemma >> art [])
 >> ‘solvable M’ by (POP_ASSUM (MP_TAC o Q.SPEC ‘[]’) >> rw [])
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> ‘hnf M0’ by PROVE_TAC [hnf_principal_hnf']
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M)’ by METIS_TAC [subterm_disjoint_lemma]
 >> Know ‘?y args. M0 = LAMl (TAKE n vs) (VAR y @* args)’
 >- (qunabbrev_tac ‘n’ \\
    ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma'] \\
     irule (iffLR hnf_cases_shared) >> rw [] \\
     MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘FV M’ >> art [] \\
     qunabbrev_tac ‘M0’ >> MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art [])
 >> STRIP_TAC
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (REV_FULL_SIMP_TAC std_ss o wrap)
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
 >> Know ‘M1 = VAR y @* args’
 >- (qunabbrev_tac ‘M1’ >> POP_ORW \\
     MATCH_MP_TAC principal_hnf_beta_reduce >> rw [hnf_appstar])
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
         MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art []) \\
     ‘FV M0 UNION set vs = FV (M0 @* MAP VAR vs)’ by rw [FV_appstar_MAP_VAR] \\
      POP_ORW \\
      qunabbrev_tac ‘M1’ \\
      MATCH_MP_TAC principal_hnf_FV_SUBSET' >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘z = SUC (string_width Z)’
 >> qabbrev_tac ‘l = alloc r z (d - m + 1)’
 >> Know ‘ALL_DISTINCT l /\ LENGTH l = d - m + 1’
 >- rw [Abbr ‘l’, alloc_thm]
 >> STRIP_TAC
 >> Know ‘DISJOINT (set l) Z’
 >- (rw [Abbr ‘l’, Abbr ‘z’, DISJOINT_ALT', alloc_def, MEM_GENLIST] \\
     ONCE_REWRITE_TAC [TAUT ‘~P \/ ~R <=> P /\ R ==> F’] \\
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
 >> qabbrev_tac ‘pi = p3 ++ p2 ++ p1’
 >> Know ‘apply pi M == VAR b @* args' @* MAP VAR as’
 >- (MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘apply pi M0’ \\
     CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong \\
                  CONJ_TAC >- art [] \\
                  qunabbrev_tac ‘M0’ \\
                  MATCH_MP_TAC lameq_SYM \\
                  MATCH_MP_TAC lameq_principal_hnf' >> art []) \\
     SIMP_TAC std_ss [Once Boehm_apply_APPEND, Abbr ‘pi’] \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘apply (p3 ++ p2) M1’ \\
     CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong >> art [] \\
                  MATCH_MP_TAC Boehm_transform_APPEND >> art []) \\
     ONCE_REWRITE_TAC [Boehm_apply_APPEND] \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘apply p3 (P @* args')’ >> art [] \\
     MATCH_MP_TAC Boehm_apply_lameq_cong >> rw [])
 >> DISCH_TAC
 >> Know ‘solvable (apply pi M)’
 >- (Suff ‘solvable (VAR b @* args' @* MAP VAR as)’
     >- METIS_TAC [lameq_solvable_cong] \\
     MATCH_MP_TAC hnf_solvable \\
     simp [GSYM appstar_APPEND, hnf_appstar])
 >> DISCH_TAC
 (* stage work *)
 >> Know ‘principal_hnf (apply pi M) = VAR b @* args' @* MAP VAR as’
 >- (Q.PAT_X_ASSUM ‘Boehm_transform pi’         K_TAC \\
     Q.PAT_X_ASSUM ‘Boehm_transform p1’         K_TAC \\
     Q.PAT_X_ASSUM ‘Boehm_transform p2’         K_TAC \\
     Q.PAT_X_ASSUM ‘Boehm_transform p3’         K_TAC \\
     Q.PAT_X_ASSUM ‘apply p1 M0 == M1’          K_TAC \\
     Q.PAT_X_ASSUM ‘apply p2 M1 = P @* args'’   K_TAC \\
     Q.PAT_X_ASSUM ‘apply p3 (P @* args') == _’ K_TAC \\
  (* preparing for principal_hnf_denude_thm *)
     Q.PAT_X_ASSUM ‘apply pi M == _’ MP_TAC \\
     simp [Boehm_apply_APPEND, Abbr ‘pi’, Abbr ‘p1’, Abbr ‘p2’, Abbr ‘p3’,
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
  (* applying principal_hnf_permutator *)
     Know ‘VAR b @* args' @* MAP VAR as =
           principal_hnf ([P/y] (VAR y @* args @* MAP VAR (SNOC b as)))’
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
         MATCH_MP_TAC principal_hnf_permutator >> rw []) >> Rewr' \\
  (* applying principal_hnf_SUB_cong *)
     MATCH_MP_TAC principal_hnf_SUB_cong \\
     CONJ_TAC (* has_hnf #1 *)
     >- (simp [GSYM solvable_iff_has_hnf, GSYM appstar_APPEND] \\
        ‘M0 == M’ by rw [lameq_principal_hnf', Abbr ‘M0’] \\
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
         MATCH_MP_TAC hnf_solvable >> rw [hnf_appstar]) \\
     CONJ_TAC (* has_hnf #2 *)
     >- (REWRITE_TAC [GSYM solvable_iff_has_hnf] \\
         Suff ‘solvable (VAR b @* args' @* MAP VAR as)’
         >- PROVE_TAC [lameq_solvable_cong] \\
         MATCH_MP_TAC hnf_solvable >> rw [hnf_appstar]) \\
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
         MATCH_MP_TAC hnf_solvable >> rw [hnf_appstar]) \\
  (* applying the celebrating principal_hnf_denude_thm

     NOTE: here ‘DISJOINT (set vs) (FV M)’ is required, and this means that
          ‘vs’ must exclude ‘FV M’ instead of just ‘FV M0’.
   *)
     MATCH_MP_TAC principal_hnf_denude_thm >> rw [])
 >> DISCH_TAC
 (* applying is_ready_alt' *)
 >> CONJ_TAC
 >- (simp [is_ready_alt', Abbr ‘pi’] \\
     qexistsl_tac [‘b’, ‘args' ++ MAP VAR as’] \\
     CONJ_TAC
     >- (MP_TAC (Q.SPEC ‘VAR b @* args' @* MAP VAR as’
                   (MATCH_MP principal_hnf_thm'
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
 (* extra goal: FV (apply pi M) SUBSET X UNION RANK (SUC r) *)
 >> CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘apply pi M == _’                K_TAC \\
     Q.PAT_X_ASSUM ‘principal_hnf (apply pi M) = _’ K_TAC \\
     Q.PAT_X_ASSUM ‘apply p3 (P @* args') == _’     K_TAC \\
     rpt (Q.PAT_X_ASSUM ‘Boehm_transform _’         K_TAC) \\
     POP_ASSUM MP_TAC (* solvable (apply pi M) *) \\
     simp [Boehm_apply_APPEND, Abbr ‘pi’, Abbr ‘p1’, Abbr ‘p2’, Abbr ‘p3’,
           Boehm_apply_MAP_rightctxt'] \\
     POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
     DISCH_TAC \\
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
 >> qexistsl_tac [‘y’, ‘P’] >> art []
 >> NTAC 2 STRIP_TAC (* push ‘q <<= p’ to assumptions *)
 (* RHS rewriting from M to M0 *)
 >> Know ‘subterm X M0 q r = subterm X M q r’
 >- (qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC subterm_of_principal_hnf >> art [])
 >> DISCH_THEN (ONCE_REWRITE_TAC o wrap o SYM)
 (* LHS rewriting from M to M0 *)
 >> Know ‘subterm X (apply pi M) q r =
          subterm X (VAR b @* args' @* MAP VAR as) q r’
 >- (Q.PAT_X_ASSUM ‘_ = VAR b @* args' @* MAP VAR as’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     qabbrev_tac ‘t = apply pi M’ \\
     ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC subterm_of_principal_hnf >> art [])
 >> Rewr'
 (* stage cleanups *)
 >> Q.PAT_X_ASSUM ‘solvable (apply pi M)’          K_TAC
 >> Q.PAT_X_ASSUM ‘principal_hnf (apply pi M) = _’ K_TAC
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
 >> ASM_SIMP_TAC std_ss [hnf_head_hnf, var_name_thm]
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
 >> ‘t IN ltree_paths (BT' X N (SUC r))’ by PROVE_TAC [BT_ltree_paths_thm]
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

(* Proposition 10.3.7 (i) [1, p.248] (Boehm out lemma) *)
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
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘p’)) (* put q = p *) >> rw []
 >> qabbrev_tac ‘M' = apply p0 M’
 >> Q.PAT_X_ASSUM ‘is_ready' M'’ (MP_TAC o REWRITE_RULE [is_ready_alt'])
 >> STRIP_TAC
 >> ‘principal_hnf M' = VAR y @* Ns’ by rw [principal_hnf_thm', hnf_appstar]
 (* stage work *)
 >> qunabbrev_tac ‘p’
 >> Know ‘h < LENGTH Ns’
 >- (Q.PAT_X_ASSUM ‘subterm X M' (h::t) r <> NONE’ MP_TAC \\
     RW_TAC std_ss [subterm_of_solvables] >> fs [])
 >> DISCH_TAC
 >> qabbrev_tac ‘m = LENGTH Ns’
 >> qabbrev_tac ‘N = EL h Ns’
 (* stage work *)
 >> Know ‘subterm X N t (SUC r) <> NONE /\
          subterm' X M' (h::t) r = subterm' X N t (SUC r)’
 >- (Q.PAT_X_ASSUM ‘subterm' X M' (h::t) r =
                    [P/v] (subterm' X M (h::t) r)’ K_TAC \\
     Q.PAT_X_ASSUM ‘subterm X M' (h::t) r <> NONE’ MP_TAC \\
     rw [subterm_of_solvables, Abbr ‘N’])
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘subterm' X M' (h::t) r = subterm' X N t (SUC r)’ (fs o wrap)
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
     Q.EXISTS_TAC ‘apply p1 (principal_hnf M')’ \\
     CONJ_TAC >- (MATCH_MP_TAC Boehm_apply_lameq_cong \\
                  CONJ_TAC >- art [] \\
                  MATCH_MP_TAC lameq_SYM \\
                  MATCH_MP_TAC lameq_principal_hnf' >> art []) \\
     rw [Abbr ‘p1’, appstar_SUB] \\
     Know ‘MAP [U/y] Ns = Ns’
     >- (rw [LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC lemma14b \\
         Q.PAT_X_ASSUM ‘EVERY (\e. y # e) Ns’ MP_TAC \\
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
     Q.EXISTS_TAC ‘FV (VAR y @* Ns)’ \\
     reverse CONJ_TAC >- (MATCH_MP_TAC hreduce_FV_SUBSET >> art []) \\
     rw [SUBSET_DEF, FV_appstar, IN_UNION] \\
     DISJ2_TAC \\
     Q.EXISTS_TAC ‘FV (EL h Ns)’ >> art [] \\
     Q.EXISTS_TAC ‘EL h Ns’ >> rw [EL_MEM])
 >> RW_TAC std_ss []
 >> rename1 ‘apply p2 N == _ ISUB ss'’
 >> qabbrev_tac ‘N' = subterm' X M (h::t) r’
 (* final stage *)
 >> Q.EXISTS_TAC ‘p2 ++ p10’
 >> CONJ_TAC >- (MATCH_MP_TAC Boehm_transform_APPEND >> art [])
 >> Q.EXISTS_TAC ‘[(P,v)] ++ ss'’
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘apply p2 N’
 >> simp [ISUB_def]
 >> rw [Boehm_apply_APPEND]
 >> MATCH_MP_TAC Boehm_apply_lameq_cong >> art []
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
 >> MATCH_MP_TAC principal_hnf_bnf >> art []
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
    !M. bnf M ==> BT_valid_paths M = BT_paths M
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘FV M’, ‘M’, ‘0’] BT_valid_paths_thm)
 >> simp []
 >> DISCH_THEN K_TAC
 >> MP_TAC (Q.SPECL [‘FV M’, ‘M’, ‘0’] BT_paths_thm)
 >> simp []
 >> DISCH_THEN K_TAC
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw []
 >> MATCH_MP_TAC BT_ltree_el_neq_bot >> simp []
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

Theorem BT_valid_paths_has_bnf_lemma[local] :
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
 >> MATCH_MP_TAC BT_valid_paths_bnf >> art []
QED

Theorem BT_valid_paths_has_bnf :
    !M. has_bnf M ==> BT_valid_paths M = BT_paths M
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC BT_valid_paths_has_bnf_lemma
 >> qexistsl_tac [‘FV M’, ‘0’] >> simp []
QED

(*---------------------------------------------------------------------------*
 * ltree_finite of BT
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
     simp [principal_hnf_reduce])
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
 >> ‘principal_hnf (VAR v) = VAR v’
      by (MATCH_MP_TAC principal_hnf_reduce >> simp [])
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
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
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
     MATCH_MP_TAC principal_hnf_bnf >> art [])
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

Theorem subtree_equal_refl[simp] :
    subtree_equal X M M p r
Proof
    rw [subtree_equal_def]
QED

Theorem subtree_equal_comm :
    !X M N p r. subtree_equal X M N p r <=> subtree_equal X N M p r
Proof
    rw [subtree_equal_def]
 >> PROVE_TAC []
QED

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
         MATCH_MP_TAC principal_hnf_bnf >> art []) >> Rewr' \\
     reverse CONJ_TAC
     >- (REWRITE_TAC [GSYM LAMl_SNOC] \\
         qabbrev_tac ‘xs = SNOC v vs’ \\
         qabbrev_tac ‘args' = SNOC (VAR v) args’ \\
         simp [BT_def, BT_generator_def, Once ltree_unfold] \\
         Know ‘principal_hnf (LAMl xs (VAR y @* args')) =
               LAMl xs (VAR y @* args')’
         >- (MATCH_MP_TAC principal_hnf_reduce \\
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
         simp [principal_hnf_beta_reduce, hnf_appstar] \\
         simp [LMAP_fromList, MAP_MAP_o, o_DEF] \\
         simp [LIST_EQ_REWRITE, Abbr ‘args'’] \\
         Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
         simp [EL_MAP] \\
        ‘i < m \/ i = m’ by rw [] >- simp [EL_SNOC] \\
        ‘i = LENGTH args’ by rw [] >> POP_ORW \\
         simp [EL_LENGTH_SNOC]) \\
    ‘M = M0’ by METIS_TAC [principal_hnf_bnf] \\
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
     MATCH_MP_TAC principal_hnf_bnf >> art [])
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
     qunabbrev_tac ‘M0’ >> MATCH_MP_TAC principal_hnf_bnf >> art [])
 >> Rewr'
 >> reverse CONJ_TAC
 >- (qmatch_abbrev_tac ‘BT' X (LAMl vs (VAR y @* args')) r = _’ \\
     simp [BT_def, BT_generator_def, Once ltree_unfold] \\
     Know ‘principal_hnf (LAMl vs (VAR y @* args')) = LAMl vs (VAR y @* args')’
     >- (MATCH_MP_TAC principal_hnf_reduce >> simp []) >> Rewr' \\
     simp [GSYM BT_def, principal_hnf_beta_reduce] \\
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
         MATCH_MP_TAC principal_hnf_bnf >> art []) \\
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
     MATCH_MP_TAC principal_hnf_bnf >> art [])
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

   NOTE: The old conclusion “... = SNOC m p INSERT ltree_paths (BT' X M r)” is
   hard to read due to lacks of parenthesis, and has been changed to equivalent
  “... = ltree_paths (BT' X M r) UNION {SNOC m p}”, for audience/reviewers.
 *)
Theorem ltree_paths_BT_expand :
    !X M p r m.
       FINITE X /\ FV M SUBSET X UNION RANK r /\ bnf M /\
       p IN ltree_paths (BT' X M r) /\
       ltree_branching (BT' X M r) p = SOME m ==>
       ltree_paths (BT_expand X (BT' X M r) p r) =
       ltree_paths (BT' X M r) UNION {SNOC m p}
Proof
    rw [BT_expand_def]
 >> qabbrev_tac ‘r' = r + LENGTH p’
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘p’, ‘r’] BT_ltree_el_cases) >> rw []
 >> simp [] (* this simp after rw does beta-reduction on paired variables *)
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
QED

Theorem ltree_paths_BT_expand' :
    !X M p r m.
       FINITE X /\ FV M SUBSET X UNION RANK r /\ has_bnf M /\
       p IN ltree_paths (BT' X M r) /\
       ltree_branching (BT' X M r) p = SOME m ==>
       ltree_paths (BT_expand X (BT' X M r) p r) =
       ltree_paths (BT' X M r) UNION {SNOC m p}
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
 >- (Rewr' \\
     simp [SET_RULE “SNOC m p' INSERT ltree_paths (BT' X N r) =
                     ltree_paths (BT' X N r) UNION {SNOC m p'}”] \\
     MATCH_MP_TAC ltree_paths_BT_expand' \\
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

(* NOTE: This is the explicit form of the Boehm transform constructed in the
   next lemma. It assumes (at least):

   1) FINITE X
   2) BIGUNION (IMAGE FV (set Ms)) SUBSET X UNION RANK r (0 < r)
   3) EVERY solvable Ms
 *)
Definition Boehm_construction_def :
    Boehm_construction X (Ms :term list) p =
    let n_max = MAX_LIST (MAP (\e. subterm_length e p) Ms);
        d_max = MAX_LIST (MAP (\e. subterm_width e p)  Ms) + n_max;
        k     = LENGTH Ms;
        X'    = BIGUNION (IMAGE FV (set Ms));
        vs0   = NEWS (n_max + SUC d_max + k) (X UNION X');
        vs    = TAKE n_max vs0;
        xs    = DROP n_max vs0;
        M  i  = EL i Ms;
        M0 i  = principal_hnf (M i);
        M1 i  = principal_hnf (M0 i @* MAP VAR vs);
        y  i  = hnf_headvar (M1 i);
        P  i  = permutator (d_max + i);
        p1    = MAP rightctxt (REVERSE (MAP VAR vs));
        p2    = REVERSE (GENLIST (\i. [P i/y i]) k);
        p3    = MAP rightctxt (REVERSE (MAP VAR xs))
    in
        p3 ++ p2 ++ p1
End

Theorem Boehm_construction_transform :
    !X Ms p. Boehm_transform (Boehm_construction X Ms p)
Proof
    RW_TAC std_ss [Boehm_construction_def]
 >> MATCH_MP_TAC Boehm_transform_APPEND
 >> reverse CONJ_TAC
 >- rw [Abbr ‘p1’, MAP_MAP_o, GSYM MAP_REVERSE]
 >> MATCH_MP_TAC Boehm_transform_APPEND
 >> CONJ_TAC
 >- rw [Abbr ‘p3’, MAP_MAP_o, GSYM MAP_REVERSE]
 >> rw [Boehm_transform_def, Abbr ‘p2’, EVERY_GENLIST]
QED

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

val _ = export_theory ();
val _ = html_theory "boehm";

(* References:

 [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
     College Publications, London (1984).
 [2] https://en.wikipedia.org/wiki/Corrado_Böhm

 *)
