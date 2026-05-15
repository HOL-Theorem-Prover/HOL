(* ========================================================================== *)
(* FILE    : separabilityScript.sml                                           *)
(* TITLE   : Separability of lambda terms (additional work) [1, Chapter 10.4] *)
(*                                                                            *)
(* AUTHOR  : Chun Tian (binghe) <binghe.lisp@gmail.com> (2026)                *)
(* ========================================================================== *)

Theory separability
Ancestors
  combin option arithmetic pred_set list rich_list llist ltree relation
  topology nomset basic_swap term appFOLDL chap2 chap3 horeduction
  head_reduction standardisation solvable boehm takahashiS3 lameta_complete
Libs
  hurdUtils tautLib numLib listLib NEWLib reductionEval head_reductionLib
  monadsyntax BasicProvers

(* enable basic monad support *)
val _ = enable_monadsyntax ();
val _ = enable_monad "option";

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

(* such re-definitions actually change their priorities *)
Overload FV  = “supp term_pmact”
Overload VAR = “term$VAR”

val _ = temp_clear_overloads_on "fEL"; (* use old EL syntax *)

(*---------------------------------------------------------------------------*
 *  Virtual subterm (vsubterm) of Boehm Trees
 *---------------------------------------------------------------------------*)

(* vsubterm

   ((vs,y),Ms)   vs::[z_0,z_1,z_2,...]
       /\
     /    \      0,   1, .. (j = h - m)
    0 ...  m-1,  m, m+1, .. h
                       (([],z_j),[])
 *)
Definition vsubterm_def :
    vsubterm X M     [] r = SOME (M,r) /\
    vsubterm X M (h::p) r =
    if solvable M then
      let M0 = principal_hnf M;
           n = LAMl_size M0;
          vs = RNEWS r n X;
          M1 = principal_hnf (M0 @* MAP VAR vs);
          Ms = hnf_children M1;
           m = LENGTH Ms;
           j = h - m;
          zs = RNEWS r (n + SUC j) X;
           z = LAST zs;
          M2 = if h < m then EL h Ms else VAR z
      in
        vsubterm X M2 p (SUC r)
    else
      NONE
End

Overload vsubterm' = “\X M p r. FST (THE (vsubterm X M p r))”

(* |- vsubterm X M [] r = SOME (M,r) *)
Theorem vsubterm_NIL[simp] = SPEC_ALL (cj 1 vsubterm_def)

Theorem vsubterm_NIL'[simp] :
    vsubterm' X M [] r = M
Proof
    rw [vsubterm_NIL]
QED

Theorem vsubterm_of_solvables :
    !X M h p r. solvable M ==>
      vsubterm X M (h::p) r =
      let M0 = principal_hnf M;
           n = LAMl_size M0;
          vs = RNEWS r n X;
          M1 = principal_hnf (M0 @* MAP VAR vs);
          Ms = hnf_children M1;
           m = LENGTH Ms;
           j = h - m;
          zs = RNEWS r (n + SUC j) X;
           z = LAST zs;
          M2 = if h < m then EL h Ms else VAR z
      in
          vsubterm X M2 p (SUC r)
Proof
    RW_TAC std_ss [vsubterm_def]
QED

Theorem vsubterm_of_unsolvables :
    !X M p r. unsolvable M /\ p <> [] ==> vsubterm X M p r = NONE
Proof
    rpt STRIP_TAC
 >> Cases_on ‘p’ >> fs []
 >> RW_TAC std_ss [vsubterm_def]
QED

Theorem vsubterm_of_absfree_hnf :
    !X M h p r. hnf M /\ ~is_abs M ==>
       vsubterm X M (h::p) r =
       let Ms = hnf_children M;
            m = LENGTH Ms;
            j = h - m;
           zs = RNEWS r (SUC j) X;
            z = LAST zs;
           M2 = if h < m then EL h Ms else VAR z
       in
           vsubterm X M2 p (SUC r)
Proof
    rpt STRIP_TAC
 >> ‘solvable M’ by PROVE_TAC [hnf_solvable]
 >> RW_TAC std_ss [vsubterm_of_solvables]
 >> ‘M0 = M’ by rw [Abbr ‘M0’, principal_hnf_reduce]
 >> fs [Abbr ‘M0’]
 >> Know ‘n = 0’
 >- (qunabbrev_tac ‘n’ \\
     MATCH_MP_TAC LAMl_size_eq_0 >> art [])
 >> DISCH_THEN (fs o wrap)
 >> fs [Abbr ‘vs’]
 >> Q.PAT_X_ASSUM ‘Ms' = Ms’ (rfs o wrap)
 >> Q.PAT_X_ASSUM ‘m = m'’ (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M = M1’ (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘j = j'’ (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘zs = zs'’ (rfs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘z = z'’ (rfs o wrap o SYM)
QED

Theorem vsubterm_of_absfree_hnf_explicit :
    !X y Ms h p r.
       vsubterm X (VAR y @* Ms) (h::p) r =
       let m = LENGTH Ms;
           j = h - m;
          zs = RNEWS r (SUC j) X;
           z = LAST zs;
          M2 = if h < m then EL h Ms else VAR z
       in
          vsubterm X M2 p (SUC r)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’, ‘VAR y @* Ms’, ‘h’, ‘p’, ‘r’] vsubterm_of_absfree_hnf)
 >> rw [hnf_appstar, is_abs_appstar]
QED

Theorem vsubterm_of_principal_hnf :
    !X M p r. solvable M /\ p <> [] ==>
              vsubterm X (principal_hnf M) p r = vsubterm X M p r
Proof
    rpt STRIP_TAC
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> Cases_on ‘p’ >> fs []
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> ‘solvable M0’ by PROVE_TAC [solvable_principal_hnf]
 >> RW_TAC std_ss [vsubterm_of_solvables]
 >> ‘M0' = M0’ by rw [Abbr ‘M0'’, Abbr ‘M0’, principal_hnf_stable']
 >> POP_ASSUM (fs o wrap)
 >> Q.PAT_X_ASSUM ‘n = n'’   (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘m = m'’   (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘j = j'’   (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘zs = zs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘z = z'’   (fs o wrap o SYM)
QED

Theorem vsubterm_alt_subterm :
    !p X M r. subterm X M p r <> NONE ==> vsubterm X M p r = subterm X M p r
Proof
    Induct_on ‘p’ >> rw [subterm_def, vsubterm_def]
QED

Theorem vsubterm_alt_subterm' :
    !p X M r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              p IN ltree_paths (BT' X M r) ==>
              vsubterm X M p r = subterm X M p r
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC vsubterm_alt_subterm
 >> simp [GSYM BT_ltree_paths_thm]
QED

Theorem subterm_imp_vsubterm_not_none :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              subterm X M p r <> NONE ==> vsubterm X M p r <> NONE
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> qid_specl_tac [‘p’, ‘M’, ‘r’]
 >> Induct_on ‘p’ >- simp []
 >> rpt GEN_TAC >> STRIP_TAC
 >> Q_TAC (UNBETA_TAC [subterm_def]) ‘subterm X M (h::p) r’
 >> STRIP_TAC
 >> Q_TAC (UNBETA_TAC [vsubterm_def]) ‘vsubterm X M (h::p) r’
 >> ‘n' = n’ by simp [Abbr ‘n’, Abbr ‘n'’]
 >> POP_ASSUM (fs o wrap) >> T_TAC
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘m = m'’   (fs o wrap o SYM)
 >> simp [Abbr ‘M2’]
 >> FIRST_X_ASSUM irule >> art []
 >> MATCH_MP_TAC subterm_induction_lemma'
 >> qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp []
 >> simp [Abbr ‘m’, Once EQ_SYM_EQ]
 >> MATCH_MP_TAC hnf_children_size_alt
 >> qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘vs’, ‘M1’] >> simp []
QED

Theorem vsubterm_imp_subterm_none :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              vsubterm X M p r = NONE ==> subterm X M p r = NONE
Proof
    PROVE_TAC [subterm_imp_vsubterm_not_none]
QED

Theorem vsubterm_var :
    !X y p r. FINITE X /\ p <> [] ==>
              vsubterm X (VAR y) p r =
              SOME (VAR (RNEW (r + LENGTH p - 1) (LAST p) X),r + LENGTH p)
Proof
    Q.X_GEN_TAC ‘X’
 >> Suff ‘FINITE X ==>
            !p y r. p <> [] ==>
                    vsubterm X (VAR y) p r =
                    SOME (VAR (RNEW (r + LENGTH p - 1) (LAST p) X),r + LENGTH p)’
 >- METIS_TAC []
 >> DISCH_TAC
 >> Induct_on ‘p’ >> simp [] (* only one goal is left *)
 >> rpt STRIP_TAC
 >> Cases_on ‘p = []’
 >- (simp [RNEW_def] \\
     RW_TAC std_ss [vsubterm_def, GSYM ADD1] >- simp [solvable_VAR] \\
    ‘hnf (VAR y)’ by simp [hnf_thm] \\
    ‘M0 = VAR y’ by simp [Abbr ‘M0’, principal_hnf_reduce] \\
     POP_ASSUM (fs o wrap) \\
     fs [Abbr ‘M0’, Abbr ‘n’] \\
     fs [Abbr ‘vs’] \\
     fs [Abbr ‘M1’, hnf_children_VAR, Abbr ‘Ms’] \\
     fs [Abbr ‘m’, Abbr ‘j’])
 (* stage work *)
 >> simp [LAST_DEF]
 >> RW_TAC std_ss [vsubterm_def] >- simp [solvable_VAR]
 >> ‘hnf (VAR y)’ by simp [hnf_thm]
 >> ‘M0 = VAR y’ by simp [Abbr ‘M0’, principal_hnf_reduce]
 >> POP_ASSUM (fs o wrap) >> T_TAC
 >> fs [Abbr ‘M0’, Abbr ‘n’]
 >> fs [Abbr ‘vs’]
 >> fs [Abbr ‘M1’, hnf_children_VAR, Abbr ‘Ms’]
 >> fs [Abbr ‘m’, Abbr ‘j’]
 >> simp [Abbr ‘M2’]
 >> qabbrev_tac ‘m = LENGTH p’
 >> Suff ‘m + SUC r - 1 = r + SUC m - 1’ >- Rewr
 >> simp []
QED

Theorem vsubterm_var' :
    !X y p r. FINITE X /\ p <> [] ==>
              vsubterm' X (VAR y) p r = VAR (RNEW (r + LENGTH p - 1) (LAST p) X)
Proof
    RW_TAC std_ss [vsubterm_var]
QED

(* NOTE: The exact value of ‘x’ is hard to describe, except for it's row/rank. *)
Theorem vsubterm_eq_var :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              vsubterm X M p r <> NONE /\ subterm X M p r = NONE ==>
              ?x. vsubterm X M p r = SOME (VAR x,r + LENGTH p) /\
                  x IN RANK (r + LENGTH p)
Proof
    Q.X_GEN_TAC ‘X’
 >> Suff ‘FINITE X ==>
           !p M r. FV M SUBSET X UNION RANK r /\ vsubterm X M p r <> NONE /\
                   subterm X M p r = NONE ==>
                   ?x. vsubterm X M p r = SOME (VAR x,r + LENGTH p) /\
                       x IN RANK (r + LENGTH p)’
 >- METIS_TAC []
 >> DISCH_TAC
 >> Induct_on ‘p’ >- simp []
 >> rpt GEN_TAC >> STRIP_TAC
 >> reverse (Cases_on ‘solvable M’)
 >- (Q.PAT_X_ASSUM ‘vsubterm X M (h::p) r <> NONE’ MP_TAC \\
     simp [vsubterm_def])
 >> Q.PAT_X_ASSUM ‘vsubterm X M (h::p) r <> NONE’ MP_TAC
 >> Q.PAT_X_ASSUM ‘subterm X M (h::p) r = NONE’ MP_TAC
 >> Q_TAC (UNBETA_TAC [vsubterm_def]) ‘vsubterm X M (h::p) r’
 >> Q_TAC (UNBETA_TAC [subterm_def]) ‘subterm X M (h::p) r’
 >> ‘n' = n’ by simp [Abbr ‘n’, Abbr ‘n'’]
 >> POP_ASSUM (fs o wrap) >> T_TAC
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘m = m'’ (fs o wrap o SYM)
 >> qabbrev_tac ‘l = LENGTH p’
 >> Cases_on ‘h < m’ >> simp [Abbr ‘M2’]
 >- (Cases_on ‘p = []’ >- simp [subterm_def] \\
    ‘r + SUC l = SUC r + l’ by simp [] >> POP_ORW \\
     rpt STRIP_TAC \\
     FIRST_X_ASSUM irule >> art [] \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
     SYM_TAC >> qunabbrev_tac ‘m’ \\
     MATCH_MP_TAC hnf_children_size_alt \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘vs’, ‘M1’] >> simp [])
 >> Know ‘z IN RANK (SUC r)’
 >- (qunabbrev_tac ‘zs’ \\
     Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n + SUC j”)) ‘X’ \\
    ‘zs <> []’ by simp [NOT_NIL_EQ_LENGTH_NOT_0] \\
    ‘MEM z zs’ by simp [Abbr ‘z’, LAST_MEM] \\
     MP_TAC (Q.SPECL [‘r’, ‘SUC r’, ‘n + SUC j’, ‘X’] RNEWS_SUBSET_RANK) \\
     simp [] \\
     rw [SUBSET_DEF])
 >> DISCH_TAC
 >> Cases_on ‘p = []’
 >- simp [vsubterm_def, Abbr ‘l’, GSYM ADD1]
 >> ‘r + SUC l = SUC r + l’ by simp [] >> POP_ORW
 >> DISCH_TAC
 >> FIRST_X_ASSUM irule >> art []
 >> reverse CONJ_TAC
 >- (Suff ‘FV (VAR z) SUBSET RANK (SUC r)’ >- SET_TAC [] \\
     rw [FV_thm, SUBSET_DEF])
 >> ‘solvable (VAR z)’ by simp []
 >> Cases_on ‘p’ >> fs [] >> T_TAC
 >> RW_TAC std_ss [subterm_def]
 >> ‘hnf (VAR z)’ by simp [hnf_thm]
 >> ‘M0' = VAR z’ by simp [Abbr ‘M0'’, principal_hnf_reduce]
 >> POP_ASSUM (fs o wrap) >> T_TAC
 >> fs [Abbr ‘M0'’, Abbr ‘n'’]
 >> fs [Abbr ‘vs'’]
 >> fs [Abbr ‘M1'’, hnf_children_VAR, Abbr ‘Ms'’]
 >> fs [Abbr ‘m'’]
QED

Theorem vsubterm_eq_var' :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              vsubterm X M p r <> NONE /\ subterm X M p r = NONE ==>
              ?x. vsubterm' X M p r = VAR x /\
                  x IN RANK (r + LENGTH p)
Proof
    rpt GEN_TAC
 >> DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP vsubterm_eq_var))
 >> Q.EXISTS_TAC ‘x’ >> simp []
QED

Theorem vsubterm_var_not_none :
    !X y p r. FINITE X ==> vsubterm X (VAR y) p r <> NONE
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Cases_on ‘p = []’ >- simp [vsubterm_def]
 >> simp [vsubterm_var]
QED

(* cf. lameq_subterm_cong *)
Theorem lameta_vsubterm_cong :
    !X M N p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
                            FV N SUBSET X UNION RANK r /\ M === N
           ==> (vsubterm X M p r = NONE <=> vsubterm X N p r = NONE) /\
               (vsubterm X M p r <> NONE ==>
                vsubterm' X M p r === vsubterm' X N p r)
Proof
    Suff ‘!X. FINITE X ==>
              !p M N r. FV M SUBSET X UNION RANK r /\
                        FV N SUBSET X UNION RANK r /\ M === N
          ==> (vsubterm X M p r = NONE <=> vsubterm X N p r = NONE) /\
              (vsubterm X M p r <> NONE ==>
               vsubterm' X M p r === vsubterm' X N p r)’ >- METIS_TAC []
 >> NTAC 2 STRIP_TAC
 >> Induct_on ‘p’ >- simp []
 >> rpt GEN_TAC >> STRIP_TAC
 >> reverse (Cases_on ‘solvable M’)
 >- (‘unsolvable N’ by PROVE_TAC [lameta_solvable_cong] \\
     simp [vsubterm_def])
 >> ‘solvable N’ by PROVE_TAC [lameta_solvable_cong]
 >> Q_TAC (UNBETA_TAC [vsubterm_def]) ‘vsubterm X M (h::p) r’
 >> Q_TAC (UNBETA_TAC [vsubterm_def]) ‘vsubterm X N (h::p) r’
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> CONJ_TAC
 >- (Cases_on ‘h < m’ >> simp [Abbr ‘M2’]
     >- (MATCH_MP_TAC subterm_induction_lemma' \\
         qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
         simp [Abbr ‘m’, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC hnf_children_size_alt \\
         qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘vs’, ‘M1’] >> simp []) \\
     simp [IN_UNION] >> DISJ2_TAC \\
     Know ‘set zs SUBSET RANK (SUC r)’
     >- (qunabbrev_tac ‘zs’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp []) \\
     Suff ‘z IN set zs’ >- METIS_TAC [SUBSET_DEF] \\
     qunabbrev_tac ‘z’ \\
     MATCH_MP_TAC LAST_MEM \\
     qunabbrev_tac ‘zs’ \\
     Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n + SUC j”)) ‘X’ \\
     simp [NOT_NIL_EQ_LENGTH_NOT_0])
 >> CONJ_TAC
 >- (Cases_on ‘h < m'’ >> simp [Abbr ‘M2'’]
     >- (MATCH_MP_TAC subterm_induction_lemma' \\
         qexistsl_tac [‘N’, ‘M0'’, ‘n'’, ‘m'’, ‘vs'’, ‘M1'’] >> simp [] \\
         simp [Abbr ‘m'’, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC hnf_children_size_alt \\
         qexistsl_tac [‘X’, ‘N’, ‘r’, ‘n'’, ‘vs'’, ‘M1'’] >> simp []) \\
     simp [IN_UNION] >> DISJ2_TAC \\
     Know ‘set zs' SUBSET RANK (SUC r)’
     >- (qunabbrev_tac ‘zs'’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp []) \\
     Suff ‘z' IN set zs'’ >- METIS_TAC [SUBSET_DEF] \\
     qunabbrev_tac ‘z'’ \\
     MATCH_MP_TAC LAST_MEM \\
     qunabbrev_tac ‘zs'’ \\
     Q_TAC (RNEWS_TAC (“zs' :string list”, “r :num”, “n' + SUC j'”)) ‘X’ \\
     simp [NOT_NIL_EQ_LENGTH_NOT_0])
 (* stage work *)
 >> Know ‘M0 === M0'’
 >- (Q_TAC (TRANS_TAC lameta_TRANS) ‘M’ \\
     CONJ_TAC
     >- (MATCH_MP_TAC lameq_imp_lameta \\
         qunabbrev_tac ‘M0’ \\
         MATCH_MP_TAC lameq_principal_hnf' >> art []) \\
     Q_TAC (TRANS_TAC lameta_TRANS) ‘N’ >> art [] \\
     MATCH_MP_TAC lameq_imp_lameta \\
     qunabbrev_tac ‘M0'’ \\
     MATCH_MP_TAC lameq_SYM \\
     MATCH_MP_TAC lameq_principal_hnf' >> art [])
 >> DISCH_TAC
 >> ‘?Z. M0 -be->* Z /\ M0' -be->* Z’ by METIS_TAC [lameta_CR]
 (*
    M -h->* M0 -be->*
    |       |        \
   ===     ===        Z
    |       |        /
    N -h->* M0'-be->*
  *)
 >> qunabbrev_tac ‘vs’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y  :string”, “args :term list”)) ‘M1’
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs) (FV M0)’ K_TAC
 >> ‘TAKE (LAMl_size M0) vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> qunabbrev_tac ‘vs'’
 >> Q_TAC (RNEWS_TAC (“vs' :string list”, “r :num”, “n' :num”)) ‘X’
 >> ‘DISJOINT (set vs') (FV M0')’ by METIS_TAC [subterm_disjoint_lemma']
 >> Q_TAC (HNF_TAC (“M0' :term”, “vs' :string list”,
                    “y'  :string”, “args' :term list”)) ‘M1'’
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs') (FV M0')’ K_TAC
 >> ‘TAKE (LAMl_size M0') vs' = vs'’ by rw []
 >> POP_ASSUM (rfs o wrap)
 (* eliminating Ms and Ms' *)
 >> ‘Ms  = args’  by rw [Abbr ‘Ms’]  >> POP_ASSUM (rfs o wrap)
 >> ‘Ms' = args'’ by rw [Abbr ‘Ms'’] >> POP_ASSUM (rfs o wrap)
 >> qunabbrevl_tac [‘Ms’, ‘Ms'’]
 >> Q.PAT_X_ASSUM ‘M0  = _’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M0' = _’ (ASSUME_TAC o SYM)
 (* applying hnf_bestar_cases *)
 >> MP_TAC (Q.SPECL [‘vs’,  ‘y’,  ‘args’,  ‘Z’] hnf_bestar_cases) >> simp []
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘i’  STRIP_ASSUME_TAC) (* i  and Ns *)
 >> Q.PAT_X_ASSUM ‘Z = _’ (ASSUME_TAC o SYM)
 >> MP_TAC (Q.SPECL [‘vs'’, ‘y'’, ‘args'’, ‘Z’] hnf_bestar_cases) >> simp []
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘i'’ STRIP_ASSUME_TAC) (* i' and Ns' *)
 >> Q.PAT_X_ASSUM ‘Z = _’ (ASSUME_TAC o SYM)
 (*
    M -h->* M0 -be->*
    |       |        \
   ===     ===        Z
    |       |        /
    N -h->* M0'-be->*

   M0  = LAMl vs  (VAR y  @* args)
   Z   = LAMl (TAKE (n - i) vs)  (VAR y  @* (TAKE (m - i) Ns)
   Z   = LAMl (TAKE (n'-i') vs') (VAR y' @* (TAKE (m'-i') Ns')
   M0' = LAMl vs' (VAR y' @* args')
 *)
 >> Know ‘n' - i' = n - i’
 >- (Q.PAT_X_ASSUM ‘_ = Z’ (MP_TAC o AP_TERM “LAMl_size”) \\
     REWRITE_TAC [LAMl_size_hnf] \\
     simp [LENGTH_BUTLASTN] >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘_ = Z’ (MP_TAC o AP_TERM “LAMl_size”) \\
     REWRITE_TAC [LAMl_size_hnf] \\
     simp [LENGTH_BUTLASTN])
 >> DISCH_TAC
 (* stage work *)
 >> gs [BUTLASTN_TAKE_UNCOND, LASTN_DROP_UNCOND]
 >> qabbrev_tac ‘n_max = SUC (MAX n n' + MAX j j')’
 >> Know ‘n <= n_max /\ n' <= n_max’
 >- (simp [Abbr ‘n_max’, MAX_DEF] >> numLib.ARITH_TAC)
 >> STRIP_TAC
 >> Q_TAC (RNEWS_TAC (“xs :string list”, “r :num”, “n_max :num”)) ‘X’
 (* applying TAKE_RNEWS (and TAKE_TAKE) *)
 >> Know ‘TAKE (n - i) vs = TAKE (n - i) xs’
 >- (‘vs = TAKE n xs’ by METIS_TAC [TAKE_RNEWS] >> POP_ORW \\
     irule TAKE_TAKE >> simp [])
 >> DISCH_THEN (fs o wrap)
 >> Q.PAT_X_ASSUM ‘LAMl (TAKE (n - i) vs') _ = Z’ MP_TAC
 >> Know ‘TAKE (n' - i') vs' = TAKE (n' - i') xs’
 >- (‘vs' = TAKE n' xs’ by METIS_TAC [TAKE_RNEWS] >> POP_ORW \\
     irule TAKE_TAKE >> simp [])
 >> simp [] >> DISCH_THEN K_TAC
 >> Q.PAT_X_ASSUM ‘LAMl (TAKE (n - i) xs) _ = Z’ (simp o wrap o SYM)
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘y' = y’ (fs o wrap)
 >> Know ‘m' - i' = m - i’
 >- (POP_ASSUM (MP_TAC o AP_TERM “LENGTH :term list -> num”) \\
     simp [])
 >> DISCH_TAC
 >> Know ‘DROP (n - i) vs = TAKE (n - (n - i)) (DROP (n - i) xs)’
 >- (‘vs = TAKE n xs’ by METIS_TAC [TAKE_RNEWS] >> POP_ORW \\
     REWRITE_TAC [DROP_TAKE])
 >> simp [] >> DISCH_THEN (fs o wrap)
 >> Know ‘DROP (n' - i') vs' = TAKE (n' - (n' - i')) (DROP (n' - i') xs)’
 >- (‘vs' = TAKE n' xs’ by METIS_TAC [TAKE_RNEWS] >> POP_ORW \\
     REWRITE_TAC [DROP_TAKE])
 >> ‘n' - (n' - i') = i'’ by simp [] >> POP_ORW
 >> simp [] >> DISCH_THEN (fs o wrap)
 >> qabbrev_tac ‘xs2 = DROP (n - i) xs’
 (* stage work *)
 >> qunabbrevl_tac [‘M2’, ‘M2'’]
 >> Cases_on ‘h < m’ >> Cases_on ‘h < m'’ >> simp [] (* 4 subgoals *)
 >| [ (* goal 1 (of 4) *)
      Q_TAC (TRANS_TAC lameta_TRANS) ‘EL h Ns’ \\
      CONJ_TAC >- simp [bestar_lameta] \\
      Suff ‘EL h Ns = EL h Ns'’
      >- (Rewr' \\
          MATCH_MP_TAC lameta_SYM >> simp [bestar_lameta]) \\
   (* 0       h1       h2  m     m'
      |<------------>+-i-->|     |  Ns
      |<------------>+-----i'--->|  Ns'
                     |
                   m - i (= m' - i')
    *)
      Cases_on ‘h < m - i’
      >- (Q.PAT_X_ASSUM ‘TAKE (m - i) Ns' = TAKE (m - i) Ns’ MP_TAC \\
          simp [LIST_EQ_REWRITE, EL_TAKE]) \\
      qabbrev_tac ‘m_i = m - i’ \\
      REV_FULL_SIMP_TAC std_ss [NOT_LESS] \\
     ‘h = h - m_i + m_i’ by simp [] >> POP_ORW \\
      Know ‘EL (h - m_i + m_i) Ns = EL (h - m_i) (DROP m_i Ns)’
      >- (SYM_TAC >> MATCH_MP_TAC EL_DROP >> simp []) >> Rewr' \\
      Know ‘EL (h - m_i + m_i) Ns' = EL (h - m_i) (DROP m_i Ns')’
      >- (SYM_TAC >> MATCH_MP_TAC EL_DROP >> simp []) >> Rewr' \\
      ASM_SIMP_TAC std_ss [] \\
     ‘h - m_i < i /\ h - m_i < i'’ by simp [Abbr ‘m_i’] \\
      qabbrev_tac ‘l = TAKE i xs2’ \\
      qabbrev_tac ‘l' = TAKE i' xs2’ \\
      Know ‘LENGTH l = i’
      >- (simp [Abbr ‘l’] \\
          MATCH_MP_TAC LENGTH_TAKE \\
          simp [Abbr ‘xs2’, LENGTH_DROP]) >> DISCH_TAC \\
      Know ‘LENGTH l' = i'’
      >- (simp [Abbr ‘l'’] \\
          MATCH_MP_TAC LENGTH_TAKE \\
          simp [Abbr ‘xs2’, LENGTH_DROP]) >> DISCH_TAC \\
      simp [EL_MAP] \\
      simp [Abbr ‘l’, Abbr ‘l'’, EL_TAKE],
      (* goal 2 (of 4) *)
      REV_FULL_SIMP_TAC std_ss [NOT_LESS] \\
   (* 0                    m'   h   m
      |<------------>+-i'->|    z'  |  Ns'
      |<------------>+------i------>|  Ns
                     |
                   m - i (= m' - i')
    *)
     ‘j = 0’ by simp [Abbr ‘j’] \\
      POP_ASSUM (rfs o wrap) \\
      qunabbrevl_tac [‘j’, ‘zs’, ‘z’] \\
      Suff ‘VAR z' = EL h Ns’ >- (Rewr' >> simp [bestar_lameta]) \\
      qabbrev_tac ‘m_i = m - i’ \\
     ‘h = h - m_i + m_i’ by simp [] >> POP_ORW \\
      Know ‘EL (h - m_i + m_i) Ns = EL (h - m_i) (DROP m_i Ns)’
      >- (SYM_TAC >> MATCH_MP_TAC EL_DROP >> simp []) >> Rewr' \\
      ASM_SIMP_TAC std_ss [] \\
     ‘h - m_i < i’ by simp [Abbr ‘m_i’] \\
      qabbrev_tac ‘l = TAKE i xs2’ \\
      Know ‘LENGTH l = i’
      >- (simp [Abbr ‘l’] \\
          MATCH_MP_TAC LENGTH_TAKE \\
          simp [Abbr ‘xs2’, LENGTH_DROP]) >> DISCH_TAC \\
      simp [EL_MAP] \\
      simp [Abbr ‘l’, EL_TAKE, Abbr ‘z'’] \\
      POP_ASSUM K_TAC \\
      Know ‘n' + SUC j' <= n_max’
      >- (simp [Abbr ‘n_max’, MAX_DEF] \\
          numLib.ARITH_TAC) >> DISCH_TAC \\
      qunabbrev_tac ‘zs'’ \\
      Q_TAC (RNEWS_TAC (“zs' :string list”, “r :num”, “n' + SUC j'”)) ‘X’ \\
     ‘zs' <> []’ by simp [NOT_NIL_EQ_LENGTH_NOT_0] \\
      simp [LAST_EL] \\
     ‘PRE (n' + SUC j') = n' + j'’ by numLib.ARITH_TAC >> POP_ORW \\
     ‘zs' = TAKE (n' + SUC j') xs’ by METIS_TAC [TAKE_RNEWS] >> POP_ORW \\
      simp [EL_TAKE] \\
      simp [Abbr ‘xs2’, EL_DROP] \\
     ‘h + n - (i + m_i) = h + (n' - i') - (m' - i')’ by simp [Abbr ‘m_i’] \\
      POP_ORW \\
      qunabbrev_tac ‘m_i’ \\
     ‘h + (n' - i') - (m' - i') = h + n' - m'’ by simp [] >> POP_ORW \\
      simp [Abbr ‘j'’],
      (* goal 3 (of 4) *)
      REV_FULL_SIMP_TAC std_ss [NOT_LESS] \\
   (* 0                    m    h   m'
      |<------------>+-i'->|    z   |  Ns
      |<------------>+------i------>|  Ns'
                     |
                   m - i (= m' - i')
    *)
     ‘j' = 0’ by simp [Abbr ‘j'’] \\
      POP_ASSUM (rfs o wrap) \\
      qunabbrevl_tac [‘j'’, ‘zs'’, ‘z'’] \\
      Suff ‘VAR z = EL h Ns'’
      >- (Rewr' \\
          MATCH_MP_TAC lameta_SYM >> simp [bestar_lameta]) \\
      qabbrev_tac ‘m_i = m - i’ \\
     ‘m_i <= h’ by simp [Abbr ‘m_i’] \\
     ‘h = h - m_i + m_i’ by simp [] >> POP_ORW \\
      Know ‘EL (h - m_i + m_i) Ns' = EL (h - m_i) (DROP m_i Ns')’
      >- (SYM_TAC >> MATCH_MP_TAC EL_DROP >> simp []) >> Rewr' \\
      ASM_SIMP_TAC std_ss [] \\
     ‘h - m_i < i'’ by simp [Abbr ‘m_i’] \\
      qabbrev_tac ‘l = TAKE i' xs2’ \\
      Know ‘LENGTH l = i'’
      >- (simp [Abbr ‘l’] \\
          MATCH_MP_TAC LENGTH_TAKE \\
          simp [Abbr ‘xs2’, LENGTH_DROP]) >> DISCH_TAC \\
      simp [EL_MAP] \\
      simp [Abbr ‘l’, EL_TAKE, Abbr ‘z’] \\
      POP_ASSUM K_TAC \\
      Know ‘n + SUC j <= n_max’
      >- (simp [Abbr ‘n_max’, MAX_DEF] \\
          numLib.ARITH_TAC) >> DISCH_TAC \\
      qunabbrev_tac ‘zs’ \\
      Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n + SUC j”)) ‘X’ \\
     ‘zs <> []’ by simp [NOT_NIL_EQ_LENGTH_NOT_0] \\
      simp [LAST_EL] \\
     ‘PRE (n + SUC j) = n + j’ by numLib.ARITH_TAC >> POP_ORW \\
     ‘zs = TAKE (n + SUC j) xs’ by METIS_TAC [TAKE_RNEWS] >> POP_ORW \\
      simp [EL_TAKE] \\
      simp [Abbr ‘xs2’, EL_DROP] \\
      simp [Abbr ‘j’, Abbr ‘m_i’],
      (* goal 4 (of 4) *)
      Suff ‘VAR z = VAR z'’ >- simp [lameta_REFL] \\
      REV_FULL_SIMP_TAC std_ss [NOT_LESS] \\
   (* 0                    m        m'  h
      |<------------>+-i'->|        |   z   Ns
      |<------------>+------i------>|   z'  Ns'
                     |
                   m - i (= m' - i')
    *)
      qunabbrev_tac ‘zs’ \\
      Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n + SUC j”)) ‘X’ \\
     ‘zs <> []’ by simp [NOT_NIL_EQ_LENGTH_NOT_0] \\
      qunabbrev_tac ‘zs'’ \\
      Q_TAC (RNEWS_TAC (“zs' :string list”, “r :num”, “n' + SUC j'”)) ‘X’ \\
     ‘zs' <> []’ by simp [NOT_NIL_EQ_LENGTH_NOT_0] \\
      simp [Abbr ‘z’, Abbr ‘z'’, LAST_EL] \\
     ‘PRE (n  + SUC j)  = n  + j’  by numLib.ARITH_TAC >> POP_ORW \\
     ‘PRE (n' + SUC j') = n' + j'’ by numLib.ARITH_TAC >> POP_ORW \\
      Know ‘n + SUC j <= n_max’
      >- (simp [Abbr ‘n_max’, MAX_DEF] \\
          numLib.ARITH_TAC) >> DISCH_TAC \\
      Know ‘n' + SUC j' <= n_max’
      >- (simp [Abbr ‘n_max’, MAX_DEF] \\
          numLib.ARITH_TAC) >> DISCH_TAC \\
     ‘zs  = TAKE (n  + SUC j)  xs’ by METIS_TAC [TAKE_RNEWS] >> POP_ORW \\
     ‘zs' = TAKE (n' + SUC j') xs’ by METIS_TAC [TAKE_RNEWS] >> POP_ORW \\
      simp [EL_TAKE] \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      qunabbrevl_tac [‘j’, ‘j'’] \\
      Suff ‘h - m + n = h - m' + n'’ >- Rewr \\
      Q.PAT_X_ASSUM ‘n' - i' = n - i’ MP_TAC \\
      Q.PAT_X_ASSUM ‘m' - i' = m - i’ MP_TAC \\
      Q.PAT_X_ASSUM ‘i <= n’   MP_TAC \\
      Q.PAT_X_ASSUM ‘i <= m’   MP_TAC \\
      Q.PAT_X_ASSUM ‘i' <= n'’ MP_TAC \\
      Q.PAT_X_ASSUM ‘i' <= m'’ MP_TAC \\
      Q.PAT_X_ASSUM ‘m <= h’   MP_TAC \\
      Q.PAT_X_ASSUM ‘m' <= h’  MP_TAC \\
      numLib.ARITH_TAC ]
QED

Theorem vsubterm_not_none_bnf :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\ bnf M ==>
              vsubterm X M p r <> NONE
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> qid_specl_tac [‘p’, ‘M’, ‘r’]
 >> Induct_on ‘p’ >- simp []
 >> rpt GEN_TAC
 >> NTAC 2 DISCH_TAC
 >> ‘solvable M’ by PROVE_TAC [bnf_solvable]
 >> RW_TAC std_ss [vsubterm_def]
 >> Cases_on ‘h < m’ >> simp [Abbr ‘M2’]
 >- (FIRST_X_ASSUM irule \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC subterm_induction_lemma' \\
         qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
         simp [Abbr ‘m’, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC hnf_children_size_alt \\
         qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘vs’, ‘M1’] >> simp []) \\
     qunabbrev_tac ‘vs’ \\
     Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’ \\
    ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma'] \\
     Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                     “y :string”, “args :term list”)) ‘M1’ \\
    ‘TAKE n vs = vs’ by rw [] \\
     POP_ASSUM (rfs o wrap) \\
    ‘Ms = args’ by simp [Abbr ‘Ms’] \\
     POP_ASSUM (rfs o wrap) \\
     qunabbrev_tac ‘Ms’ \\
     MATCH_MP_TAC hnf_children_bnf \\
     qexistsl_tac [‘vs’, ‘y’] \\
     ASM_SIMP_TAC std_ss [] \\
     Q.PAT_X_ASSUM ‘M0 = _’ (REWRITE_TAC o wrap o SYM) \\
     Suff ‘M0 = M’ >- rw [] \\
     qunabbrev_tac ‘M0’ \\
     MATCH_MP_TAC principal_hnf_bnf >> art [])
 >> Cases_on ‘p = []’ >- simp []
 >> Suff ‘z IN X UNION RANK (SUC r)’
 >- (DISCH_TAC >> simp [vsubterm_var])
 >> simp [Abbr ‘z’, Abbr ‘zs’]
 >> ‘n + SUC j = SUC (n + j)’ by simp [] >> POP_ORW
 >> REWRITE_TAC [GSYM RNEW_def]
 >> MATCH_MP_TAC RNEW_IN_RANK' >> art []
QED

Theorem vsubterm_not_none_has_bnf :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\ has_bnf M ==>
              vsubterm X M p r <> NONE
Proof
    rw [has_bnf_thm]
 >> ‘M == N’ by PROVE_TAC [betastar_lameq]
 >> Know ‘FV N SUBSET X UNION RANK r’
 >- (Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M’ >> art [] \\
     MATCH_MP_TAC betastar_FV_SUBSET >> art [])
 >> DISCH_TAC
 >> Know ‘vsubterm X M p r = NONE <=> vsubterm X N p r = NONE’
 >- (MATCH_MP_TAC (cj 1 lameta_vsubterm_cong) >> art [] \\
     MATCH_MP_TAC lameq_imp_lameta >> art [])
 >> Rewr'
 >> MATCH_MP_TAC vsubterm_not_none_bnf >> art []
QED

Theorem lameta_vsubterm_cong_has_bnf :
    !X M N p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
                          FV N SUBSET X UNION RANK r /\
                M === N /\ has_bnf M /\ has_bnf N
            ==> vsubterm' X M p r === vsubterm' X N p r
Proof
    rpt STRIP_TAC
 >> ‘vsubterm X M p r <> NONE /\
     vsubterm X N p r <> NONE’ by PROVE_TAC [vsubterm_not_none_has_bnf]
 >> MP_TAC (Q.SPECL [‘X’, ‘M’, ‘N’, ‘p’, ‘r’] lameta_vsubterm_cong)
 >> simp []
QED

Theorem vsubterm_is_none_inclusive :
    !X M p r. vsubterm X M p r = NONE <=>
              !q. p <<= q ==> vsubterm X M q r = NONE
Proof
    rpt GEN_TAC
 >> reverse EQ_TAC
 >- (DISCH_THEN (MP_TAC o (Q.SPEC ‘p’)) >> rw [])
 >> qid_specl_tac [‘p’, ‘X’, ‘M’, ‘r’]
 >> Induct_on ‘p’ >- rw [vsubterm_NIL]
 >> rw [vsubterm_def] (* 3 subgoals, same tactics *)
 >> Cases_on ‘q’ >> fs [vsubterm_def]
QED

Theorem vsubterm_is_none_iff_parent_unsolvable :
    !p X M r. FINITE X /\ FV M SUBSET X UNION RANK r ==>
             (vsubterm X M p r = NONE <=>
              p <> [] /\
              (vsubterm X M (FRONT p) r <> NONE ==>
               unsolvable (vsubterm' X M (FRONT p) r)))

Proof
    rpt GEN_TAC
 >> STRIP_TAC >> POP_ASSUM MP_TAC
 >> Suff ‘!p M r. FV M SUBSET X UNION RANK r ==>
                 (vsubterm X M p r = NONE <=>
                  p <> [] /\
                  (vsubterm X M (FRONT p) r <> NONE ==>
                   unsolvable (vsubterm' X M (FRONT p) r)))’ >- METIS_TAC []
 >> Induct_on ‘p’ >- rw [vsubterm_def]
 >> rpt STRIP_TAC
 >> Cases_on ‘p = []’ >> fs []
 >- simp [vsubterm_def]
 >> simp [FRONT_DEF]
 >> reverse (Q_TAC (UNBETA_TAC [vsubterm_def]) ‘vsubterm X M (h::p) r’)
 >- simp [vsubterm_def]
 >> Q_TAC (UNBETA_TAC [vsubterm_def]) ‘vsubterm X M (h::FRONT p) r’
 >> ‘n' = n’ by simp [Abbr ‘n’, Abbr ‘n'’]
 >> POP_ASSUM (fs o wrap) >> T_TAC
 >> Q.PAT_X_ASSUM ‘vs = vs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = M1'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ms = Ms'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘m = m'’   (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘j = j'’   (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘zs = zs'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘z = z'’   (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘M2 = M2'’ (fs o wrap o SYM)
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Cases_on ‘h < m’ >> simp [Abbr ‘M2’]
 >- (MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
     simp [Abbr ‘m’, Once EQ_SYM_EQ] \\
     MATCH_MP_TAC hnf_children_size_alt \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘vs’, ‘M1’] >> simp [])
 >> fs [NOT_LESS]
 >> Suff ‘z IN RANK (SUC r)’ >- rw [IN_UNION]
 >> qunabbrev_tac ‘zs’
 >> Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n + SUC j”)) ‘X’
 >> ‘zs <> []’ by simp [NOT_NIL_EQ_LENGTH_NOT_0]
 >> ‘MEM z zs’ by simp [Abbr ‘z’, LAST_MEM]
 >> MP_TAC (Q.SPECL [‘r’, ‘SUC r’, ‘n + SUC j’, ‘X’] RNEWS_SUBSET_RANK)
 >> simp []
 >> rw [SUBSET_DEF]
QED

Theorem vsubterm_rank_lemma :
    !p X M N r r'. FINITE X /\ FV M SUBSET X UNION RANK r /\
                   vsubterm X M p r = SOME (N,r')
               ==> r' = r + LENGTH p /\ FV N SUBSET X UNION RANK r'
Proof
    Induct_on ‘p’ >- NTAC 2 (rw [])
 >> rpt GEN_TAC
 >> reverse (Cases_on ‘solvable M’) >- rw [vsubterm_def]
 >> UNBETA_TAC [vsubterm_def] “vsubterm X M (h::p) r”
 >> STRIP_TAC
 >> simp []
 >> qabbrev_tac ‘l = LENGTH p’
 >> ‘r + SUC l = SUC r + l’ by simp [] >> POP_ORW
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘M2’ >> art []
 >> Cases_on ‘h < m’ >> simp [Abbr ‘M2’]
 >- (MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
     simp [Abbr ‘m’, Once EQ_SYM_EQ] \\
     MATCH_MP_TAC hnf_children_size_alt \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’, ‘vs’, ‘M1’] >> simp [])
 >> fs [NOT_LESS]
 >> Suff ‘z IN RANK (SUC r)’ >- rw [IN_UNION]
 >> qunabbrev_tac ‘zs’
 >> Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n + SUC j”)) ‘X’
 >> ‘zs <> []’ by simp [NOT_NIL_EQ_LENGTH_NOT_0]
 >> ‘MEM z zs’ by simp [Abbr ‘z’, LAST_MEM]
 >> MP_TAC (Q.SPECL [‘r’, ‘SUC r’, ‘n + SUC j’, ‘X’] RNEWS_SUBSET_RANK)
 >> simp []
 >> rw [SUBSET_DEF]
QED

Theorem FV_vsubterm_upperbound :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r /\
              vsubterm X M p r <> NONE ==>
              FV (vsubterm' X M p r) SUBSET X UNION RANK (r + LENGTH p)
Proof
    rpt STRIP_TAC
 >> fs [GSYM IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS]
 >> Cases_on ‘x’
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘M’, ‘q’, ‘r’, ‘r'’] vsubterm_rank_lemma)
 >> NTAC 2 (rw [])
QED

(* NOTE: ‘vsubterm_width’ further ensures that it's bigger than every index
   in the path, which may be arbitrarily bigger as a virtual path.

   The SUC in “SUC (MAX_LIST p)” is necessary: for even an index 0 in the path,
   it means the vsubterm at that level has at least one child, making the width
   at least be 1 there.
 *)
Definition vsubterm_width_def :
    vsubterm_width M p = MAX (subterm_width M p) (SUC (MAX_LIST p))
End

Theorem subterm_le_vsubterm_width[simp] :
    subterm_width M p <= vsubterm_width M p
Proof
    rw [vsubterm_width_def]
QED

Theorem vsubterm_width_ge_1[simp] :
    1 <= vsubterm_width M p
Proof
    rw [vsubterm_width_def]
QED

(* NOTE: This is the main purpose of introducing ‘vsubterm_width’. *)
Theorem vsubterm_width_thm :
    !p M e. MEM e p ==> e < vsubterm_width M p
Proof
    rw [vsubterm_width_def]
 >> DISJ2_TAC
 >> Suff ‘e <= MAX_LIST p’ >- simp []
 >> MATCH_MP_TAC MAX_LIST_PROPERTY >> art []
QED

Theorem vsubterm_width_nil :
    !M. vsubterm_width M [] =
        if solvable M then MAX (hnf_children_size (principal_hnf M)) 1 else 1
Proof
    rw [vsubterm_width_def, subterm_width_def]
QED

Theorem vsubterm_width_inclusive :
    !M p q d. q <<= p /\ vsubterm_width M p <= d ==> vsubterm_width M q <= d
Proof
    rpt GEN_TAC
 >> simp [vsubterm_width_def]
 >> STRIP_TAC
 >> CONJ_TAC
 >- (MATCH_MP_TAC subterm_width_inclusive \\
     Q.EXISTS_TAC ‘p’ >> art [])
 >> Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘SUC (MAX_LIST p)’
 >> simp []
 >> MATCH_MP_TAC MAX_LIST_LE_PREFIX >> art []
QED

Theorem vsubterm_width_induction_lemma :
    !X M h p r M0 n n' m vs' M1 Ms d.
         FINITE X /\ FV M SUBSET X UNION RANK r /\
         solvable M /\
         M0 = principal_hnf M /\
          n = LAMl_size M0 /\ n <= n' /\
          m = hnf_children_size M0 /\ h < m /\
        vs' = RNEWS r n' X /\
         M1 = principal_hnf (M0 @* MAP VAR vs') /\
         Ms = hnf_children M1 ==>
        (vsubterm_width M (h::p) <= d <=>
         h < d /\ m <= d /\ vsubterm_width (EL h Ms) p <= d)
Proof
    rw [vsubterm_width_def, GSYM LESS_EQ]
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> qabbrev_tac ‘n  = LAMl_size M0’
 >> qabbrev_tac ‘vs = RNEWS r n' X’
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
 >> qabbrev_tac ‘m  = hnf_children_size M0’
 >> qabbrev_tac ‘Ms = hnf_children M1’
 >> Suff ‘subterm_width M (h::p) <= d <=>
          m <= d /\ subterm_width (EL h Ms) p <= d’ >- PROVE_TAC []
 >> MATCH_MP_TAC subterm_width_induction_lemma
 >> qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’, ‘n'’, ‘vs’, ‘M1’] >> simp []
QED

Theorem vsubterm_width_induction_lemma' :
    !X M h p r M0 n m vs M1 Ms d.
         FINITE X /\ FV M SUBSET X UNION RANK r /\
         solvable M /\
         M0 = principal_hnf M /\
          n = LAMl_size M0 /\
          m = hnf_children_size M0 /\ h < m /\
         vs = RNEWS r n X /\
         M1 = principal_hnf (M0 @* MAP VAR vs) /\
         Ms = hnf_children M1 ==>
        (vsubterm_width M (h::p) <= d <=>
         h < d /\ m <= d /\ vsubterm_width (EL h Ms) p <= d)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC vsubterm_width_induction_lemma
 >> qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’, ‘n’, ‘vs’, ‘M1’] >> simp []
QED

Theorem vsubterm_width_var[simp] :
    vsubterm_width (VAR y) p = SUC (MAX_LIST p)
Proof
    RW_TAC std_ss [vsubterm_width_def, subterm_width_var]
QED

(* NOTE: “~(h < m)” is assumed here. *)
Theorem vsubterm_width_eq_first :
    !X M h p r M0 n m.
         FINITE X /\ FV M SUBSET X UNION RANK r /\
         solvable M /\
         M0 = principal_hnf M /\
          n = LAMl_size M0 /\
          m = hnf_children_size M0 /\ ~(h < m) ==>
         vsubterm_width M (h::p) = MAX m (SUC (MAX h (MAX_LIST p)))
Proof
    rw [vsubterm_width_def]
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> qabbrev_tac ‘n  = LAMl_size M0’
 >> qabbrev_tac ‘m  = hnf_children_size M0’
 >> Suff ‘subterm_width M (h::p) = m’ >- Rewr
 >> MATCH_MP_TAC subterm_width_eq_first
 >> qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’, ‘vs’] >> simp []
QED

Theorem vsubterm_width_le_eq_first :
    !X M h p r M0 n m d.
         FINITE X /\ FV M SUBSET X UNION RANK r /\
         solvable M /\
         M0 = principal_hnf M /\
          n = LAMl_size M0 /\
          m = hnf_children_size M0 /\ ~(h < m) ==>
        (vsubterm_width M (h::p) <= d <=> m <= d /\ h < d /\ MAX_LIST p < d)
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> qabbrev_tac ‘n  = LAMl_size M0’
 >> qabbrev_tac ‘m  = hnf_children_size M0’
 >> Know ‘vsubterm_width M (h::p) = MAX m (SUC (MAX h (MAX_LIST p)))’
 >- (MATCH_MP_TAC vsubterm_width_eq_first \\
     qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’] >> simp [])
 >> Rewr'
 >> simp [GSYM LESS_EQ]
QED

(*---------------------------------------------------------------------------*
 *  "Boehm out" technique for single terms at arbitrary path                 *
 *---------------------------------------------------------------------------*)

(* cf. solvable_subst_permutator. Now we work with vsubterm_width *)
Theorem solvable_subst_permutator' :
    !X M r P v d.
       FINITE X /\ FV M SUBSET X UNION RANK r /\
       v IN X UNION RANK r /\ P = permutator d /\
       solvable M /\ vsubterm_width M [] <= d
   ==> solvable ([P/v] M) /\ vsubterm_width ([P/v] M) [] <= d
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
 >> ‘TAKE n vs = vs’ by simp []
 >> POP_ASSUM (rfs o wrap)
 >> ‘M0 == M’ by simp [Abbr ‘M0’, lameq_principal_hnf']
 >> ‘[P/v] M0 == [P/v] M’ by simp [lameq_sub_cong]
 >> ‘FV P = {}’ by simp [Abbr ‘P’, FV_permutator]
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
 >> Know ‘LENGTH args <= d’
 >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘vsubterm_width M []’ >> art [] \\
     Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width M []’ >> simp [] \\
     simp [hnf_children_size_thm, subterm_width_nil])
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
    ‘LENGTH args' = m’ by simp [Abbr ‘args'’] \\
    ‘LENGTH args' <= d’ by simp [Abbr ‘args'’] \\
  (* applying hreduce_permutator_thm *)
     MP_TAC (Q.SPECL [‘{}’, ‘d’, ‘args'’] hreduce_permutator_thm) \\
     rw [Abbr ‘P’] \\
     Q.EXISTS_TAC ‘LAMl xs (LAM y (VAR y @* args' @* MAP VAR xs))’ \\
     rw [hnf_appstar, hnf_thm])
 (* extra goal for induction *)
 >> Q.PAT_X_ASSUM ‘vsubterm_width M [] <= d’ MP_TAC
 >> simp [vsubterm_width_nil]
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

Theorem solvable_subst_permutator_cong' :
    !X M r P v d.
       FINITE X /\ FV M SUBSET X UNION RANK r /\
       v IN X UNION RANK r /\ P = permutator d /\
       vsubterm_width M [] <= d ==> (solvable ([P/v] M) <=> solvable M)
Proof
    rpt STRIP_TAC
 >> EQ_TAC >- PROVE_TAC [unsolvable_subst]
 >> DISCH_TAC
 >> MATCH_MP_TAC (cj 1 solvable_subst_permutator')
 >> qexistsl_tac [‘X’, ‘r’, ‘d’] >> art []
QED

(* NOTE: v, P and d are fixed free variables here *)
Theorem vsubterm_subst_permutator_cong_lemma[local] :
    !X. FINITE X ==>
        !q M p r. q <<= p /\
                  FV M SUBSET X UNION RANK r /\
                  vsubterm X M p r <> NONE /\
                  vsubterm_width M p <= d /\
                  P = permutator d /\ v IN X UNION RANK r
              ==> vsubterm X ([P/v] M) q r <> NONE /\
                  vsubterm_width ([P/v] M) q <= d /\
                  vsubterm' X ([P/v] M) q r = [P/v] (vsubterm' X M q r)
Proof
    NTAC 2 STRIP_TAC
 >> Induct_on ‘q’
 >- (rw [] \\
     qabbrev_tac ‘P = permutator d’ \\
     Know ‘1 <= d’
     >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘vsubterm_width M p’ >> simp []) \\
     DISCH_TAC \\
     Cases_on ‘solvable ([P/v] M)’ \\ (* 2 subgoals, same tactics *)
     rw [vsubterm_width_def, subterm_width_def] \\
  (* only one goal is left *)
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
     >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘vsubterm_width M p’ >> art [] \\
         Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width M p’ >> simp [] \\
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
 (* re-define P as abbreviations *)
 >> Q.PAT_X_ASSUM ‘P = permutator d’ (FULL_SIMP_TAC std_ss o wrap)
 >> qabbrev_tac ‘P = permutator d’
 >> qabbrev_tac ‘Y = X UNION RANK r’
 >> Cases_on ‘p = []’ >- fs []
 >> qabbrev_tac ‘w = vsubterm_width M p’
 (* decompose ‘p’ and eliminate ‘p <> []’ *)
 >> Cases_on ‘p’ >> fs [] >> T_TAC
 >> Q.PAT_X_ASSUM ‘h = h'’ (fs o wrap o SYM)
 >> Know ‘h < w’
 >- (qunabbrev_tac ‘w’ \\
     MATCH_MP_TAC vsubterm_width_thm >> simp [])
 >> DISCH_TAC
 (* preparing for eliminating ‘vsubterm' X M (h::q)’ *)
 >> Know ‘solvable M’
 >- (CCONTR_TAC \\
     Q.PAT_X_ASSUM ‘vsubterm X M (h::t) r <> NONE’ MP_TAC \\
     simp [vsubterm_def])
 >> DISCH_TAC
 >> Know ‘vsubterm X M (h::q) r <> NONE’
 >- (‘h::q <<= h::t’ by simp [] \\
     METIS_TAC [vsubterm_is_none_inclusive])
 >> UNBETA_TAC [vsubterm_of_solvables] “vsubterm X M (h::q) r”
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
 >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width M (h::t)’ \\
     reverse CONJ_TAC >- simp [Abbr ‘w’] \\
     MP_TAC (Q.SPECL [‘X’, ‘M’, ‘h::t’, ‘r’] subterm_width_first) \\
     rw [Abbr ‘w’])
 >> DISCH_TAC
 (* NOTE: ‘[P/v] M’ is solvable iff ‘[P/v] M0’ is solvable, the latter is either
    already a hnf (v <> y), or can be head-reduced to a hnf (v = y).
  *)
 >> Know ‘solvable ([P/v] M)’
 >- (MATCH_MP_TAC (cj 1 solvable_subst_permutator') \\
     qexistsl_tac [‘X’, ‘r’, ‘d’] >> simp [] \\
     MATCH_MP_TAC vsubterm_width_inclusive \\
     Q.EXISTS_TAC ‘h::t’ >> simp [])
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
 >> ‘FV P = {}’ by rw [Abbr ‘P’, FV_permutator]
 >> Know ‘FV ([P/v] M) SUBSET Y’
 >- (simp [FV_SUB] \\
     Cases_on ‘v IN FV M’ >> simp [] \\
     MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘FV M’ >> art [] \\
     SET_TAC [])
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
              LAMl vs (LAMl xs (LAM Z (VAR Z @* args' @* MAP VAR xs))) =
              LAMl (vs ++ xs ++ [Z]) (VAR Z @* args' @* MAP VAR xs), a hnf

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
 >> ‘LENGTH args' = m’ by rw [Abbr ‘args'’]
 (* LHS rewriting of args', this will introduce M0' = principal_hnf ([P/v] M)
    and a new set of abbreviations (vs', n', ...).
  *)
 >> CONV_TAC (UNBETA_CONV “vsubterm X ([P/v] M) (h::q) r”)
 >> qmatch_abbrev_tac ‘f _’
 >> ASM_SIMP_TAC std_ss [vsubterm_of_solvables]
 >> LET_ELIM_TAC
 >> simp [Abbr ‘f’, hnf_children_hnf]
 >> Q.PAT_X_ASSUM ‘m = m’ K_TAC (* a bit strange *)
 (* Case 2 (easy: vs = vs' /\ m = m') *)
 >> reverse (Cases_on ‘y = v’)
 >- (simp [LAMl_SUB, appstar_SUB] \\
     DISCH_TAC (* [P/v] M -h->* LAMl vs (VAR y @* args') *) \\
     Q.PAT_X_ASSUM ‘M0 = _’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘M1 = _’ (ASSUME_TAC o SYM) \\
    ‘hnf (LAMl vs (VAR y @* args'))’ by rw [hnf_appstar] \\
    ‘M0' = LAMl vs (VAR y @* args')’ by METIS_TAC [principal_hnf_thm'] \\
    ‘n = n'’ by rw [Abbr ‘n'’] \\
     POP_ASSUM (rfs o wrap o SYM) >> T_TAC \\
     qunabbrev_tac ‘n'’ \\
     Q.PAT_X_ASSUM ‘vs = vs'’ (rfs o wrap o SYM) \\
    ‘hnf (LAMl vs (VAR y @* args))’ by rw [hnf_appstar] \\
     fs [Abbr ‘M1'’, principal_hnf_beta_reduce] \\
     Q.PAT_X_ASSUM ‘args' = Ms’ (rfs o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘m' = m’     (rfs o wrap) \\
     Q.PAT_X_ASSUM ‘j = j'’     (rfs o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘zs = zs'’   (rfs o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘z = z'’     (rfs o wrap o SYM) \\
     fs [Abbr ‘m'’] >> T_TAC \\
    ‘LENGTH args' = m’ by simp [Abbr ‘args'’] \\
     qunabbrev_tac ‘zs’ \\
     Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n + SUC j”)) ‘X’ \\
    ‘zs <> []’ by simp [NOT_NIL_EQ_LENGTH_NOT_0] \\
     reverse (Cases_on ‘h < m’)
     >- (simp [Abbr ‘M2’, Abbr ‘M2'’, vsubterm_var_not_none] \\
         reverse CONJ_TAC
         >- (SYM_TAC >> MATCH_MP_TAC lemma14b \\
             Cases_on ‘q = []’
             >- (simp [vsubterm_def] \\
                 Suff ‘z NOTIN Y’ >- METIS_TAC [] \\
                 qunabbrev_tac ‘Y’ \\
                 Know ‘z = RNEW r (n + j) X’
                 >- (simp [Abbr ‘z’, Abbr ‘zs’, RNEW_def] \\
                    ‘n + SUC j = SUC (j + n)’ by simp [] \\
                     POP_ASSUM (REWRITE_TAC o wrap)) >> Rewr' \\
                 MATCH_MP_TAC RNEW_thm >> art []) \\
             simp [vsubterm_var, FV_thm] \\
             qabbrev_tac ‘l = LENGTH q’ \\
            ‘0 < l’ by simp [Abbr ‘l’, LENGTH_NON_NIL] \\
             qabbrev_tac ‘r' = l + SUC r - 1’ \\
            ‘r < r'’ by simp [Abbr ‘r'’] \\
            ‘RNEW r' (LAST q) X NOTIN X UNION RANK r'’ by simp [RNEW_thm] \\
             Suff ‘v IN X UNION RANK r'’ >- METIS_TAC [] \\
             Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
             qunabbrev_tac ‘Y’ \\
             Suff ‘RANK r SUBSET RANK r'’ >- SET_TAC [] \\
             MATCH_MP_TAC RANK_MONO >> simp []) \\
         Know ‘vsubterm_width ([P/v] M) (h::q) <= d <=>
               m <= d /\ h < d /\ MAX_LIST q < d’
         >- (MATCH_MP_TAC vsubterm_width_le_eq_first \\
             qexistsl_tac [‘X’, ‘r’, ‘M0'’, ‘n’] >> simp [] \\
             simp [FV_SUB] \\
             Cases_on ‘v IN FV M’ >> simp [] \\
             Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV M’ >> art [] \\
             SET_TAC []) >> Rewr' \\
         simp [] \\
         Q_TAC (TRANS_TAC LET_TRANS) ‘MAX_LIST t’ \\
         CONJ_TAC >- (MATCH_MP_TAC MAX_LIST_LE_PREFIX >> art []) \\
         Q_TAC (TRANS_TAC LTE_TRANS) ‘w’ >> art [] \\
         simp [Abbr ‘w’, vsubterm_width_def, LESS_EQ]) \\
  (* now we have ‘h < m’ (the regular case) *)
     Q.PAT_X_ASSUM ‘vsubterm X M2 q (SUC r) <> NONE’ MP_TAC \\
     simp [Abbr ‘M2’, Abbr ‘M2'’] \\
  (* applying vsubterm_width_induction_lemma' *)
     Know ‘vsubterm_width ([P/v] M) (h::q) <= d <=>
           h < d /\ m <= d /\ vsubterm_width (EL h args') q <= d’
     >- (MATCH_MP_TAC vsubterm_width_induction_lemma' \\
         qexistsl_tac [‘X’, ‘r’, ‘M0'’, ‘n’, ‘vs’, ‘VAR y @* args'’] \\
         simp [principal_hnf_beta_reduce]) >> Rewr' \\
     simp [] >> DISCH_TAC \\
  (* now applying IH *)
     fs [Abbr ‘m’, Abbr ‘args'’, EL_MAP] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘t’ >> simp [] \\
     CONJ_TAC
     >- (Q.PAT_X_ASSUM ‘_ = M0’ (ASSUME_TAC o SYM) \\
         Q.PAT_X_ASSUM ‘_ = M1’ (ASSUME_TAC o SYM) \\
         MATCH_MP_TAC subterm_induction_lemma' \\
         qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘LENGTH args’, ‘vs’, ‘M1’] >> simp []) \\
     CONJ_TAC
     >- (Q.PAT_X_ASSUM ‘vsubterm X M (h::t) r <> NONE’ MP_TAC \\
         Q_TAC (unbeta_tac [vsubterm_def]) ‘vsubterm X M (h::t) r’ \\
         Q.PAT_X_ASSUM ‘_ = M0’ (ASSUME_TAC o SYM) \\
         Q.PAT_X_ASSUM ‘_ = M1’ (ASSUME_TAC o SYM) \\
         simp []) \\
     reverse CONJ_TAC
     >- (Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
         qunabbrev_tac ‘Y’ >> simp [] \\
         Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         rw [RANK_MONO]) \\
     Q.PAT_X_ASSUM ‘w <= d’ MP_TAC \\
     qunabbrev_tac ‘w’ \\
     qabbrev_tac ‘m = LENGTH args’ \\
     Suff ‘vsubterm_width M (h::t) <= d <=>
           h < d /\ m <= d /\ vsubterm_width (EL h args) t <= d’ >- simp [] \\
     MATCH_MP_TAC vsubterm_width_induction_lemma' \\
     qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’, ‘vs’, ‘M1’] >> simp [] \\
     Q.PAT_X_ASSUM ‘_ = M0’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘_ = M1’ (ASSUME_TAC o SYM) \\
     simp [])
 (* Case 3 (hard, vs <<= vs' *)
 >> Q.PAT_X_ASSUM ‘y = v’ (fs o wrap o SYM)
 >> simp [Abbr ‘P’]
 >> DISCH_TAC (* [permutator d/y] M -h->* ... *)
 (* applying hreduce_permutator_thm with a suitable excluded list

    NOTE: ‘vs'’ is to be proved extending vs (vs' = vs ++ ys), and we will need
          DISJOINT (set (SNOC z xs)) (set ys), thus here ‘set vs'’ is used.

    LAMl vs (LAMl xs (LAM Z (VAR Z @* args' @* MAP VAR xs)))

    The goal is make vs ++ xs ++ [Z] = vs', whose LENGTH is n + d - m + 1
  *)
 >> MP_TAC (Q.SPECL [‘set vs'’, ‘d’, ‘args'’] hreduce_permutator_thm) >> simp []
 >> DISCH_THEN (qx_choosel_then [‘xs’, ‘Z’] STRIP_ASSUME_TAC)
 (* calculating head reductions of ‘[permutator d/y] M’ *)
 >> Know ‘[permutator d/y] M -h->*
            LAMl vs (LAMl xs (LAM Z (VAR Z @* args' @* MAP VAR xs)))’
 >- (MATCH_MP_TAC hreduce_TRANS \\
     Q.EXISTS_TAC ‘LAMl vs (permutator d @* args')’ >> rw [])
 >> DISCH_TAC
 >> Know ‘M0' = LAMl vs (LAMl xs (LAM Z (VAR Z @* args' @* MAP VAR xs)))’
 >- (‘hnf (LAMl vs (LAMl xs (LAM Z (VAR Z @* args' @* MAP VAR xs))))’
       by simp[hnf_LAMl, hnf_appstar] \\
     METIS_TAC [principal_hnf_thm'])
 >> DISCH_TAC
 >> qabbrev_tac ‘P = permutator d’
 >> Q.PAT_X_ASSUM ‘P @* args' -h->* _’                 K_TAC
 >> Q.PAT_X_ASSUM ‘[P/y] M -h->* LAMl vs (P @* args')’ K_TAC
 >> Know ‘LENGTH Ms = hnf_children_size M0'’
 >- (SYM_TAC >> MATCH_MP_TAC hnf_children_size_alt \\
     qabbrev_tac ‘M' = [P/y] M’ \\
     qexistsl_tac [‘X’, ‘M'’, ‘r’, ‘n'’, ‘vs'’, ‘M1'’] >> simp [])
 >> DISCH_THEN (ASSUME_TAC o SYM)
 >> Know ‘m <= m'’
 >- (qunabbrevl_tac [‘m’, ‘m'’] \\
     POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [GSYM appstar_APPEND])
 >> DISCH_TAC
 (* 0            h1   m    h2    m' (= d, h < d)
    |<---- args' ---->|<-- xs -->|          M0'
                           d-m
  *)
 >> Know ‘m' = d’
 >- (qunabbrev_tac ‘m'’ \\
     Q.PAT_X_ASSUM ‘_ = LENGTH Ms’ (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘M0' = _’ (REWRITE_TAC o wrap) \\
     simp [GSYM appstar_APPEND])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘M0 = _’          (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M1 = _’          (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘M0' = LAMl vs _’ (ASSUME_TAC o SYM)
 >> fs []
 >> ‘h < d’ by simp []
 >> fs [Abbr ‘M2'’]
 >> ‘j' = 0’ by simp [Abbr ‘j'’]
 >> POP_ASSUM (fs o wrap)
 >> qunabbrevl_tac [‘j'’, ‘zs'’, ‘z'’]
 (* stage work *)
 >> qunabbrev_tac ‘vs'’
 >> Q_TAC (RNEWS_TAC (“vs' :string list”, “r :num”, “n' :num”)) ‘X’
 >> Know ‘n' = n + LENGTH xs + 1’
 >- (qunabbrevl_tac [‘n’, ‘n'’] \\
     Q.PAT_X_ASSUM ‘_ = M0’  (REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘_ = M0'’ (REWRITE_TAC o wrap o SYM) \\
    ‘!t. LAMl vs (LAMl xs (LAM Z t)) = LAMl (vs ++ xs ++ [Z]) t’
        by rw [LAMl_APPEND] >> POP_ORW \\
     Q.PAT_X_ASSUM ‘_ = M1’  (REWRITE_TAC o wrap o SYM) \\
     simp [LAMl_size_LAMl])
 >> DISCH_TAC
 >> Know ‘vs <<= vs'’
 >- (qunabbrevl_tac [‘vs’, ‘vs'’] \\
     MATCH_MP_TAC RNEWS_prefix >> rw [])
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [IS_PREFIX_APPEND]))
 >> rename1 ‘vs' = vs ++ ys’ (* l -> ys *)
 (* stage work *)
 >> gs [MAP_APPEND, appstar_APPEND, LIST_TO_SET_APPEND, ALL_DISTINCT_APPEND]
 (* applying hreduce_BETA_extended *)
 >> Know ‘M0' @* MAP VAR vs @* MAP VAR ys -h->*
          LAMl xs (LAM Z (VAR Z @* args' @* MAP VAR xs)) @* MAP VAR ys’
 >- (Q.PAT_X_ASSUM ‘_ = M0'’ (REWRITE_TAC o wrap o SYM) \\
     REWRITE_TAC [hreduce_BETA_extended])
 >> REWRITE_TAC [GSYM LAMl_SNOC]
 >> DISCH_TAC
 (* applying hreduce_LAMl_appstar *)
 >> qabbrev_tac ‘xs' = SNOC Z xs’
 >> qabbrev_tac ‘t' = VAR Z @* args' @* MAP VAR xs’
 >> Know ‘LAMl xs' t' @* MAP VAR ys -h->* fromPairs xs' (MAP VAR ys) ' t'’
 >- (MATCH_MP_TAC hreduce_LAMl_appstar >> simp [Abbr ‘xs'’] \\
     rw [EVERY_MEM, MEM_MAP] >> REWRITE_TAC [FV_thm] \\
     MATCH_MP_TAC DISJOINT_SUBSET' \\
     Q.EXISTS_TAC ‘set ys’ >> art [] \\
     rw [SUBSET_DEF])
 >> Know ‘LENGTH ys = d - m + 1’
 >- (Q.PAT_X_ASSUM ‘n + LENGTH ys = _’ MP_TAC \\
     Know ‘m <= d’ >- simp [] \\
     numLib.ARITH_TAC)
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘n + LENGTH ys = _’ K_TAC
 >> ‘FDOM (fromPairs xs' (MAP VAR ys)) = set xs'’
      by simp [FDOM_fromPairs, Abbr ‘xs'’]
 >> ASM_SIMP_TAC std_ss [Abbr ‘t'’, ssub_appstar, Abbr ‘xs'’]
 >> qabbrev_tac ‘fm = fromPairs (SNOC Z xs) (MAP VAR ys)’
 >> Know ‘MAP ($' fm) args' = args'’
 >- (simp [LIST_EQ_REWRITE, EL_MAP] \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     MATCH_MP_TAC ssub_14b' >> art [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> simp [MEM_EL] \\
     Q.EXISTS_TAC ‘i’ >> art [])
 >> Rewr'
 >> Know ‘?z'. fm ' (VAR Z) = VAR z'’
 >- (simp [Abbr ‘fm’] \\
     qabbrev_tac ‘ls = SNOC Z xs’ \\
     Know ‘Z = LAST ls’ >- rw [Abbr ‘ls’, LAST_SNOC] \\
    ‘ls <> []’ by rw [Abbr ‘ls’] \\
     simp [LAST_EL] >> DISCH_THEN K_TAC \\
     qabbrev_tac ‘i = PRE (LENGTH ls)’ \\
     Q.EXISTS_TAC ‘EL i ys’ \\
    ‘i < LENGTH ys’ by rw [Abbr ‘i’, Abbr ‘ls’] \\
    ‘VAR (EL i ys) :term = EL i (MAP VAR ys)’ by rw [EL_MAP] >> POP_ORW \\
     MATCH_MP_TAC fromPairs_FAPPLY_EL \\
     simp [Abbr ‘i’, Abbr ‘ls’])
 >> STRIP_TAC >> POP_ORW
 >> qabbrev_tac ‘ls = MAP ($' fm) (MAP VAR xs)’
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
 (* applying vsubterm_width_induction_lemma again *)
 >> Know ‘vsubterm_width ([P/y] M) (h::q) <= d <=>
          h < d /\ m' <= d /\ vsubterm_width (EL h Ms) q <= d’
 >- (MATCH_MP_TAC vsubterm_width_induction_lemma' \\
     qexistsl_tac [‘X’, ‘r’, ‘M0'’, ‘n'’, ‘vs'’, ‘M1'’] \\
     simp [appstar_APPEND])
 >> Rewr'
 >> simp []
 (* extra case for vsubterm
    0                 m    h    d/m' (h < d)
    |<---- args' ---->|<-- ls -->|   M1'
                        j  d-m       (j = h - m)
  *)
 >> reverse (Cases_on ‘h < m’)
 >- (simp [Abbr ‘M2’] \\
    ‘Ms = args' ++ ls’ by simp [Abbr ‘Ms’] >> POP_ORW \\
     Know ‘EL h (args' ++ ls) = EL (h - LENGTH args') ls’
     >- (irule EL_APPEND2 >> simp [Abbr ‘args'’]) >> Rewr' \\
     fs [] >> T_TAC \\
    ‘j < LENGTH xs’ by simp [Abbr ‘j’] \\
     simp [Abbr ‘ls’, MAP_MAP_o, EL_MAP, EL_MEM] \\
    ‘EL j xs = EL j (SNOC Z xs)’ by simp [EL_SNOC] >> POP_ORW \\
     Know ‘FAPPLY fm (EL j (SNOC Z xs)) = EL j (MAP VAR ys)’
     >- (qunabbrev_tac ‘fm’ \\
         MATCH_MP_TAC fromPairs_FAPPLY_EL >> simp []) >> Rewr' \\
     simp [EL_MAP] \\
     qunabbrev_tac ‘zs’ \\
     Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n + SUC j”)) ‘X’ \\
    ‘zs <> []’ by simp [GSYM LENGTH_NON_NIL] \\
     simp [Abbr ‘z’, LAST_EL] \\
    ‘PRE (n + SUC j) = n + j’ by simp [] >> POP_ORW \\
    ‘EL j ys = EL (n + j) vs'’ by simp [EL_APPEND2] >> POP_ORW \\
     Know ‘zs = TAKE (n + SUC j) vs'’
     >- (qunabbrevl_tac [‘zs’, ‘vs'’] \\
         MATCH_MP_TAC RNEWS_TAKE >> simp []) >> Rewr' \\
     Know ‘EL (n + j) (TAKE (n + SUC j) vs') = EL (n + j) vs'’
     >- (MATCH_MP_TAC EL_TAKE >> simp []) >> Rewr' \\
     qabbrev_tac ‘z = EL (n + j) vs'’ \\
     Q.PAT_X_ASSUM ‘vs' = vs ++ ys’ K_TAC \\
     qunabbrev_tac ‘vs'’ \\
     Q_TAC (RNEWS_TAC (“vs' :string list”, “r :num”,
                       “d + (n + 1) - (m :num)”)) ‘X’ \\
     Know ‘DISJOINT (set vs') Y’
     >- (simp [Abbr ‘Y’, DISJOINT_UNION'] \\
         qunabbrev_tac ‘vs'’ \\
         MATCH_MP_TAC DISJOINT_RNEWS_RANK' >> art []) >> DISCH_TAC \\
     Know ‘y <> z’
     >- (Suff ‘z NOTIN Y’ >- METIS_TAC [] \\
         Suff ‘MEM z vs'’
         >- (POP_ASSUM MP_TAC >> rw [DISJOINT_ALT]) \\
         simp [EL_MEM, Abbr ‘z’]) >> DISCH_TAC \\
     Know ‘SUC (MAX_LIST q) <= d’
     >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘w’ >> art [] \\
         simp [Abbr ‘w’, vsubterm_width_def] \\
         NTAC 2 DISJ2_TAC \\
         MATCH_MP_TAC MAX_LIST_LE_PREFIX >> art []) >> Rewr \\
     Cases_on ‘q = []’ >- simp [vsubterm_def] \\
     simp [vsubterm_var] \\
     SYM_TAC >> MATCH_MP_TAC lemma14b >> simp [FV_thm] \\
     qabbrev_tac ‘r' = LENGTH q + SUC r - 1’ \\
     Suff ‘RNEW r' (LAST q) X NOTIN Y’ >- METIS_TAC [] \\
  (* applying RNEW_thm *)
     qunabbrev_tac ‘Y’ \\
     Know ‘RNEW r' (LAST q) X NOTIN X UNION RANK r'’ >- simp [RNEW_thm] \\
     Suff ‘RANK r SUBSET RANK r'’ >- SET_TAC [] \\
     MATCH_MP_TAC RANK_MONO >> simp [Abbr ‘r'’])
 >> Know ‘EL h Ms = EL h args'’
 >- (simp [Abbr ‘Ms’, hnf_children_hnf] \\
     MATCH_MP_TAC EL_APPEND1 >> art [])
 >> Rewr'
 >> Q.PAT_X_ASSUM ‘vsubterm X M2 q (SUC r) <> NONE’ MP_TAC
 >> simp [Abbr ‘args'’, EL_MAP, Abbr ‘M2’]
 >> qabbrev_tac ‘N = EL h args’
 >> DISCH_TAC
 (* applying IH, finally *)
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘t’ >> simp []
 >> CONJ_TAC (* FV N SUBSET X UNION RANK (SUC r) *)
 >- (qunabbrev_tac ‘N’ \\
     MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [] \\
     Q.PAT_X_ASSUM ‘LAMl vs M1 = M0’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘VAR y @* args = M1’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     simp [])
 >> CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘vsubterm X M (h::t) r <> NONE’ MP_TAC \\
     Q_TAC (unbeta_tac [vsubterm_def]) ‘vsubterm X M (h::t) r’ \\
     Q.PAT_X_ASSUM ‘_ = M0’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘_ = M1’ (ASSUME_TAC o SYM) \\
     simp [])
 >> reverse CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘v IN Y’ MP_TAC \\
     qunabbrev_tac ‘Y’ >> simp [] \\
     Suff ‘RANK r SUBSET RANK (SUC r)’ >- SET_TAC [] \\
     rw [RANK_MONO])
 >> Q.PAT_X_ASSUM ‘w <= d’ MP_TAC
 >> qunabbrev_tac ‘w’
 >> Suff ‘vsubterm_width M (h::t) <= d <=>
          h < d /\ m <= d /\ vsubterm_width (EL h args) t <= d’ >- simp []
 >> MATCH_MP_TAC vsubterm_width_induction_lemma'
 >> qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’, ‘vs’, ‘M1’] >> simp []
 >> Q.PAT_X_ASSUM ‘_ = M0’ (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM ‘_ = M1’ (ASSUME_TAC o SYM)
 >> simp []
QED

(* This theorem can be repeatedly applied for ‘M ISUB ss’ *)
Theorem vsubterm_subst_permutator_cong :
    !p X M r y P d. FINITE X /\ FV M SUBSET X UNION RANK r /\
                    vsubterm X M p r <> NONE /\
                    P = permutator d /\ y IN X UNION RANK r /\
                    vsubterm_width M p <= d
                ==> vsubterm X ([P/y] M) p r <> NONE /\
                    vsubterm_width ([P/y] M) p <= d /\
                    vsubterm' X ([P/y] M) p r = [P/y] (vsubterm' X M p r)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> irule vsubterm_subst_permutator_cong_lemma >> art []
 >> Q.EXISTS_TAC ‘p’ >> rw []
QED

(* NOTE: This reduced version is for applying MATCH_MP_TAC later *)
Theorem vsubterm_subst_permutator_cong'[local] :
    !p X M r y P d. FINITE X /\ FV M SUBSET X UNION RANK r /\
                    vsubterm X M p r <> NONE /\
                    P = permutator d /\ y IN X UNION RANK r /\
                    vsubterm_width M p <= d
                ==> vsubterm X ([P/y] M) p r <> NONE /\
                    vsubterm' X ([P/y] M) p r = [P/y] (vsubterm' X M p r)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘M’, ‘r’, ‘y’, ‘P’, ‘d’]
                    vsubterm_subst_permutator_cong) >> rw []
QED

(* cf. Boehm_transform_exists_lemma (for subterm) *)
Theorem Boehm_transform_exists_lemma' :
    !X M p r. FINITE X /\ FV M SUBSET X UNION RANK r ==>
         ?pi. Boehm_transform pi /\
              is_ready (apply pi M) /\
              FV (apply pi M) SUBSET X UNION RANK (SUC r) /\
              ?v P. closed P /\
                   !q. q <<= p /\ q <> [] /\
                       vsubterm X M q r <> NONE ==>
                       vsubterm X (apply pi M) q r <> NONE /\
                       vsubterm' X (apply pi M) q r = [P/v] (vsubterm' X M q r)
Proof
    rpt STRIP_TAC
 (* trivial case: M is unsolvable *)
 >> reverse (Cases_on ‘solvable M’)
 >- (Q.EXISTS_TAC ‘[]’ >> simp [is_ready_def] \\
     CONJ_TAC
     >- (Suff ‘RANK r SUBSET RANK (SUC r)’ >- ASM_SET_TAC [] \\
         simp [RANK_MONO]) \\
     qabbrev_tac ‘v = RNEW (r + LENGTH p) 0 X’ \\
     qexistsl_tac [‘v’, ‘I’] \\
     simp [closed_def, FV_I] \\
     rpt STRIP_TAC \\
    ‘LENGTH q <= LENGTH p’ by PROVE_TAC [IS_PREFIX_LENGTH] \\
     SYM_TAC >> MATCH_MP_TAC lemma14b \\
     MP_TAC (Q.SPECL [‘X’, ‘M’, ‘q’, ‘r’] FV_vsubterm_upperbound) >> rw [] \\
    ‘v NOTIN X UNION (RANK (r + LENGTH p))’ by PROVE_TAC [RNEW_thm] \\
     CCONTR_TAC >> fs [] \\
    ‘v IN X UNION RANK (r + LENGTH q)’ by PROVE_TAC [SUBSET_DEF] \\
     fs [IN_UNION] >- PROVE_TAC [] \\
     Suff ‘RANK (r + LENGTH q) SUBSET RANK (r + LENGTH p)’ >- ASM_SET_TAC [] \\
     simp [RANK_MONO])
 >> qabbrev_tac ‘M0 = principal_hnf M’
 >> ‘hnf M0’ by PROVE_TAC [hnf_principal_hnf']
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> Q_TAC (RNEWS_TAC (“vs :string list”, “r :num”, “n :num”)) ‘X’
 >> ‘DISJOINT (set vs) (FV M)’ by METIS_TAC [subterm_disjoint_lemma]
 (* applying HNF_TAC *)
 >> ‘DISJOINT (set vs) (FV M0)’ by METIS_TAC [subterm_disjoint_lemma']
 >> qabbrev_tac ‘M1 = principal_hnf (M0 @* MAP VAR vs)’
 >> Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                    “y :string”, “args :term list”)) ‘M1’
 >> ‘TAKE n vs = vs’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> qabbrev_tac ‘m = LENGTH args’
 (* using ‘subterm_width’ and applying subterm_width_thm *)
 >> qabbrev_tac ‘d = vsubterm_width M p’
 >> Know ‘m <= d’
 >- (Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘subterm_width M p’ \\
     simp [Abbr ‘d’] \\
     MP_TAC (Q.SPECL [‘X’, ‘M’, ‘p’, ‘r’] subterm_width_first) \\
     simp [])
 >> DISCH_TAC
 (* applying vsubterm_width_thm *)
 >> ‘!e. MEM e p ==> e < d’ by PROVE_TAC [vsubterm_width_thm]
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
 >> Know ‘solvable (M0 @* MAP VAR vs)’
 >- (MATCH_MP_TAC solvable_appstar' \\
     qexistsl_tac [‘X’, ‘M’, ‘r’, ‘n’] >> simp [])
 >> DISCH_TAC
 (* NOTE: Z contains ‘vs’ in addition to X and FV M *)
 >> qabbrev_tac ‘Z = X UNION FV M UNION set vs’
 >> ‘FINITE Z’ by (rw [Abbr ‘Z’] >> rw [])
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
 (* NOTE: new method avoiding calling ‘alloc’ directly *)
 >> Q_TAC (RNEWS_TAC (“zs :string list”, “r :num”, “n + d - m + 1”)) ‘X’
 >> ‘DISJOINT (set zs) (FV M)’ by PROVE_TAC [subterm_disjoint_lemma]
 >> qabbrev_tac ‘l = DROP n zs’
 >> ‘ALL_DISTINCT l’ by PROVE_TAC [ALL_DISTINCT_DROP]
 >> ‘LENGTH l = d - m + 1’ by simp [Abbr ‘l’]
 >> ‘l <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> ‘TAKE n zs = vs’ by simp [Abbr ‘zs’, Abbr ‘vs’, TAKE_RNEWS]
 >> Know ‘DISJOINT (set l) (set vs)’
 >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT zs’ MP_TAC \\
    ‘zs = TAKE n zs ++ DROP n zs’ by simp [TAKE_DROP] >> POP_ORW \\
     POP_ORW \\
     rw [ALL_DISTINCT_APPEND] \\
     rw [DISJOINT_ALT'])
 >> DISCH_TAC
 >> Know ‘set l SUBSET set zs’
 >- (‘zs = TAKE n zs ++ DROP n zs’ by simp [TAKE_DROP] >> POP_ORW \\
     simp [])
 >> DISCH_TAC
 >> Know ‘DISJOINT (set l) Z’
 >- (rw [Abbr ‘Z’, DISJOINT_UNION'] >|
     [ MATCH_MP_TAC DISJOINT_SUBSET' \\
       Q.EXISTS_TAC ‘set zs’ >> art [],
       MATCH_MP_TAC DISJOINT_SUBSET' \\
       Q.EXISTS_TAC ‘set zs’ >> art [] ])
 >> DISCH_TAC
 (* now recover the old definition of Y *)
 >> Know ‘DISJOINT (set l) (FV M1)’
 >- (MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘Z’ >> art [])
 >> ASM_REWRITE_TAC [FV_appstar, FV_thm]
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [DISJOINT_UNION']))
 >> Q.PAT_X_ASSUM ‘DISJOINT (set l) {y}’ (* ~MEM y l *)
      (STRIP_ASSUME_TAC o (SIMP_RULE (srw_ss()) [DISJOINT_ALT']))
 >> qabbrev_tac ‘as = FRONT l’
 >> ‘LENGTH as = d - m’ by rw [Abbr ‘as’, LENGTH_FRONT]
 >> qabbrev_tac ‘b = LAST l’
 >> Know ‘l = SNOC b as’
 >- ASM_SIMP_TAC std_ss [Abbr ‘as’, Abbr ‘b’, SNOC_LAST_FRONT]
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
 >- (simp [is_ready_alt, Abbr ‘pi’] \\
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
     fs [LIST_TO_SET_SNOC] >> T_TAC \\
     Suff ‘FV e SUBSET Y’ >- METIS_TAC [SUBSET_DEF] \\
     qunabbrev_tac ‘Y’ \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘BIGUNION (IMAGE FV (set args'))’ \\
     CONJ_TAC
     >- (rw [SUBSET_DEF, IN_BIGUNION_IMAGE] \\
         Q.EXISTS_TAC ‘e’ >> art []) \\
     rw [SUBSET_DEF, IN_BIGUNION_IMAGE, MEM_EL] \\
     rename1 ‘i < LENGTH args'’ \\
     Q.EXISTS_TAC ‘EL i args’ \\
     CONJ_TAC >- (Q.EXISTS_TAC ‘i’ >> art []) \\
     POP_ASSUM MP_TAC \\
     Suff ‘FV (EL i args') SUBSET FV (EL i args)’ >- METIS_TAC [SUBSET_DEF] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 (* extra goal: FV (apply pi M) SUBSET X UNION RANK (SUC r) *)
 >> CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘apply pi M == _’                K_TAC \\
     Q.PAT_X_ASSUM ‘principal_hnf (apply pi M) = _’ K_TAC \\
     Q.PAT_X_ASSUM ‘apply p3 (P @* args') == _’     K_TAC \\
     rpt (Q.PAT_X_ASSUM ‘Boehm_transform _’         K_TAC) \\
     POP_ASSUM MP_TAC (* solvable (apply pi M) *) \\
     simp [Boehm_apply_APPEND, Abbr ‘pi’, Abbr ‘p1’, Abbr ‘p2’, Abbr ‘p3’,
           Boehm_apply_MAP_rightctxt'] \\
     POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) (* l = SNOC b as *) \\
     DISCH_TAC \\
     reverse CONJ_TAC
     >- (Suff ‘set l SUBSET RANK (SUC r)’ >- SET_TAC [] \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘set zs’ >> art [] \\
         qunabbrev_tac ‘zs’ \\
         MATCH_MP_TAC RNEWS_SUBSET_RANK >> simp []) \\
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
 >> Q.X_GEN_TAC ‘q’
 >> STRIP_TAC (* push ‘q <<= p’ to assumptions *)
 (* LHS rewriting from M to M0 *)
 >> Know ‘vsubterm X (apply pi M) q r =
          vsubterm X (VAR b @* args' @* MAP VAR as) q r’
 >- (Q.PAT_X_ASSUM ‘_ = VAR b @* args' @* MAP VAR as’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     qabbrev_tac ‘t = apply pi M’ \\
     ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC vsubterm_of_principal_hnf >> art [])
 >> Rewr'
 (* stage cleanups *)
 >> Q.PAT_X_ASSUM ‘solvable (apply pi M)’          K_TAC
 >> Q.PAT_X_ASSUM ‘principal_hnf (apply pi M) = _’ K_TAC
 >> Q.PAT_X_ASSUM ‘apply pi M == _’                K_TAC
 >> Q.PAT_X_ASSUM ‘Boehm_transform pi’             K_TAC
 (* stage work, now ‘M’ is eliminated from both sides! *)
 >> Cases_on ‘q’ >- FULL_SIMP_TAC std_ss []
 >> Q.PAT_X_ASSUM ‘h::t <> []’ K_TAC
 >> Know ‘h < d’
 >- (FIRST_X_ASSUM MATCH_MP_TAC \\
     MATCH_MP_TAC IS_PREFIX_MEM \\
     Q.EXISTS_TAC ‘h::t’ >> simp [])
 >> DISCH_TAC
 >> REWRITE_TAC [GSYM appstar_APPEND]
 >> qabbrev_tac ‘args2 = args' ++ MAP VAR as’
 >> ‘LENGTH args2 = d’ by simp [Abbr ‘args2’]
 >> Know ‘vsubterm X (VAR b @* args2) (h::t) r =
          vsubterm X (EL h args2) t (SUC r)’
 >- (MP_TAC (Q.SPECL [‘X’, ‘b’, ‘args2’, ‘h’, ‘t’, ‘r’]
                     vsubterm_of_absfree_hnf_explicit) >> simp [])
 >> Rewr'
 >> reverse (Cases_on ‘h < m’)
 >- (Know ‘EL h args2 = EL (h - LENGTH args') (MAP VAR as)’
     >- (qunabbrev_tac ‘args2’ \\
         MATCH_MP_TAC EL_APPEND2 >> simp []) \\
     simp [EL_MAP] >> DISCH_THEN K_TAC \\
  (* 0                m      h    d
     |<---- args' ---->|<---as---->|
     |<---- args  ---->| n, n+1, n+2
   *)
     Q.PAT_X_ASSUM ‘vsubterm X M (h::t) r <> NONE’ MP_TAC \\
    ‘hnf_children M1 = args’ by simp [] \\
    ‘hnf_headvar M1 = y’ by simp [] \\
     Q.PAT_X_ASSUM ‘M0 = _’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘M1 = _’ (ASSUME_TAC o SYM) \\
     Q_TAC (unbeta_tac [vsubterm_def]) ‘vsubterm X M (h::t) r’ \\
     reverse (Cases_on ‘t = []’)
     >- (simp [vsubterm_var] \\
         SYM_TAC >> MATCH_MP_TAC lemma14b \\
         simp [FV_thm] \\
         MP_TAC (Q.SPECL [‘X’, ‘M’, ‘r’, ‘M0’, ‘n’, ‘vs’, ‘M1’]
                         subterm_headvar_lemma) >> simp [] \\
         Suff ‘RNEW (LENGTH t + SUC r - 1) (LAST t) X NOTIN
               X UNION RANK (SUC r)’ >- METIS_TAC [] \\
         qabbrev_tac ‘r' = LENGTH t + SUC r - 1’ \\
         MP_TAC (Q.SPECL [‘r'’, ‘LAST t’, ‘X’] RNEW_thm) >> simp [] \\
         Suff ‘RANK (SUC r) SUBSET RANK r'’ >- SET_TAC [] \\
         MATCH_MP_TAC RANK_MONO \\
        ‘0 < LENGTH t’ by simp [LENGTH_NON_NIL] \\
         simp [Abbr ‘r'’]) \\
     simp [] \\
     MP_TAC (Q.SPECL [‘X’, ‘M’, ‘r’, ‘M0’, ‘n’, ‘vs’, ‘M1’]
                     subterm_headvar_lemma') >> simp [] >> DISCH_TAC \\
     qabbrev_tac ‘i = n + SUC (h - m)’ \\
     Know ‘RNEWS r i X = TAKE i zs’
     >- (qunabbrev_tac ‘zs’ \\
         MATCH_MP_TAC RNEWS_TAKE >> simp [Abbr ‘i’]) >> Rewr' \\
     Know ‘LAST (TAKE i zs) = EL (i - 1) zs’
     >- (MATCH_MP_TAC (REWRITE_RULE [PRE_SUB1] LAST_TAKE_EL) \\
         simp [Abbr ‘i’]) >> Rewr' \\
     simp [Abbr ‘i’] \\
    ‘n + SUC (h - m) - 1 = n + (h - m)’ by simp [] >> POP_ORW \\
     Know ‘EL (h - m) as = EL (h - m) l’
     >- (qunabbrev_tac ‘as’ \\
         MATCH_MP_TAC EL_FRONT >> simp [NULL_EQ_NIL]) >> Rewr' \\
     Know ‘EL (n + (h - m)) zs = EL (h - m) l’
     >- simp [Abbr ‘l’, EL_DROP] >> Rewr' \\
     SYM_TAC >> MATCH_MP_TAC lemma14b \\
     Q.PAT_X_ASSUM ‘l = SNOC b as’ K_TAC \\
     simp [FV_thm] \\
     reverse (Q.PAT_X_ASSUM ‘y IN FV M UNION set vs’
                (STRIP_ASSUME_TAC o REWRITE_RULE [IN_UNION]))
     >- (CCONTR_TAC >> rfs [] \\
         Q.PAT_X_ASSUM ‘~MEM y l’ MP_TAC \\
         simp [MEM_EL] \\
         Q.EXISTS_TAC ‘h - m’ >> simp []) \\
     simp [Abbr ‘l’, EL_DROP] \\
     qabbrev_tac ‘i = h + n - m’ \\
    ‘n <= i /\ i < LENGTH zs’ by simp [Abbr ‘i’] \\
     Know ‘y IN X UNION RANK r’ >- PROVE_TAC [SUBSET_DEF] \\
     simp [IN_UNION] >> STRIP_TAC
     >- (Q.PAT_X_ASSUM ‘DISJOINT (set zs) X’ MP_TAC \\
         simp [DISJOINT_ALT'] \\
         CCONTR_TAC >> rfs [] \\
         Q.PAT_X_ASSUM ‘!x. x IN X ==> ~MEM x zs’ (MP_TAC o Q.SPEC ‘y’) \\
         simp [MEM_EL] \\
         Q.EXISTS_TAC ‘i’ >> simp []) \\
     MP_TAC (Q.SPECL [‘r’, ‘n + d - m + 1’, ‘X’]
                     DISJOINT_RNEWS_RANK') >> simp [] \\
     simp [DISJOINT_ALT'] \\
     DISCH_THEN (MP_TAC o Q.SPEC ‘y’) >> art [] \\
     DISCH_TAC \\
     CCONTR_TAC >> rfs [] \\
     Q.PAT_X_ASSUM ‘~MEM y zs’ MP_TAC \\
     simp [MEM_EL] \\
     Q.EXISTS_TAC ‘i’ >> simp [])
 (* eliminating ‘MAP VAR as’ *)
 >> Q.PAT_X_ASSUM ‘LENGTH args2 = d’ K_TAC
 >> qunabbrev_tac ‘args2’
 >> Know ‘EL h (args' ++ MAP VAR as) = EL h args'’
 >- (MATCH_MP_TAC EL_APPEND1 >> rw [])
 >> Rewr'
 (* stage work *)
 >> Q.PAT_X_ASSUM ‘vsubterm X M (h::t) r <> NONE’ MP_TAC
 >> Know ‘vsubterm X M (h::t) r = vsubterm X (EL h args) t (SUC r)’
 >- (‘hnf_children M1 = args’ by simp [] \\
     Q.PAT_X_ASSUM ‘M0 = _’ (ASSUME_TAC o SYM) \\
     Q.PAT_X_ASSUM ‘M1 = _’ (ASSUME_TAC o SYM) \\
     Q_TAC (unbeta_tac [vsubterm_def]) ‘vsubterm X M (h::t) r’)
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
 >> qabbrev_tac ‘N  = EL h args’
 >> qabbrev_tac ‘N' = EL h args'’
 (* eliminating N' *)
 >> ‘N' = [P/y] N’ by simp [EL_MAP, Abbr ‘m’, Abbr ‘N’, Abbr ‘N'’, Abbr ‘args'’]
 >> POP_ORW >> qunabbrev_tac ‘N'’
 (* cleanup args' *)
 >> Q.PAT_X_ASSUM ‘!i. i < m ==> FV (EL i args') SUBSET FV (EL i args)’ K_TAC
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
 >> DISCH_TAC (* vsubterm X N t (SUC r) <> NONE *)
 (* applying vsubterm_subst_permutator_cong *)
 >> MATCH_MP_TAC vsubterm_subst_permutator_cong'
 >> Q.EXISTS_TAC ‘d’
 >> simp [Abbr ‘P’]
 >> CONJ_TAC
 >- (qunabbrev_tac ‘N’ >> MATCH_MP_TAC subterm_induction_lemma' \\
     qexistsl_tac [‘M’, ‘M0’, ‘n’, ‘m’, ‘vs’, ‘M1’] >> simp [])
 (* stage work *)
 >> Know ‘vsubterm_width M (h::t) <= d’
 >- (qunabbrev_tac ‘d’ \\
     MATCH_MP_TAC vsubterm_width_inclusive \\
     Q.EXISTS_TAC ‘p’ >> simp [])
 >> Suff ‘vsubterm_width M (h::t) <= d <=>
          h < d /\ m <= d /\ vsubterm_width (EL h args) t <= d’ >- simp []
 >> MATCH_MP_TAC vsubterm_width_induction_lemma'
 >> qexistsl_tac [‘X’, ‘r’, ‘M0’, ‘n’, ‘vs’, ‘M1’] >> simp []
QED

(* END *)
val _ = html_theory "separability";

(* References:

 [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
     College Publications, London (1984).
 *)
