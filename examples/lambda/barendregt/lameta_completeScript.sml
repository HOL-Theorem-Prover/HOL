(* ========================================================================== *)
(* FILE    : lameta_completeScript.sml                                        *)
(* TITLE   : Completeness of (Untyped) Lambda-Calculus [1, Chapter 10.4]      *)
(*                                                                            *)
(* AUTHORS : 2024 - 2025 The Australian National University (Chun Tian)       *)
(* ========================================================================== *)

Theory lameta_complete
Ancestors
  combin option arithmetic pred_set list rich_list llist ltree relation iterate
  topology nomset basic_swap term appFOLDL chap2 chap3 chap4 horeduction
  solvable takahashiS3 head_reduction standardisation boehm separability
Libs
  hurdUtils tautLib numLib listLib NEWLib reductionEval head_reductionLib
  monadsyntax

(* enable basic monad support *)
val _ = enable_monadsyntax ();
val _ = enable_monad "option";

local open set_relationTheory in
   val rel_to_reln_IS_UNCURRY = rel_to_reln_IS_UNCURRY;
end

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

val PRINT_TAC = goalStack.note_tac

(* Disable some conflicting overloads from labelledTermsTheory *)
Overload FV  = “supp term_pmact”
Overload VAR = “term$VAR”

val _ = temp_clear_overloads_on "fEL"; (* use old EL syntax *)

(*---------------------------------------------------------------------------*
 *  subtree_equiv_lemma (by vsubterm_equivalent_lemma)
 *---------------------------------------------------------------------------*)

Theorem subtree_equiv_lemma :
    !X Ms p r.
       FINITE X /\ p <> [] /\ 0 < r /\
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
 >> Know ‘EVERY solvable Ms’
 >- (POP_ASSUM MP_TAC >> rw [EVERY_MEM] \\
     CCONTR_TAC \\
     rename1 ‘MEM M Ms’ \\
     Q.PAT_X_ASSUM ‘!M. MEM M Ms ==> subterm X M p r <> NONE’
       (MP_TAC o Q.SPEC ‘M’) >> art [] \\
     MATCH_MP_TAC subterm_of_unsolvables >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘pi = Boehm_construction X Ms [p]’
 >> MP_TAC (Q.SPECL [‘X’, ‘Ms’, ‘p’, ‘r’, ‘pi’] vsubterm_equivalent_lemma)
 >> simp []
 >> STRIP_TAC
 >> Q.EXISTS_TAC ‘pi’
 >> CONJ_TAC >- simp [Abbr ‘pi’, Boehm_construction_transform]
 >> CONJ_TAC (* EVERY is_ready' _ *)
 >- (rw [EVERY_MEM, MEM_MAP] >> simp [])
 >> CONJ_ASM1_TAC (* EVERY (\M. FV M SUBSET X UNION RANK r) _ *)
 >- (rw [EVERY_MEM, MEM_MAP] \\
     qunabbrev_tac ‘pi’ \\
     irule FV_apply_Boehm_construction >> art [] \\
     Q.EXISTS_TAC ‘Ms’ >> simp [])
 >> CONJ_ASM1_TAC
 >- (POP_ASSUM MP_TAC >> rw [EVERY_MEM, MEM_MAP] \\
     rename1 ‘MEM M Ms’ \\
     Know ‘p IN ltree_paths (BT' X (apply pi M) r) <=>
           subterm X (apply pi M) p r <> NONE’
     >- (MATCH_MP_TAC BT_ltree_paths_thm >> art [] \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         Q.EXISTS_TAC ‘M’ >> art []) >> Rewr' \\
     FIRST_X_ASSUM MATCH_MP_TAC >> simp [] \\
     Q.PAT_X_ASSUM ‘EVERY (\M. subterm X M p r <> NONE) Ms’ MP_TAC \\
     rw [EVERY_MEM, MEM_MAP])
 >> Know ‘EVERY (\M. FV M SUBSET X UNION RANK r) Ms’
 >- (rw [EVERY_MEM] \\
     Q.PAT_X_ASSUM
       ‘BIGUNION (IMAGE FV (set Ms)) SUBSET X UNION RANK r’ MP_TAC \\
     rw [SUBSET_DEF, IN_BIGUNION_IMAGE] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘M’ >> art [])
 >> DISCH_TAC
 >> CONJ_TAC
 >- (rpt STRIP_TAC \\
     Know ‘subterm X M q r = vsubterm X M q r’
     >- (SYM_TAC >> MATCH_MP_TAC vsubterm_alt_subterm' >> art [] \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC ltree_paths_inclusive \\
             Q.EXISTS_TAC ‘p’ >> art [] \\
             Q.PAT_X_ASSUM
               ‘EVERY (\M. p IN ltree_paths (BT' X M r)) Ms’ MP_TAC \\
             rw [EVERY_MEM]) \\
         Q.PAT_X_ASSUM ‘EVERY (\M. FV M SUBSET X UNION RANK r) Ms’ MP_TAC \\
         rw [EVERY_MEM]) >> DISCH_TAC \\
     simp [] \\
     Know ‘subterm X (apply pi M) q r = vsubterm X (apply pi M) q r’
     >- (SYM_TAC >> MATCH_MP_TAC vsubterm_alt_subterm' >> art [] \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC ltree_paths_inclusive \\
             Q.EXISTS_TAC ‘p’ >> art [] \\
             Q.PAT_X_ASSUM
              ‘EVERY (\M. p IN ltree_paths (BT' X M r)) (apply pi Ms)’ MP_TAC \\
             rw [EVERY_MEM, MEM_MAP] \\
             POP_ASSUM MATCH_MP_TAC \\
             Q.EXISTS_TAC ‘M’ >> art []) \\
         Q.PAT_X_ASSUM
           ‘EVERY (\M. FV M SUBSET X UNION RANK r) (apply pi Ms)’ MP_TAC \\
         rw [EVERY_MEM, MEM_MAP] \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         Q.EXISTS_TAC ‘M’ >> art []) >> Rewr' \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [] \\
     POP_ASSUM (REWRITE_TAC o wrap o SYM) \\
     Suff ‘subterm X M p r <> NONE’ >- METIS_TAC [subterm_is_none_inclusive] \\
     Q.PAT_X_ASSUM ‘EVERY (\M. subterm X M p r <> NONE) Ms’ MP_TAC \\
     rw [EVERY_MEM])
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘EVERY (\M. FV M SUBSET X UNION RANK r) Ms’ MP_TAC
 >> rw [EVERY_MEM]
 >> Q.PAT_X_ASSUM ‘EVERY (\M. subterm X M p r <> NONE) Ms’ MP_TAC
 >> rw [EVERY_MEM]
 (* applying subtree_equiv_alt_equivalent_vsubterm *)
 >> Know ‘subtree_equiv X M N q r <=>
          equivalent (vsubterm' X M q r) (vsubterm' X N q r)’
 >- (MATCH_MP_TAC subtree_equiv_alt_equivalent_vsubterm >> simp [] \\
     METIS_TAC [subterm_is_none_inclusive])
 >> Rewr'
 >> Know ‘subtree_equiv X (apply pi M) (apply pi N) q r <=>
          equivalent (vsubterm' X (apply pi M) q r)
                     (vsubterm' X (apply pi N) q r)’
 >- (MATCH_MP_TAC subtree_equiv_alt_equivalent_vsubterm >> simp [] \\
     Q.PAT_X_ASSUM
       ‘EVERY (\M. FV M SUBSET X UNION RANK r) (apply pi Ms)’ MP_TAC \\
     simp [EVERY_MEM, MEM_MAP] >> DISCH_TAC \\
     CONJ_TAC >- (POP_ASSUM MATCH_MP_TAC \\
                  Q.EXISTS_TAC ‘M’ >> art []) \\
     CONJ_TAC >- (POP_ASSUM MATCH_MP_TAC \\
                  Q.EXISTS_TAC ‘N’ >> art []) \\
     Suff ‘subterm X (apply pi M) p r <> NONE /\
           subterm X (apply pi N) p r <> NONE’
     >- METIS_TAC [subterm_is_none_inclusive] \\
     simp [])
 >> Rewr'
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> Know ‘vsubterm X M q r = subterm X M q r’
 >- (MATCH_MP_TAC vsubterm_alt_subterm' >> art [] \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC ltree_paths_inclusive \\
         Q.EXISTS_TAC ‘p’ >> art [] \\
         Q.PAT_X_ASSUM ‘EVERY (\M. p IN ltree_paths (BT' X M r)) Ms’ MP_TAC \\
         rw [EVERY_MEM]) \\
     simp [])
 >> Rewr'
 >> Know ‘vsubterm X N q r = subterm X N q r’
 >- (MATCH_MP_TAC vsubterm_alt_subterm' >> art [] \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC ltree_paths_inclusive \\
         Q.EXISTS_TAC ‘p’ >> art [] \\
         Q.PAT_X_ASSUM ‘EVERY (\M. p IN ltree_paths (BT' X M r)) Ms’ MP_TAC \\
         rw [EVERY_MEM]) \\
     simp [])
 >> Rewr'
 >> Suff ‘subterm X M p r <> NONE /\ subterm X N p r <> NONE’
 >- METIS_TAC [subterm_is_none_inclusive]
 >> simp []
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

val _ = html_theory "lameta_complete";

(* References:

 [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
     College Publications, London (1984).
 *)
