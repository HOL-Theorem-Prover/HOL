(*---------------------------------------------------------------------------*
 * solvableScript.sml (or chap8_3): solvable terms (and principle hnfs)      *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;

(* core theories *)
open arithmeticTheory pred_setTheory listTheory rich_listTheory sortingTheory
     finite_mapTheory pathTheory relationTheory hurdUtils;

(* lambda theories *)
open binderLib nomsetTheory termTheory appFOLDLTheory chap2Theory chap3Theory
     reductionEval standardisationTheory head_reductionTheory horeductionTheory;

val _ = new_theory "solvable";

(* |- !M. FV M = {} ==> (solvable M <=> ?Ns. M @* Ns == I) *)
Theorem solvable_alt_closed'[local] =
    REWRITE_RULE [closed_def] solvable_alt_closed

(* 8.3.2 Examples of solvable terms [1, p.171] *)
Theorem solvable_K :
    solvable K
Proof
    rw [solvable_alt_closed']
 >> Q.EXISTS_TAC ‘[I; I]’
 >> rw [lameq_K]
QED

Theorem solvable_xIO :
    solvable (VAR x @@ I @@ Omega)
Proof
    Q.ABBREV_TAC ‘M = VAR x @@ I @@ Omega’
 >> ‘FV M = {x}’ by rw [Abbr ‘M’]
 >> ‘closures M = {LAM x M}’ by PROVE_TAC [closures_of_open_sing]
 >> rw [solvable_def]
 >> Q.EXISTS_TAC ‘[K]’ >> simp []
 >> ASM_SIMP_TAC (betafy (srw_ss())) [Abbr ‘M’, lameq_K]
 >> KILL_TAC
 >> rw [SUB_THM, lemma14b]
QED

val _ = reveal "Y"; (* from chap2Theory *)
Theorem solvable_Y :
    solvable Y
Proof
    rw [solvable_alt_closed']
 >> Q.EXISTS_TAC ‘[K @@ I]’ >> simp []
 >> ASM_SIMP_TAC (betafy (srw_ss())) [YYf, Once YffYf, lameq_K]
QED
val _ = hide "Y";

Theorem closure_VAR[simp] :
    closure (VAR x) = I
Proof
    Know ‘closure (VAR x) = LAM x (VAR x)’
 >- (MATCH_MP_TAC closure_open_sing >> rw [])
 >> Rewr'
 >> REWRITE_TAC [Q.SPEC ‘x’ I_thm]
QED

Theorem closures_imp_closed :
    !M N. N IN closures M ==> closed N
Proof
    rw [closures_def, closed_def]
 >> simp [FV_LAMl]
QED

(* |- !M N. N IN closures M ==> FV N = {} *)
Theorem FV_closures = REWRITE_RULE [closed_def] closures_imp_closed

Theorem FV_closure[simp] :
    FV (closure M) = {}
Proof
    MATCH_MP_TAC FV_closures
 >> Q.EXISTS_TAC ‘M’
 >> rw [closure_in_closures]
QED

(* alternative definition of solvable terms involving all closed terms *)
Theorem solvable_alt_closed_every :
    !M. closed M ==> (solvable M <=> ?Ns. M @* Ns == I /\ EVERY closed Ns)
Proof
    rw [solvable_alt_closed, closed_def]
 >> reverse EQ_TAC
 >- (STRIP_TAC >> Q.EXISTS_TAC ‘Ns’ >> rw [])
 (* stage work *)
 >> STRIP_TAC
 (* collect all free variables in Ns into vs *)
 >> Q.ABBREV_TAC ‘vs = BIGUNION (IMAGE FV (set Ns))’
 >> ‘FINITE vs’
      by (Q.UNABBREV_TAC ‘vs’ >> MATCH_MP_TAC FINITE_BIGUNION \\
          rw [IMAGE_FINITE] >> rw [FINITE_FV])
 >> ‘!N. MEM N Ns ==> FV N SUBSET vs’
      by (rw [Abbr ‘vs’, SUBSET_DEF, IN_BIGUNION_IMAGE] \\
          Q.EXISTS_TAC ‘N’ >> art [])
 (* construct the variable substitution *)
 >> Q.ABBREV_TAC ‘fm = FUN_FMAP (\x. I) vs’
 >> Q.EXISTS_TAC ‘MAP (ssub fm) Ns’
 >> reverse CONJ_TAC (* EVERY closed (MAP ($' fm) Ns) *)
 >- (rw [EVERY_MAP, EVERY_EL, closed_def] \\
     Q.ABBREV_TAC ‘N = EL n Ns’ \\
    ‘MEM N Ns’ by PROVE_TAC [MEM_EL] \\
    ‘{} = FV N DIFF vs’ by ASM_SET_TAC [] >> POP_ORW \\
    ‘vs = FDOM fm’ by rw [Abbr ‘fm’] >> POP_ORW \\
     MATCH_MP_TAC FV_ssub \\
     rw [Abbr ‘fm’, FUN_FMAP_DEF, FAPPLY_FUPDATE_THM])
 (* stage work *)
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘fm ' (M @* Ns)’
 >> reverse CONJ_TAC
 >- (ONCE_REWRITE_TAC [SYM ssub_I] \\
     MATCH_MP_TAC lameq_ssub_cong \\
     rw [Abbr ‘fm’, FUN_FMAP_DEF, FAPPLY_FUPDATE_THM, closed_def])
 >> rw [ssub_appstar]
 >> Suff ‘fm ' M = M’ >- rw []
 >> MATCH_MP_TAC ssub_value >> art []
QED

(* cf. solvable_def, adding ‘EVERY closed Ns’ in RHS *)
Theorem solvable_alt :
    !M. solvable M <=> ?M' Ns. M' IN closures M /\ M' @* Ns == I /\ EVERY closed Ns
Proof
    Q.X_GEN_TAC ‘M’
 >> reverse EQ_TAC
 >- (rw [solvable_def] \\
     qexistsl_tac [‘M'’, ‘Ns’] >> art [])
 >> rw [solvable_def]
 >> Q.EXISTS_TAC ‘M'’ >> art []
 >> ‘closed M'’ by PROVE_TAC [closures_imp_closed]
 >> Suff ‘solvable M'’ >- rw [solvable_alt_closed_every]
 >> rw [solvable_alt_closed]
 >> Q.EXISTS_TAC ‘Ns’ >> art []
QED

Definition closed_substitution_instances_def :
    closed_substitution_instances M =
       {fm ' M | fm | FDOM fm = FV M /\ !v. v IN FDOM fm ==> closed (fm ' v)}
End

Theorem solvable_alt_closed_substitution_instance_lemma[local] :
    !Ns. FV M = set vs /\ ALL_DISTINCT vs /\ LAMl vs M @* Ns == I /\
         LENGTH vs <= LENGTH Ns /\ EVERY closed Ns
     ==> ?M' Ns'. M' IN closed_substitution_instances M /\
                  M' @* Ns' == I /\ EVERY closed Ns'
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘n = LENGTH vs’
 >> Q.ABBREV_TAC ‘m = LENGTH Ns’
 >> Q.PAT_X_ASSUM ‘LAMl vs M @* Ns == I’ MP_TAC
 >> Q.ABBREV_TAC ‘Ns0 = TAKE n Ns’
 >> ‘LENGTH Ns0 = n’ by rw [Abbr ‘Ns0’, LENGTH_TAKE]
 >> Q.ABBREV_TAC ‘Ns1 = DROP n Ns’
 >> ‘Ns = Ns0 ++ Ns1’ by rw [Abbr ‘Ns0’, Abbr ‘Ns1’, TAKE_DROP]
 >> ‘EVERY closed Ns0 /\ EVERY closed Ns1’
      by FULL_SIMP_TAC std_ss [EVERY_APPEND]
 >> Q.PAT_X_ASSUM ‘Ns = Ns0 ++ Ns1’ (ONCE_REWRITE_TAC o wrap)
 >> REWRITE_TAC [appstar_APPEND]
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘fm = FEMPTY |++ ZIP (vs,Ns0)’
 >> Know ‘LAMl vs M @* Ns0 == fm ' M’
 >- (Q.UNABBREV_TAC ‘fm’ \\
     MATCH_MP_TAC lameq_LAMl_appstar_ssub_closed >> rw [])
 >> DISCH_TAC
 >> ‘LAMl vs M @* Ns0 @* Ns1 == fm ' M @* Ns1’ by PROVE_TAC [lameq_appstar_cong]
 >> ‘fm ' M @* Ns1 == I’ by PROVE_TAC [lameq_TRANS, lameq_SYM]
 >> qexistsl_tac [‘fm ' M’, ‘Ns1’]
 >> rw [closed_substitution_instances_def]
 >> Q.EXISTS_TAC ‘fm’ >> rw [Abbr ‘fm’]
 >- rw [MEM_MAP, MEM_ZIP, FDOM_FUPDATE_LIST, MAP_ZIP]
 >> gs [MEM_MAP, MEM_ZIP, FDOM_FUPDATE_LIST]
 >> Suff ‘(FEMPTY |++ ZIP (vs,Ns0)) ' (EL n vs) = EL n Ns0’
 >- (Rewr' \\
     Q.PAT_X_ASSUM ‘EVERY closed Ns0’ MP_TAC >> rw [EVERY_MEM] \\
     POP_ASSUM MATCH_MP_TAC >> rw [MEM_EL] \\
     Q.EXISTS_TAC ‘n’ >> rw [])
 >> MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM
 >> Q.EXISTS_TAC ‘n’
 >> rw [LENGTH_ZIP, EL_MAP, MAP_ZIP, EL_ZIP]
 >> rename1 ‘j < LENGTH Ns0’
 >> ‘j <> n’ by rw []
 >> METIS_TAC [EL_ALL_DISTINCT_EL_EQ]
QED

(* Lemma 8.3.3 (i) *)
Theorem solvable_alt_closed_substitution_instance :
    !M. solvable M <=> ?M' Ns. M' IN closed_substitution_instances M /\
                               M' @* Ns == I /\ EVERY closed Ns
Proof
    Q.X_GEN_TAC ‘M’
 >> EQ_TAC
 >- (rw [solvable_alt, closures_def] \\
     Q.ABBREV_TAC ‘n = LENGTH vs’ \\
     Q.ABBREV_TAC ‘m = LENGTH Ns’ \\
     Cases_on ‘n <= m’
     >- (MATCH_MP_TAC solvable_alt_closed_substitution_instance_lemma \\
         Q.EXISTS_TAC ‘Ns’ >> rw []) \\
     Q.ABBREV_TAC ‘Is = GENLIST (\i. I) (n - m)’ \\
    ‘(LAMl vs M @* Ns) @* Is == I @* Is’ by PROVE_TAC [lameq_appstar_cong] \\
    ‘I @* Is == I’ by PROVE_TAC [I_appstar] \\
     FULL_SIMP_TAC std_ss [GSYM appstar_APPEND] \\
     Q.ABBREV_TAC ‘Ns' = Ns ++ Is’ \\
    ‘LENGTH Ns' = n’ by (rw [Abbr ‘Ns'’, Abbr ‘Is’]) \\
    ‘LAMl vs M @* Ns' == I’ by PROVE_TAC [lameq_TRANS] \\
     Know ‘EVERY closed Ns'’
     >- (rw [EVERY_APPEND, Abbr ‘Ns'’] \\
         rw [EVERY_MEM, Abbr ‘Is’, closed_def, MEM_GENLIST] \\
         REWRITE_TAC [FV_I]) >> DISCH_TAC \\
     MATCH_MP_TAC solvable_alt_closed_substitution_instance_lemma \\
     Q.EXISTS_TAC ‘Ns'’ >> rw [])
 (* stage work *)
 >> rw [solvable_def, closed_substitution_instances_def]
 >> Q.ABBREV_TAC ‘vss = FDOM fm’
 >> ‘FINITE vss’ by rw [FDOM_FINITE, Abbr ‘vss’]
 (* preparing for lameq_LAMl_appstar_ssub_closed *)
 >> Q.ABBREV_TAC ‘vs = SET_TO_LIST vss’
 >> ‘ALL_DISTINCT vs’ by PROVE_TAC [Abbr ‘vs’, ALL_DISTINCT_SET_TO_LIST]
 >> Q.ABBREV_TAC ‘Ps = MAP (\v. fm ' v) vs’
 >> ‘LENGTH Ps = LENGTH vs’ by rw [Abbr ‘Ps’]
 (* stage work *)
 >> Q.PAT_X_ASSUM ‘fm ' M @* Ns == I’ MP_TAC
 >> Know ‘fm = (FEMPTY |++ ZIP (vs,Ps))’
 >- (rw [fmap_EXT, FDOM_FUPDATE_LIST, MAP_ZIP]
     >- rw [Abbr ‘vs’, SET_TO_LIST_INV] \\
    ‘MEM x vs’ by rw [Abbr ‘vs’] \\
     Cases_on ‘INDEX_OF x vs’ >- fs [INDEX_OF_eq_NONE] \\
     rename1 ‘INDEX_OF x vs = SOME n’ \\
     fs [INDEX_OF_eq_SOME] \\
     Q.PAT_X_ASSUM ‘EL n vs = x’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.ABBREV_TAC ‘L = ZIP (vs,Ps)’ \\
    ‘LENGTH L = LENGTH vs’ by rw [Abbr ‘L’, LENGTH_ZIP] \\
     Know ‘(FEMPTY |++ L) ' (EL n vs) = EL n Ps’
     >- (MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM \\
         Q.EXISTS_TAC ‘n’ >> rw [EL_MAP, Abbr ‘L’, EL_ZIP] \\
        ‘m <> n’ by rw [] \\
         METIS_TAC [EL_ALL_DISTINCT_EL_EQ]) >> Rewr' \\
     rw [Abbr ‘Ps’, EL_MAP])
 >> Rewr'
 >> DISCH_TAC
 >> Know ‘LAMl vs M @* Ps == (FEMPTY |++ ZIP (vs,Ps)) ' M’
 >- (MATCH_MP_TAC lameq_LAMl_appstar_ssub_closed >> art [] \\
     rw [Abbr ‘Ps’, EVERY_MEM, MEM_MAP] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     POP_ASSUM MP_TAC \\
     rw [Abbr ‘vs’, MEM_SET_TO_LIST])
 >> DISCH_TAC
 >> Know ‘LAMl vs M @* Ps @* Ns == (FEMPTY |++ ZIP (vs,Ps)) ' M @* Ns’
 >- (MATCH_MP_TAC lameq_appstar_cong >> art [])
 >> DISCH_TAC
 >> ‘LAMl vs M @* Ps @* Ns == I’ by PROVE_TAC [lameq_TRANS]
 >> qexistsl_tac [‘LAMl vs M’, ‘Ps ++ Ns’]
 >> rw [appstar_APPEND, closures_def]
 >> Q.EXISTS_TAC ‘vs’ >> art []
 >> rw [Abbr ‘vs’, SET_TO_LIST_INV]
QED

(* NOTE: this proof needs sortingTheory (PERM) *)
Theorem solvable_alt_universal_lemma[local] :
    !Ns. ALL_DISTINCT vs /\ ALL_DISTINCT vs' /\
         set vs = FV M /\ set vs' = FV M /\
         LENGTH vs <= LENGTH Ns /\ EVERY closed Ns /\
         LAMl vs M @* Ns == I ==> ?Ns'. LAMl vs' M @* Ns' == I
Proof
    rpt STRIP_TAC
 >> Know ‘PERM vs vs'’
 >- (‘set vs = set vs'’ by PROVE_TAC [] \\
     ‘PERM vs  (SET_TO_LIST (set vs)) /\
      PERM vs' (SET_TO_LIST (set vs'))’
        by PROVE_TAC [ALL_DISTINCT_PERM_LIST_TO_SET_TO_LIST] \\
     PROVE_TAC [PERM_TRANS, PERM_SYM])
 (* asserts an bijection ‘f’ mapping vs to vs' *)
 >> DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERM_BIJ))
 >> Q.ABBREV_TAC ‘n = LENGTH vs’
 >> Q.ABBREV_TAC ‘m = LENGTH Ns’
 >> Q.PAT_X_ASSUM ‘LAMl vs M @* Ns == I’ MP_TAC
 >> Q.ABBREV_TAC ‘Ns0 = TAKE n Ns’
 >> ‘LENGTH Ns0 = n’ by rw [Abbr ‘Ns0’, LENGTH_TAKE]
 >> Q.ABBREV_TAC ‘Ns1 = DROP n Ns’
 >> ‘Ns = Ns0 ++ Ns1’ by rw [Abbr ‘Ns0’, Abbr ‘Ns1’, TAKE_DROP]
 >> ‘EVERY closed Ns0 /\ EVERY closed Ns1’
      by FULL_SIMP_TAC std_ss [EVERY_APPEND]
 >> Q.PAT_X_ASSUM ‘Ns = Ns0 ++ Ns1’ (ONCE_REWRITE_TAC o wrap)
 >> REWRITE_TAC [appstar_APPEND]
 >> DISCH_TAC
 (* construct the 1st finite map *)
 >> Q.ABBREV_TAC ‘fm = FEMPTY |++ ZIP (vs,Ns0)’
 >> Know ‘LAMl vs M @* Ns0 == fm ' M’
 >- (Q.UNABBREV_TAC ‘fm’ \\
     MATCH_MP_TAC lameq_LAMl_appstar_ssub_closed >> rw [])
 >> DISCH_TAC
 >> ‘LAMl vs M @* Ns0 @* Ns1 == fm ' M @* Ns1’ by PROVE_TAC [lameq_appstar_cong]
 >> ‘fm ' M @* Ns1 == I’ by PROVE_TAC [lameq_TRANS, lameq_SYM]
 (* Ns0' is the permuted version of Ns0 *)
 >> Q.ABBREV_TAC ‘Ns0' = GENLIST (\i. EL (f i) Ns0) n’
 >> ‘LENGTH Ns0' = n’ by rw [Abbr ‘Ns0'’, LENGTH_GENLIST]
 >> Know ‘EVERY closed Ns0'’
 >- (Q.PAT_X_ASSUM ‘EVERY closed Ns0’ MP_TAC \\
     rw [Abbr ‘Ns0'’, EVERY_MEM, MEM_GENLIST, LENGTH_GENLIST] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> rw [MEM_EL] \\
     Q.ABBREV_TAC ‘n = LENGTH Ns0’ \\
     Q.EXISTS_TAC ‘f i’ >> art [] \\
     Q.PAT_X_ASSUM ‘f PERMUTES count n’ MP_TAC \\
     rw [BIJ_ALT, IN_FUNSET])
 >> DISCH_TAC
 (* stage work *)
 >> Q.EXISTS_TAC ‘Ns0' ++ Ns1’
 >> REWRITE_TAC [appstar_APPEND]
 (* construct the 2nd finite map *)
 >> Q.ABBREV_TAC ‘fm' = FEMPTY |++ ZIP (vs',Ns0')’
 >> Know ‘LAMl vs' M @* Ns0' == fm' ' M’
 >- (Q.UNABBREV_TAC ‘fm'’ \\
     MATCH_MP_TAC lameq_LAMl_appstar_ssub_closed >> rw [])
 >> DISCH_TAC
 >> ‘LAMl vs' M @* Ns0' @* Ns1 == fm' ' M @* Ns1’ by PROVE_TAC [lameq_appstar_cong]
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘fm' ' M @* Ns1’ >> art []
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘fm ' M @* Ns1’ >> art []
 >> Suff ‘fm = fm'’ >- rw []
 (* cleanup uncessary assumptions *)
 >> Q.PAT_X_ASSUM ‘LAMl vs M @* Ns0 @* Ns1 == I’                K_TAC
 >> Q.PAT_X_ASSUM ‘LAMl vs M @* Ns0 == fm ' M’                  K_TAC
 >> Q.PAT_X_ASSUM ‘LAMl vs M @* Ns0 @* Ns1 == fm ' M @* Ns1’    K_TAC
 >> Q.PAT_X_ASSUM ‘fm ' M @* Ns1 == I’                          K_TAC
 >> Q.PAT_X_ASSUM ‘LAMl vs' M @* Ns0' == fm' ' M’               K_TAC
 >> Q.PAT_X_ASSUM ‘LAMl vs' M @* Ns0' @* Ns1 == fm' ' M @* Ns1’ K_TAC
 (* g is bijection inversion of f *)
 >> MP_TAC (Q.ISPECL [‘f :num -> num’, ‘count n’, ‘count n’] BIJ_INV)
 >> RW_TAC std_ss [IN_COUNT]
 >> ‘LENGTH vs = LENGTH Ns0’ by PROVE_TAC []
 (* final goal: fm = fm' *)
 >> rw [Abbr ‘fm’, Abbr ‘fm'’, fmap_EXT, FDOM_FUPDATE_LIST, MAP_ZIP]
 >> ‘MEM x vs’ by PROVE_TAC []
 >> Cases_on ‘INDEX_OF x vs’ >- fs [INDEX_OF_eq_NONE]
 >> rename1 ‘INDEX_OF x vs = SOME n’
 >> fs [INDEX_OF_eq_SOME]
 >> Q.PAT_X_ASSUM ‘EL n vs = x’ (ONCE_REWRITE_TAC o wrap o SYM)
 (* applying FUPDATE_LIST_APPLY_MEM *)
 >> Know ‘(FEMPTY |++ ZIP (vs,Ns0)) ' (EL n vs) = EL n Ns0’
 >- (MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM \\
     Q.EXISTS_TAC ‘n’ \\
     rw [LENGTH_ZIP, EL_MAP, MAP_ZIP, EL_ZIP] \\
     rename1 ‘n < k’ >> ‘k <> n’ by rw [] \\
     METIS_TAC [EL_ALL_DISTINCT_EL_EQ])
 >> Rewr'
 >> Q.ABBREV_TAC ‘n0 = LENGTH Ns0'’
 >> Know ‘g n < n0’
 >- (Q.PAT_X_ASSUM ‘g PERMUTES count n0’ MP_TAC \\
     rw [BIJ_ALT, IN_FUNSET])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘vs' = GENLIST (\i. EL (f i) vs) n0’
 >> ‘LENGTH vs' = LENGTH Ns0'’ by rw [Abbr ‘vs'’, LENGTH_GENLIST]
 >> ‘EL n vs = EL (g n) vs'’
       by (rw [Abbr ‘vs'’, EL_GENLIST]) >> POP_ORW
 >> Q.ABBREV_TAC ‘i = g n’
 >> Know ‘(FEMPTY |++ ZIP (vs',Ns0')) ' (EL i vs') = EL i Ns0'’
 >- (MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM \\
     Q.EXISTS_TAC ‘i’ \\
     rw [LENGTH_ZIP, EL_MAP, MAP_ZIP, EL_ZIP] \\
     rename1 ‘i < j’ >> ‘j <> i’ by rw [] \\
     METIS_TAC [EL_ALL_DISTINCT_EL_EQ])
 >> Rewr'
 >> rw [Abbr ‘Ns0'’, Abbr ‘i’, EL_GENLIST]
QED

(* cf. solvable_def, with the existential quantifier "upgraded" to universal

   NOTE: This is actually 8.3.5 [1, p.172] showing the definition of solvability of
         open terms is independent of the order of the variables in its closure.
 *)
Theorem solvable_alt_universal :
    !M. solvable M <=> !M'. M' IN closures M ==> ?Ns. M' @* Ns == I /\ EVERY closed Ns
Proof
    Q.X_GEN_TAC ‘M’
 >> reverse EQ_TAC
 >- (rw [solvable_def] >> Q.EXISTS_TAC ‘closure M’ \\
     POP_ASSUM (MP_TAC o (Q.SPEC ‘closure M’)) >> rw [closure_in_closures] \\
     Q.EXISTS_TAC ‘Ns’ >> art [])
 (* stage work *)
 >> STRIP_TAC
 >> Q.X_GEN_TAC ‘M0’ >> DISCH_TAC
 >> ‘closed M0’ by PROVE_TAC [closures_imp_closed]
 >> Suff ‘solvable M0’ >- PROVE_TAC [solvable_alt_closed_every]
 >> rw [solvable_alt_closed]
 (* applying solvable_alt *)
 >> fs [solvable_alt, closures_def]
 >> Q.ABBREV_TAC ‘n = LENGTH vs’
 >> Q.ABBREV_TAC ‘m = LENGTH Ns’
 >> Cases_on ‘n <= m’
 >- (MATCH_MP_TAC solvable_alt_universal_lemma \\
     Q.EXISTS_TAC ‘Ns’ >> rw [])
 (* additional steps when ‘m < n’ *)
 >> Q.ABBREV_TAC ‘Is = GENLIST (\i. I) (n - m)’
 >> ‘(LAMl vs M @* Ns) @* Is == I @* Is’ by PROVE_TAC [lameq_appstar_cong]
 >> ‘I @* Is == I’ by METIS_TAC [I_appstar]
 >> ‘LAMl vs M @* (Ns ++ Is) == I @* Is’ by rw [appstar_APPEND]
 >> Q.ABBREV_TAC ‘Ns' = Ns ++ Is’
 >> ‘LENGTH Ns' = n’ by (rw [Abbr ‘Ns'’, Abbr ‘Is’])
 >> ‘LAMl vs M @* Ns' == I’ by PROVE_TAC [lameq_TRANS]
 >> Know ‘EVERY closed Ns'’
 >- (rw [EVERY_APPEND, Abbr ‘Ns'’] \\
     rw [EVERY_MEM, Abbr ‘Is’, closed_def, MEM_GENLIST] \\
     REWRITE_TAC [FV_I])
 >> DISCH_TAC
 >> MATCH_MP_TAC solvable_alt_universal_lemma
 >> Q.EXISTS_TAC ‘Ns'’ >> rw []
QED

Theorem ssub_LAM[local] = List.nth(CONJUNCTS ssub_thm, 2)

(* Lemma 8.3.3 (ii) [1, p.172] *)
Theorem solvable_iff_LAM[simp] :
    !x M. solvable (LAM x M) <=> solvable M
Proof
    rpt STRIP_TAC
 >> reverse EQ_TAC
 >> rw [solvable_alt_closed_substitution_instance, closed_substitution_instances_def]
 >| [ (* goal 1 (of 2) *)
      Cases_on ‘x IN FV M’ >| (* 2 subgoals *)
      [ (* goal 1.1 (of 2) *)
        Q.ABBREV_TAC ‘fm0 = fm \\ x’ \\
        Q.ABBREV_TAC ‘N = fm ' x’ \\
        Q.PAT_X_ASSUM ‘fm ' M @* Ns == I’ MP_TAC \\
        Know ‘fm = fm0 |+ (x,N)’
        >- (rw [Abbr ‘fm0’, DOMSUB_FUPDATE_THM, FUPDATE_ELIM]) >> Rewr' \\
        Know ‘(fm0 |+ (x,N)) ' M = fm0 ' ([N/x] M)’
        >- (MATCH_MP_TAC ssub_update_apply_subst \\
            Q.PAT_X_ASSUM ‘!v. v IN FDOM fm ==> closed (fm ' v)’ MP_TAC \\
            rw [Abbr ‘fm0’, Abbr ‘N’, DOMSUB_FAPPLY_THM, closed_def]) >> Rewr' \\
        DISCH_TAC \\
        Know ‘fm0 ' (LAM x M @@ N) @* Ns == I’
        >- (MATCH_MP_TAC lameq_TRANS \\
            Q.EXISTS_TAC ‘fm0 ' ([N/x] M) @* Ns’ \\
            POP_ASSUM (REWRITE_TAC o wrap) \\
            MATCH_MP_TAC lameq_appstar_cong \\
            MATCH_MP_TAC lameq_ssub_cong \\
            rw [Abbr ‘fm0’, lameq_rules, DOMSUB_FAPPLY_THM]) \\
        POP_ASSUM K_TAC (* useless now *) \\
        REWRITE_TAC [ssub_thm, appstar_CONS] \\
        Know ‘fm0 ' N = N’
        >- (MATCH_MP_TAC ssub_value >> Q.UNABBREV_TAC ‘N’ \\
            fs [closed_def]) >> Rewr' \\
        DISCH_TAC \\
        qexistsl_tac [‘fm0 ' (LAM x M)’, ‘N::Ns’] >> rw [Abbr ‘N’] \\
        Q.EXISTS_TAC ‘fm0’ >> rw [Abbr ‘fm0’, DOMSUB_FAPPLY_THM],
        (* goal 1.2 (of 2) *)
        Know ‘fm ' (LAM x M @@ I) @* Ns == I’
        >- (MATCH_MP_TAC lameq_TRANS \\
            Q.EXISTS_TAC ‘fm ' M @* Ns’ >> art [] \\
            MATCH_MP_TAC lameq_appstar_cong \\
            MATCH_MP_TAC lameq_ssub_cong >> art [] \\
           ‘M = [I/x] M’ by rw [lemma14b] \\
            POP_ASSUM (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites o wrap) \\
            rw [lameq_rules]) \\
        REWRITE_TAC [ssub_thm, appstar_CONS] \\
       ‘fm ' I = I’ by rw [ssub_value] >> POP_ORW \\
        DISCH_TAC \\
        qexistsl_tac [‘fm ' (LAM x M)’, ‘I::Ns’] \\
       ‘closed I’ by rw [closed_def] >> rw [] \\
        Q.EXISTS_TAC ‘fm’ >> rw [GSYM DELETE_NON_ELEMENT] ],
      (* goal 2 (of 2) *)
      Cases_on ‘x IN FV M’ >| (* 2 subgoals *)
      [ (* goal 2.1 (of 2) *)
       ‘x NOTIN FDOM fm’ by ASM_SET_TAC [] \\
        Q.PAT_X_ASSUM ‘fm ' (LAM x M) @* Ns == I’ MP_TAC \\
        Know ‘fm ' (LAM x M) = LAM x (fm ' M)’
        >- (MATCH_MP_TAC ssub_LAM >> fs [closed_def]) >> Rewr' \\
        Cases_on ‘Ns’ (* special case: [] *)
        >- (rw [] \\
            Know ‘LAM x (fm ' M) @@ I == I @@ I’
            >- (ASM_SIMP_TAC (betafy (srw_ss())) []) \\
            SIMP_TAC (betafy (srw_ss())) [lameq_I] \\
            Know ‘[I/x] (fm ' M) = (fm |+ (x,I)) ' M’
            >- (MATCH_MP_TAC (GSYM ssub_update_apply) >> art []) >> Rewr' \\
            DISCH_TAC \\
            qexistsl_tac [‘(fm |+ (x,I)) ' M’, ‘[]’] >> rw [] \\
            Q.EXISTS_TAC ‘fm |+ (x,I)’ >> rw [] \\
           ‘closed I’ by rw [closed_def] \\
            Cases_on ‘x = v’ >> rw [FAPPLY_FUPDATE_THM]) \\
       ‘h :: t = [h] ++ t’ by rw [] >> POP_ORW \\
        simp [appstar_APPEND] \\
        DISCH_TAC \\
        Know ‘[h/x] (fm ' M) @* t == I’
        >- (MATCH_MP_TAC lameq_TRANS \\
            Q.EXISTS_TAC ‘LAM x (fm ' M) @@ h @* t’ >> art [] \\
            MATCH_MP_TAC lameq_appstar_cong \\
            rw [lameq_rules]) \\
        POP_ASSUM K_TAC \\
        Know ‘[h/x] (fm ' M) = (fm |+ (x,h)) ' M’
        >- (MATCH_MP_TAC (GSYM ssub_update_apply) >> art []) >> Rewr' \\
        DISCH_TAC \\
        qexistsl_tac [‘(fm |+ (x,h)) ' M’, ‘t’] >> fs [] \\
        Q.EXISTS_TAC ‘fm |+ (x,h)’ >> rw [] \\
        Cases_on ‘x = v’ >> rw [FAPPLY_FUPDATE_THM],
        (* goal 2.2 (of 2) *)
       ‘x NOTIN FDOM fm’ by ASM_SET_TAC [] \\
       ‘FV M DELETE x = FV M’ by PROVE_TAC [DELETE_NON_ELEMENT] \\
        POP_ASSUM (fs o wrap) \\
        Q.PAT_X_ASSUM ‘fm ' (LAM x M) @* Ns == I’ MP_TAC \\
        Know ‘fm ' (LAM x M) = LAM x (fm ' M)’
        >- (MATCH_MP_TAC ssub_LAM >> fs [closed_def]) >> Rewr' \\
        Know ‘FV (fm ' M) = FV M DIFF FDOM fm’
        >- (MATCH_MP_TAC FV_ssub >> fs [closed_def]) \\
        simp [] >> DISCH_TAC \\
        Cases_on ‘Ns’ (* special case: [] *)
        >- (rw [] \\
            Know ‘LAM x (fm ' M) @@ I == I @@ I’
            >- (ASM_SIMP_TAC (betafy (srw_ss())) []) \\
            SIMP_TAC (betafy (srw_ss())) [lameq_I] \\
            Know ‘[I/x] (fm ' M) = fm ' M’
            >- (MATCH_MP_TAC lemma14b >> rw []) >> Rewr' \\
            DISCH_TAC \\
            qexistsl_tac [‘fm ' M’, ‘[]’] >> rw [] \\
            Q.EXISTS_TAC ‘fm’ >> simp []) \\
        ‘h :: t = [h] ++ t’ by rw [] >> POP_ORW \\
        simp [appstar_APPEND] \\
        DISCH_TAC \\
        Know ‘[h/x] (fm ' M) @* t == I’
        >- (MATCH_MP_TAC lameq_TRANS \\
            Q.EXISTS_TAC ‘LAM x (fm ' M) @@ h @* t’ >> art [] \\
            MATCH_MP_TAC lameq_appstar_cong \\
            rw [lameq_rules]) \\
        POP_ASSUM K_TAC \\
        Know ‘[h/x] (fm ' M) = fm ' M’
        >- (MATCH_MP_TAC lemma14b >> rw []) >> Rewr' \\
        DISCH_TAC \\
        qexistsl_tac [‘fm ' M’, ‘t’] >> fs [] \\
        Q.EXISTS_TAC ‘fm’ >> simp [] ] ]
QED

Theorem solvable_iff_LAMl[simp] :
    !vs M. solvable (LAMl vs M) <=> solvable M
Proof
    Induct_on ‘vs’ >> rw [solvable_iff_LAM]
QED

(* Theorem 8.3.14 (Wadsworth) [1, p.175] *)
Theorem solvable_iff_has_hnf :
    !M. solvable M <=> has_hnf M
Proof
    Q.X_GEN_TAC ‘M’
 >> Q.ABBREV_TAC ‘vs = SET_TO_LIST (FV M)’
 >> Q.ABBREV_TAC ‘M0 = LAMl vs M’
 >> ‘closed M0’
       by (rw [closed_def, Abbr ‘M0’, Abbr ‘vs’, FV_LAMl, SET_TO_LIST_INV])
 >> Suff ‘solvable M0 <=> has_hnf M0’
 >- (‘solvable M <=> solvable M0’ by rw [Abbr ‘M0’, solvable_iff_LAMl] \\
     POP_ORW >> Rewr' \\
     rw [Abbr ‘M0’, has_hnf_LAMl_E])
 >> POP_ASSUM MP_TAC >> KILL_TAC
 >> Q.SPEC_TAC (‘M0’, ‘M’)
 (* stage work, now M is closed *)
 >> rpt STRIP_TAC >> EQ_TAC
 >- (rw [solvable_alt_closed] \\
     Know ‘has_hnf (M @* Ns)’
     >- (rw [has_hnf_def] \\
         Q.EXISTS_TAC ‘I’ >> rw [hnf_I]) \\
     Q.ID_SPEC_TAC ‘Ns’ >> KILL_TAC \\
     HO_MATCH_MP_TAC SNOC_INDUCT >> rw [SNOC_APPEND, appstar_SNOC] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     rename1 ‘has_hnf (M @* Ns @@ N)’ \\
     MATCH_MP_TAC has_hnf_APP_E >> art [])
 (* stage work *)
 >> rw [has_hnf_thm, solvable_alt_closed]
 >> Know ‘closed N’
 >- (fs [closed_def] \\
     Suff ‘FV N SUBSET FV M’ >- ASM_SET_TAC [] \\
     MP_TAC (Q.GEN ‘v’ (Q.SPECL [‘M’, ‘N’] hreduces_FV)) >> rw [SUBSET_DEF])
 >> DISCH_TAC
 >> ‘?vs y Ns. ALL_DISTINCT vs /\ N = LAMl vs (VAR y @* Ns)’
       by METIS_TAC [hnf_cases] (* new version with ALL_DISTINCT *)
 >> Know ‘MEM y vs’
 >- (CCONTR_TAC \\
     Q.PAT_X_ASSUM ‘closed N’ MP_TAC \\
     rw [Once EXTENSION, FV_LAMl, FV_appstar, closed_def] \\
     Q.EXISTS_TAC ‘y’ >> rw [])
 >> DISCH_TAC
 >> Suff ‘?Ms. N @* Ms == I’
 >- (STRIP_TAC \\
     Q.EXISTS_TAC ‘Ms’ \\
    ‘M == N’ by PROVE_TAC [hreduces_lameq] \\
    ‘M @* Ms == N @* Ms’ by PROVE_TAC [lameq_appstar_cong] \\
     MATCH_MP_TAC lameq_TRANS \\
     Q.EXISTS_TAC ‘N @* Ms’ >> art [])
 >> qabbrev_tac ‘n = LENGTH vs’
 >> qabbrev_tac ‘m = LENGTH Ns’
 >> Q.PAT_X_ASSUM ‘N = LAMl vs (VAR y @* Ns)’ (ONCE_REWRITE_TAC o wrap)
 (* now we use arithmeticTheory.FUNPOW instead of locally defined one *)
 >> qabbrev_tac ‘Ms = GENLIST (\i. FUNPOW (APP K) m I) n’
 >> Q.EXISTS_TAC ‘Ms’
 (* applying ssub_appstar *)
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘(FEMPTY |++ ZIP (vs,Ms)) ' (VAR y @* Ns)’
 >> CONJ_TAC
 >- (MATCH_MP_TAC lameq_LAMl_appstar_ssub_closed >> art [] \\
     CONJ_TAC >- rw [Abbr ‘Ms’] \\
     rw [EVERY_EL, Abbr ‘Ms’, closed_def, FV_FUNPOW])
 >> REWRITE_TAC [ssub_appstar]
 >> Q.PAT_ASSUM ‘MEM y vs’ ((Q.X_CHOOSE_THEN ‘i’ STRIP_ASSUME_TAC) o
                            (REWRITE_RULE [MEM_EL]))
 >> Know ‘(FEMPTY |++ ZIP (vs,Ms)) ' (VAR y) = EL i Ms’
 >- (‘LENGTH Ms = n’ by rw [Abbr ‘Ms’, LENGTH_GENLIST] \\
     Know ‘y IN FDOM (FEMPTY |++ ZIP (vs,Ms))’
     >- rw [FDOM_FUPDATE_LIST, MAP_ZIP] \\
     rw [ssub_thm] \\
     MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM >> simp [MAP_ZIP] \\
     Q.EXISTS_TAC ‘i’ >> rw [] \\
     rename1 ‘EL j vs <> EL i vs’ \\
     ‘j <> i’ by rw [] \\
     METIS_TAC [EL_ALL_DISTINCT_EL_EQ])
 >> Rewr'
 >> Know ‘EL i Ms = FUNPOW (APP K) m I’
 >- (‘i < n’ by rw [Abbr ‘n’] \\
     rw [Abbr ‘Ms’, EL_GENLIST])
 >> Rewr'
 (* final stage *)
 >> qabbrev_tac ‘Ps = MAP ($' (FEMPTY |++ ZIP (vs,Ms))) Ns’
 >> Know ‘LENGTH Ps = m’ >- (rw [Abbr ‘m’, Abbr ‘Ps’])
 >> KILL_TAC
 >> Q.ID_SPEC_TAC ‘Ps’
 >> Induct_on ‘m’ >- ASM_SIMP_TAC (betafy(srw_ss())) [LENGTH_NIL, FUNPOW]
 >> rw [FUNPOW_SUC]
 >> Cases_on ‘Ps’ >> fs []
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘FUNPOW (APP K) m I @* t’ >> rw []
 >> MATCH_MP_TAC lameq_appstar_cong >> rw [lameq_K]
QED

Theorem solvable_tpm_I[local] :
    !pi M. solvable M ==> solvable (tpm pi M)
Proof
    rw [solvable_iff_has_hnf, has_hnf_thm]
 >> Q.EXISTS_TAC ‘tpm pi N’ >> rw []
QED

Theorem solvable_tpm[simp] :
    !pi M. solvable (tpm pi M) <=> solvable M
Proof
    METIS_TAC [pmact_inverse, solvable_tpm_I]
QED

(* |- !M N z. solvable ([N/z] M) ==> solvable M *)
Theorem solvable_from_subst =
        has_hnf_SUB_E |> REWRITE_RULE [GSYM solvable_iff_has_hnf]

(*---------------------------------------------------------------------------*
 *  Principle Head Normal Forms (principle_hnf)
 *---------------------------------------------------------------------------*)

(* Definition 8.3.20 [1, p.177]

   A term may have many different hnf's. For example, if any hnf can still do
   beta reductions, after reductions the hnf is still an hnf of the original term.

   For solvable terms, there is a unique terminating hnf as the last element of
   head reduction path, which is called "principle" hnf.
 *)
Definition principle_hnf_def :
    principle_hnf = last o head_reduction_path
End

(* NOTE: This theorem fully captures the characteristics of principle hnf *)
Theorem principle_hnf_thm :
    !M N. has_hnf M ==> (principle_hnf M = N <=> M -h->* N /\ hnf N)
Proof
    rw [corollary11_4_8]
 >> qabbrev_tac ‘p = head_reduction_path M’
 >> MP_TAC (Q.SPECL [‘M’, ‘p’] finite_head_reduction_path_to_list_11)
 >> RW_TAC std_ss [principle_hnf_def]
 >> simp [finite_last_el]
 >> Q.PAT_X_ASSUM ‘LENGTH l = THE (length p)’ (ONCE_REWRITE_TAC o wrap o SYM)
 >> qabbrev_tac ‘n = PRE (LENGTH l)’
 >> ‘LENGTH l <> 0’ by rw [GSYM NOT_NIL_EQ_LENGTH_NOT_0]
 >> ‘n < LENGTH l’ by rw [Abbr ‘n’]
 >> Q.PAT_X_ASSUM ‘!i. i < LENGTH l ==> EL i l = el i p’ (fn th => rw [GSYM th])
 (* now the path p is not needed *)
 >> Q.PAT_X_ASSUM ‘finite p’ K_TAC
 >> qunabbrev_tac ‘p’
 (* easier direction first *)
 >> EQ_TAC
 >- (DISCH_THEN (ONCE_REWRITE_TAC o wrap o SYM) \\
     reverse CONJ_TAC
     >- (Suff ‘EL n l = LAST l’ >- rw [] \\
         rw [LAST_EL, Abbr ‘n’]) \\
     POP_ASSUM MP_TAC \\
     Q.SPEC_TAC (‘n’, ‘i’) \\
     Induct_on ‘i’ >> rw [] \\
     MATCH_MP_TAC hreduce_TRANS \\
     Q.EXISTS_TAC ‘EL i l’ >> rw [])
 (* stage work *)
 >> rpt STRIP_TAC
 >> qabbrev_tac ‘M = HD l’
 (* now both ‘LAST l’ and ‘N’ is hnf, they must be the same, because a hnf has
    no further head reductions, and we know N is in the head reduction path.

    But first, we need to prove |- ?i. i < LENGTH l /\ N = EL i l, because
    head reduction is deterministic, thus all reductions from ‘HD l’ must lie
    in the list l.
 *)
 >> Know ‘!N0. M -h->* N0 ==> ?i. i < LENGTH l /\ N0 = EL i l’
 >- (HO_MATCH_MP_TAC RTC_ALT_RIGHT_INDUCT >> rw []
     >- (Q.EXISTS_TAC ‘0’ >> rw [Abbr ‘M’]) \\
    ‘SUC i < LENGTH l \/ i = n’ by rw [Abbr ‘n’]
     >- (‘EL i l -h-> EL (SUC i) l’ by PROVE_TAC [] \\
         Q.EXISTS_TAC ‘SUC i’ >> art [] \\
         PROVE_TAC [hreduce1_unique]) \\
    ‘EL i l = LAST l’ by rw [LAST_EL, Abbr ‘n’] \\
     METIS_TAC [hnf_def])
 >> DISCH_THEN (MP_TAC o (Q.SPEC ‘N’))
 >> RW_TAC std_ss []
 >> ‘i = n \/ i < n \/ n < i’ by rw []
 >| [ (* goal 1 (of 3) *)
      rw [],
      (* goal 2 (of 3) *)
     ‘SUC i < LENGTH l’ by rw [Abbr ‘n’] \\
     ‘EL i l -h-> EL (SUC i) l’ by PROVE_TAC [] \\
      METIS_TAC [hnf_def],
      (* goal 3 (of 3) *)
      fs [Abbr ‘n’] ]
QED

Theorem principle_hnf_thm' =
        principle_hnf_thm |> REWRITE_RULE [GSYM solvable_iff_has_hnf]

(* principle hnf has less (or equal) free variables

   NOTE: this theorem depends on finite_head_reduction_path_to_list_11 and
         hreduce1_FV.
 *)
Theorem principle_hnf_FV_SUBSET :
    !M. has_hnf M ==> FV (principle_hnf M) SUBSET FV M
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘N = principle_hnf M’
 (* applying principle_hnf_thm *)
 >> Know ‘principle_hnf M = N’ >- rw [Abbr ‘N’]
 >> rw [principle_hnf_thm]
 >> Q.PAT_X_ASSUM ‘M -h->* N’ MP_TAC
 >> Q.ID_SPEC_TAC ‘N’
 >> HO_MATCH_MP_TAC RTC_ALT_RIGHT_INDUCT >> rw []
 >> rename1 ‘N0 -h-> N1’
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘FV N0’ >> art []
 >> rw [SUBSET_DEF]
 >> irule hreduce1_FV
 >> Q.EXISTS_TAC ‘N1’ >> art []
QED

(* |- !M. solvable M ==> FV (principle_hnf M) SUBSET FV M *)
Theorem principle_hnf_FV_SUBSET' =
        principle_hnf_FV_SUBSET |> REWRITE_RULE [GSYM solvable_iff_has_hnf]

Theorem hnf_principle_hnf :
    !M. has_hnf M ==> hnf (principle_hnf M)
Proof
    rw [corollary11_4_8, principle_hnf_def]
 >> MP_TAC (Q.SPEC ‘M’ head_reduction_path_def)
 >> RW_TAC std_ss []
QED

(* |- !M. solvable M ==> hnf (principle_hnf M) *)
Theorem hnf_principle_hnf' =
    REWRITE_RULE [GSYM solvable_iff_has_hnf] hnf_principle_hnf

Theorem solvable_principle_hnf :
    !M. solvable M ==> solvable (principle_hnf M)
Proof
    rw [solvable_iff_has_hnf]
 >> MATCH_MP_TAC hnf_has_hnf
 >> MATCH_MP_TAC hnf_principle_hnf >> art []
QED

Theorem principle_hnf_has_hnf =
    REWRITE_RULE [solvable_iff_has_hnf] solvable_principle_hnf

Theorem principle_hnf_reduce[simp] :
    !M. hnf M ==> principle_hnf M = M
Proof
    rw [principle_hnf_def]
 >> ‘finite (head_reduction_path M)’ by PROVE_TAC [hnf_has_hnf, corollary11_4_8]
 >> MP_TAC (Q.SPEC ‘M’ head_reduction_path_def)
 >> RW_TAC std_ss []
 (* applying is_head_reduction_thm *)
 >> qabbrev_tac ‘p = head_reduction_path M’
 >> STRIP_ASSUME_TAC (ISPEC “p :(term, redpos list) path” path_cases)
 >- fs []
 >> gs [is_head_reduction_thm, hnf_no_head_redex]
QED

Theorem principle_hnf_stable :
    !M. has_hnf M ==> principle_hnf (principle_hnf M) = principle_hnf M
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC principle_hnf_reduce
 >> MATCH_MP_TAC hnf_principle_hnf >> art []
QED

(* |- !M. solvable M ==> principle_hnf (principle_hnf M) = principle_hnf M *)
Theorem principle_hnf_stable' =
    REWRITE_RULE [GSYM solvable_iff_has_hnf] principle_hnf_stable

Theorem principle_hnf_beta :
    !v t. hnf t /\ y # t ==> principle_hnf (LAM v t @@ VAR y) = [VAR y/v] t
Proof
    rw [principle_hnf_def]
 >> qabbrev_tac ‘M = LAM v t @@ VAR y’
 >> qabbrev_tac ‘N = [VAR y/v] t’
 >> ‘hnf N’ by rw [Abbr ‘N’, GSYM fresh_tpm_subst]
 >> Know ‘M -h-> N’
 >- rw [Abbr ‘M’, Abbr ‘N’, hreduce1_BETA]
 >> rw [head_reduce1_def]
 >> qabbrev_tac ‘p = pcons M r (stopped_at N)’
 >> Suff ‘head_reduction_path M = p’ >- rw [Abbr ‘p’]
 >> MATCH_MP_TAC head_reduction_path_unique
 >> rw [Abbr ‘p’]
QED

(* NOTE: this shows that ‘principle_hnf’ is the normal_form of hreduce1 *)
Theorem principle_hnf_hreduce1 :
    !M N. M -h-> N ==> principle_hnf M = principle_hnf N
Proof
    rw [principle_hnf_def]
 >> qabbrev_tac ‘p = head_reduction_path N’
 >> ‘?r. r is_head_redex M /\ labelled_redn beta M r N’
        by METIS_TAC [head_reduce1_def]
 >> qabbrev_tac ‘q = pcons M r p’
 >> Suff ‘head_reduction_path M = q’ >- rw [Abbr ‘q’]
 >> MATCH_MP_TAC head_reduction_path_unique
 >> STRIP_ASSUME_TAC (Q.SPEC ‘N’ head_reduction_path_def)
 >> rw [Abbr ‘q’, Abbr ‘p’, Once is_head_reduction_thm]
QED

(* NOTE: this useful theorem can be used to rewrite ‘principle_hnf M’ to
  ‘principle_hnf N’, if one can prove ‘M -h->* N’. *)
Theorem principle_hnf_hreduce :
    !M N. M -h->* N ==> principle_hnf M = principle_hnf N
Proof
    HO_MATCH_MP_TAC RTC_INDUCT >> rw []
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
 >> MATCH_MP_TAC principle_hnf_hreduce1 >> art []
QED

Theorem principle_hnf_LAMl_appstar_lemma[local] :
    !t. hnf t /\
        ALL_DISTINCT (MAP FST pi) /\
        ALL_DISTINCT (MAP SND pi) /\
        DISJOINT (set (MAP FST pi)) (set (MAP SND pi)) /\
       (!y. MEM y (MAP SND pi) ==> y # t) ==>
        principle_hnf (LAMl (MAP FST pi) t @* MAP VAR (MAP SND pi)) = tpm pi t
Proof
    Induct_on ‘pi’
 >- rw [principle_hnf_reduce]
 >> rw []
 >> Cases_on ‘h’ (* ‘x’ *) >> fs []
 >> qabbrev_tac ‘M = LAMl (MAP FST pi) t’
 >> ‘hnf M’ by rw [Abbr ‘M’, hnf_LAMl]
 >> qabbrev_tac ‘args :term list = MAP VAR (MAP SND pi)’
 >> Know ‘principle_hnf (LAM q M @@ VAR r @* args) =
          principle_hnf ([VAR r/q] M @* args)’
 >- (MATCH_MP_TAC principle_hnf_hreduce1 \\
     MATCH_MP_TAC hreduce1_rules_appstar >> rw [hreduce1_BETA])
 >> Rewr'
 >> Know ‘[VAR r/q] M = LAMl (MAP FST pi) ([VAR r/q] t)’
 >- (qunabbrev_tac ‘M’ \\
     MATCH_MP_TAC LAMl_SUB \\
     rw [DISJOINT_ALT])
 >> Rewr'
 >> qabbrev_tac ‘N = [VAR r/q] t’
 >> Know ‘N = tpm [(q,r)] t’
 >- (rw [Abbr ‘N’, Once EQ_SYM_EQ, Once pmact_flip_args] \\
     MATCH_MP_TAC fresh_tpm_subst >> rw [])
 >> Rewr'
 >> qabbrev_tac ‘N' = tpm [(q,r)] t’
 >> ‘hnf N'’ by rw [Abbr ‘N'’, hnf_tpm]
 >> Know ‘principle_hnf (LAMl (MAP FST pi) N' @* args) = tpm pi N'’
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw [Abbr ‘N'’] \\
    ‘r <> y’ by PROVE_TAC [] \\
     Cases_on ‘q = y’ >> rw [])
 >> POP_ASSUM K_TAC >> qunabbrev_tac ‘N'’
 >> Know ‘tpm [(q,r)] t = N’
 >- (rw [Abbr ‘N’, Once pmact_flip_args] \\
     MATCH_MP_TAC fresh_tpm_subst >> rw [])
 >> Rewr'
 >> rw [Abbr ‘N’, tpm_subst]
 (* applying lswapstr_unchanged *)
 >> Know ‘lswapstr pi r = r’
 >- (MATCH_MP_TAC lswapstr_unchanged \\
     rw [IN_patoms_MEM] \\
     CCONTR_TAC >> fs [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.PAT_X_ASSUM ‘~MEM r (MAP FST pi)’ MP_TAC >> rw [MEM_MAP] \\
       Q.EXISTS_TAC ‘(r,b)’ >> rw [],
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM ‘~MEM r (MAP SND pi)’ MP_TAC >> rw [MEM_MAP] \\
       Q.EXISTS_TAC ‘(b,r)’ >> rw [] ])
 >> Rewr'
 >> Know ‘lswapstr pi q = q’
 >- (MATCH_MP_TAC lswapstr_unchanged \\
     rw [IN_patoms_MEM] \\
     CCONTR_TAC >> fs [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.PAT_X_ASSUM ‘~MEM q (MAP FST pi)’ MP_TAC >> rw [MEM_MAP] \\
       Q.EXISTS_TAC ‘(q,b)’ >> rw [],
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM ‘~MEM q (MAP SND pi)’ MP_TAC >> rw [MEM_MAP] \\
       Q.EXISTS_TAC ‘(b,q)’ >> rw [] ])
 >> Rewr'
 >> REWRITE_TAC [Once tpm_CONS, Once pmact_flip_args, Once EQ_SYM_EQ]
 >> MATCH_MP_TAC fresh_tpm_subst
 >> rw [FV_tpm]
 >> Know ‘lswapstr (REVERSE pi) r = r’
 >- (MATCH_MP_TAC lswapstr_unchanged \\
     rw [IN_patoms_MEM] \\
     CCONTR_TAC >> fs [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.PAT_X_ASSUM ‘~MEM r (MAP FST pi)’ MP_TAC >> rw [MEM_MAP] \\
       Q.EXISTS_TAC ‘(r,b)’ >> rw [],
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM ‘~MEM r (MAP SND pi)’ MP_TAC >> rw [MEM_MAP] \\
       Q.EXISTS_TAC ‘(b,r)’ >> rw [] ])
 >> Rewr'
 >> FIRST_X_ASSUM MATCH_MP_TAC >> rw []
QED

(* ‘principle_hnf’ can be used to do final beta-reductions for an abs-free hnf

   NOTE: to satisfy ‘DISJOINT (set xs) (set ys)’, one first get ‘LENGTH xs’
         without knowing ‘xs’ (e.g. by ‘LAMl_size’), then generate ‘ys’ by
        ‘FRESH_list’, and then call [hnf_cases_genX] using ‘ys’ as the new
         excluded list.
 *)
Theorem principle_hnf_LAMl_appstar :
    !t xs ys. hnf t /\
              ALL_DISTINCT xs /\ ALL_DISTINCT ys /\
              LENGTH xs = LENGTH ys /\
              DISJOINT (set xs) (set ys) /\
              DISJOINT (set ys) (FV t)
          ==> principle_hnf (LAMl xs t @* MAP VAR ys) = tpm (ZIP (xs,ys)) t
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘n = LENGTH xs’
 >> qabbrev_tac ‘pi = ZIP (xs,ys)’
 >> ‘xs = MAP FST pi’ by rw [Abbr ‘pi’, MAP_ZIP]
 >> ‘ys = MAP SND pi’ by rw [Abbr ‘pi’, MAP_ZIP]
 >> Know ‘!y. MEM y (MAP SND pi) ==> y # t’
 >- (Q.PAT_X_ASSUM ‘DISJOINT (set vs) (FV t)’ MP_TAC \\
     rw [DISJOINT_ALT, Abbr ‘pi’, MEM_MAP, MEM_ZIP, MEM_EL] \\
     simp [] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘n’ >> art [])
 >> DISCH_TAC
 >> simp []
 >> MATCH_MP_TAC principle_hnf_LAMl_appstar_lemma >> rw []
QED

Theorem principle_hnf_beta_reduce1 :
    !v t. hnf t ==> principle_hnf (LAM v t @@ VAR v) = t
Proof
    rpt STRIP_TAC
 >> Know ‘principle_hnf (LAM v t @@ VAR v) =
          principle_hnf ([VAR v/v] t)’
 >- (MATCH_MP_TAC principle_hnf_hreduce1 \\
     rw [hreduce1_BETA])
 >> Rewr'
 >> rw [principle_hnf_reduce]
QED

Theorem principle_hnf_beta_reduce :
    !xs t. hnf t ==> principle_hnf (LAMl xs t @* MAP VAR xs) = t
Proof
    Induct_on ‘xs’
 >> rw [principle_hnf_reduce]
 >> qabbrev_tac ‘M = LAMl xs t’
 >> qabbrev_tac ‘args :term list = MAP VAR xs’
 >> Know ‘principle_hnf (LAM h M @@ VAR h @* args) =
          principle_hnf ([VAR h/h] M @* args)’
 >- (MATCH_MP_TAC principle_hnf_hreduce1 \\
     MATCH_MP_TAC hreduce1_rules_appstar >> rw [hreduce1_BETA])
 >> Rewr'
 >> simp [Abbr ‘M’]
QED

Theorem hreduce_BETA :
    !vs t. LAMl vs t @* MAP VAR vs -h->* t
Proof
    Induct_on ‘vs’
 >> rw [Once RTC_CASES1] (* only 1 goal is left *)
 >> DISJ2_TAC
 >> qabbrev_tac ‘M = LAMl vs t’
 >> Q.EXISTS_TAC ‘[VAR h/h] M @* MAP VAR vs’
 >> reverse CONJ_TAC >- rw [Abbr ‘M’]
 >> MATCH_MP_TAC hreduce1_rules_appstar
 >> rw [hreduce1_BETA]
QED

(* Example 8.3.2 [1, p.171] *)
Theorem unsolvable_Omega :
    unsolvable Omega
Proof
   ‘closed Omega’ by rw [closed_def]
 >> rw [solvable_alt_closed]
 >> CCONTR_TAC >> fs []
 >> ‘?Z. Omega @* Ns -b->* Z /\ I -b->* Z’ by METIS_TAC [lameq_CR]
 >> fs [bnf_reduction_to_self]
 >> Q.PAT_X_ASSUM ‘closed Omega’ K_TAC
 >> POP_ASSUM K_TAC (* Z = I *)
 >> ‘?Ms. I = Omega @* Ms’ by METIS_TAC [Omega_appstar_starloops]
 >> POP_ASSUM MP_TAC
 >> rw [Omega_def, I_def]
QED

(* Another proof based on solvable_iff_has_hnf, told by Michael Norrish *)
Theorem unsolvable_Omega' :
    unsolvable Omega
Proof
    rw [solvable_iff_has_hnf, corollary11_4_8]
 >> ‘?r. r is_head_redex Omega /\ labelled_redn beta Omega r Omega’
       by (rw [GSYM head_reduce1_def, Omega_hreduce1_loops])
 >> qabbrev_tac ‘p = pgenerate (\n. Omega) (\n. r)’
 >> ‘infinite p’ by rw [Abbr ‘p’, pgenerate_infinite]
 >> ‘tail p = p’ by rw [Abbr ‘p’, Once pgenerate_def, tail_def, combinTheory.o_DEF]
 >> Suff ‘head_reduction_path Omega = p’ >- (Rewr' >> art [])
 >> MATCH_MP_TAC head_reduction_path_unique
 >> simp []
 >> CONJ_TAC >- rw [Abbr ‘p’, Once pgenerate_def]
 (* is_head_reduction p *)
 >> irule is_head_reduction_coind
 >> Q.EXISTS_TAC ‘\p. first p = Omega /\ first_label p = r /\ tail p = p’
 >> simp []
 >> CONJ_TAC >- (STRIP_TAC >> rw [Abbr ‘p’, Once pgenerate_def])
 >> RW_TAC std_ss [] (* 4 subgoals *)
 >| [ POP_ORW >> simp [first_thm],
      POP_ORW >> simp [first_thm],
      POP_ORW >> simp [first_label_def],
      METIS_TAC [tail_def] ]
QED

Theorem lameq_solvable_cong_lemma[local] :
    !M N. closed M /\ closed N /\ M == N ==> (solvable M <=> solvable N)
Proof
    Suff ‘!M N. closed M /\ closed N /\ M == N /\ solvable M ==> solvable N’
 >- METIS_TAC [lameq_SYM]
 >> rw [solvable_alt_closed]
 >> gs [solvable_alt_closed]
 >> Q.EXISTS_TAC ‘Ns’
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘M @* Ns’ >> art []
 >> MATCH_MP_TAC lameq_appstar_cong
 >> rw [lameq_SYM]
QED

(* NOTE: this proof has used first principles of solvable terms *)
Theorem lameq_solvable_cong :
    !M N. M == N ==> (solvable M <=> solvable N)
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘vs = SET_TO_LIST (FV M UNION FV N)’
 >> qabbrev_tac ‘M0 = LAMl vs M’
 >> qabbrev_tac ‘N0 = LAMl vs N’
 >> Know ‘closed M0 /\ closed N0’
 >- (rw [closed_def, Abbr ‘M0’, Abbr ‘N0’, Abbr ‘vs’, FV_LAMl] \\
    ‘FINITE (FV M UNION FV N)’ by rw [] \\
     simp [SET_TO_LIST_INV] >> SET_TAC [])
 >> STRIP_TAC
 (* applying solvable_iff_LAMl *)
 >> ‘solvable M <=> solvable M0’ by (rw [Abbr ‘M0’]) >> POP_ORW
 >> ‘solvable N <=> solvable N0’ by (rw [Abbr ‘N0’]) >> POP_ORW
 >> ‘M0 == N0’ by (rw [Abbr ‘M0’, Abbr ‘N0’, lameq_LAMl_cong])
 >> MATCH_MP_TAC lameq_solvable_cong_lemma >> art []
QED

Theorem lameq_principle_hnf :
    !M. has_hnf M ==> principle_hnf M == M
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘N = principle_hnf M’
 >> Know ‘M head_reduces N’
 >- (rw [head_reduces_def] \\
     Q.EXISTS_TAC ‘head_reduction_path M’ \\
     fs [corollary11_4_8, head_reduction_path_def] \\
     rw [Abbr ‘N’, principle_hnf_def])
 >> rw [head_reduces_RTC_hreduce1]
 >> MATCH_MP_TAC lameq_SYM
 >> MATCH_MP_TAC hreduces_lameq >> art []
QED

(* |- !M. solvable M ==> principle_hnf M == M *)
Theorem lameq_principle_hnf' =
        lameq_principle_hnf |> REWRITE_RULE [GSYM solvable_iff_has_hnf]

Theorem hnf_ccbeta_appstar_rwt[local] :
    !y Ms N. VAR y @* Ms -b-> N /\ Ms <> [] ==>
             ?Ns. N = VAR y @* Ns /\ LENGTH Ns = LENGTH Ms /\
                  !i. i < LENGTH Ms ==> EL i Ms -b->* EL i Ns
Proof
    Q.X_GEN_TAC ‘y’
 >> Induct_on ‘Ms’ using SNOC_INDUCT >> rw []
 >> fs [ccbeta_rwt] (* 2 subgoals *)
 >- (Cases_on ‘Ms = []’ >> fs [ccbeta_rwt] \\
     Q.PAT_X_ASSUM ‘!N. P’ (MP_TAC o (Q.SPEC ‘M'’)) \\
     RW_TAC std_ss [] \\
     Q.EXISTS_TAC ‘SNOC x Ns’ >> rw [] \\
    ‘i = LENGTH Ms \/ i < LENGTH Ms’ by rw []
     >- (rw [EL_LENGTH_SNOC] \\
         Q.PAT_X_ASSUM ‘LENGTH Ns = LENGTH Ms’ (REWRITE_TAC o wrap o SYM) \\
         rw [EL_LENGTH_SNOC]) \\
     rw [EL_SNOC])
 (* stage work *)
 >> Cases_on ‘Ms = []’ >> fs []
 >- (Q.EXISTS_TAC ‘[N']’ >> rw [])
 >> Q.EXISTS_TAC ‘SNOC N' Ms’
 >> rw [appstar_SNOC]
 >> ‘i = LENGTH Ms \/ i < LENGTH Ms’ by rw []
 >- (rw [EL_LENGTH_SNOC])
 >> rw [EL_SNOC]
QED

Theorem hnf_ccbeta_cases[local] :
    !Ms. LAMl vs (VAR y @* Ms) -b-> N ==>
         ?Ns. N = LAMl vs (VAR y @* Ns) /\
              LENGTH Ns = LENGTH Ms /\
              !i. i < LENGTH Ms ==> EL i Ms -b->* EL i Ns
Proof
    rw [ccbeta_LAMl_rwt]
 >> Suff ‘?Ns. M' = VAR y @* Ns /\ LENGTH Ns = LENGTH Ms /\
              !i. i < LENGTH Ms ==> EL i Ms -b->* EL i Ns’
 >- (STRIP_TAC >> Q.EXISTS_TAC ‘Ns’ >> rw [])
 >> MATCH_MP_TAC hnf_ccbeta_appstar_rwt
 >> Cases_on ‘Ms = []’ >> fs [ccbeta_rwt]
QED

(* Lemma 8.3.16 [1, p.176] *)
Theorem hnf_betastar_cases :
    !vs y Ms N. LAMl vs (VAR y @* Ms) -b->* N ==>
                ?Ns. N = LAMl vs (VAR y @* Ns) /\
                     LENGTH Ns = LENGTH Ms /\
                     !i. i < LENGTH Ms ==> EL i Ms -b->* EL i Ns
Proof
    NTAC 2 GEN_TAC
 >> Suff ‘!M N. M -b->* N ==>
               !Ms. M = LAMl vs (VAR y @* Ms) ==>
                   ?Ns. N = LAMl vs (VAR y @* Ns) /\
                        LENGTH Ns = LENGTH Ms /\
                        !i. i < LENGTH Ms ==> EL i Ms -b->* EL i Ns’
 >- METIS_TAC []
 >> HO_MATCH_MP_TAC RTC_INDUCT >> rw []
 >> Know ‘?Ns. M' = LAMl vs (VAR y @* Ns) /\
               LENGTH Ns = LENGTH Ms /\
               !i. i < LENGTH Ms ==> EL i Ms -b->* EL i Ns’
 >- (irule hnf_ccbeta_cases >> art [])
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!Ms. M' = LAMl vs (VAR y @* Ms) ==> P’
      (MP_TAC o (Q.SPEC ‘Ns’))
 >> RW_TAC std_ss [] (* this asserts Ns' *)
 >> Q.EXISTS_TAC ‘Ns'’ >> rw []
 >> MATCH_MP_TAC betastar_TRANS
 >> Q.EXISTS_TAC ‘EL i Ns’ >> rw []
QED

(* Corollary 8.3.17 (ii) [1, p.176] (inner part) *)
Theorem lameq_principle_hnf_lemma :
    !X M N. FINITE X /\ FV M SUBSET X /\ FV N SUBSET X /\
            hnf M /\ hnf N /\ M == N
        ==> LAMl_size M = LAMl_size N /\
            let n = LAMl_size M;
                vs = FRESH_list n X;
                M1 = principle_hnf (M @* MAP VAR vs);
                N1 = principle_hnf (N @* MAP VAR vs)
            in
                hnf_head M1 = hnf_head N1 /\
                LENGTH (hnf_children M1) = LENGTH (hnf_children N1) /\
                !i. i < LENGTH (hnf_children M1) ==>
                    EL i (hnf_children M1) == EL i (hnf_children N1)
Proof
    rpt GEN_TAC >> STRIP_TAC
 (* at the beginning, we don't know if n = n' *)
 >> qabbrev_tac ‘n  = LAMl_size M’
 >> qabbrev_tac ‘n' = LAMl_size N’
 (* applying hnf_cases_shared *)
 >> qabbrev_tac ‘vs = FRESH_list (MAX n n') X’
 >> ‘ALL_DISTINCT vs /\ DISJOINT (set vs) X /\ LENGTH vs = MAX n n'’
      by rw [FRESH_list_def, Abbr ‘vs’]
 >> Know ‘?y args. M = LAMl (TAKE n vs) (VAR y @* args)’
 >- (qunabbrev_tac ‘n’ >> irule (iffLR hnf_cases_shared) >> rw [] \\
     MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘X’ >> fs [])
 >> STRIP_TAC
 >> Know ‘?y' args'. N = LAMl (TAKE n' vs) (VAR y' @* args')’
 >- (qunabbrev_tac ‘n'’ >> irule (iffLR hnf_cases_shared) >> rw [] \\
     MATCH_MP_TAC DISJOINT_SUBSET \\
     Q.EXISTS_TAC ‘X’ >> fs [])
 >> STRIP_TAC
 >> qabbrev_tac ‘vs1 = TAKE n vs’
 >> qabbrev_tac ‘vs2 = TAKE n' vs’
 >> ‘n = LENGTH vs1 /\ n' = LENGTH vs2’ by rw [Abbr ‘n’, Abbr ‘n'’]
 (* applying lameq_CR *)
 >> ‘?Z. M -b->* Z /\ N -b->* Z’ by METIS_TAC [lameq_CR]
 (* applying hnf_betastar_cases *)
 >> ‘?Ns. Z = LAMl vs1 (VAR y @* Ns) /\ LENGTH Ns = LENGTH args /\
          !i. i < LENGTH args ==> EL i args -b->* EL i Ns’
       by METIS_TAC [hnf_betastar_cases]
 >> ‘?Ns'. Z = LAMl vs2 (VAR y' @* Ns') /\ LENGTH Ns' = LENGTH args' /\
          !i. i < LENGTH args' ==> EL i args' -b->* EL i Ns'’
       by METIS_TAC [hnf_betastar_cases]
 (* eliminate n' once we know n = n' *)
 >> STRONG_CONJ_TAC >- METIS_TAC [LAMl_size_hnf]
 >> DISCH_THEN (REV_FULL_SIMP_TAC std_ss o wrap o SYM)
 >> qunabbrevl_tac [‘vs1’, ‘vs2’]
 >> ‘TAKE n vs = vs’ by METIS_TAC [TAKE_LENGTH_ID]
 >> POP_ASSUM (REV_FULL_SIMP_TAC std_ss o wrap)
 (* eliminiate LETs in the goal *)
 >> simp []
 (* applying principle_hnf_beta_reduce *)
 >> Know ‘principle_hnf (LAMl vs (VAR y @* args) @* MAP VAR vs) = VAR y @* args’
 >- (MATCH_MP_TAC principle_hnf_beta_reduce >> rw [hnf_appstar])
 >> Rewr'
 >> Know ‘principle_hnf (LAMl vs (VAR y' @* args') @* MAP VAR vs) = VAR y' @* args'’
 >- (MATCH_MP_TAC principle_hnf_beta_reduce >> rw [hnf_appstar])
 >> Rewr'
 >> simp [hnf_head_hnf, hnf_children_hnf]
 >> Q.PAT_X_ASSUM ‘M = LAMl vs _’ K_TAC
 >> Q.PAT_X_ASSUM ‘N = LAMl vs _’ K_TAC
 >> gs [LAMl_eq_rewrite]
 >> Q.PAT_X_ASSUM ‘y = y'’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘Ns = Ns'’ (fs o wrap o SYM)
 >> NTAC 2 (Q.PAT_X_ASSUM ‘_ = LENGTH args’ K_TAC)
 >> Q.PAT_X_ASSUM ‘Z = _’ K_TAC
 >> rpt STRIP_TAC
 (* applying lameq_TRANS and betastar_lameq *)
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘EL i Ns’
 >> CONJ_TAC >- (MATCH_MP_TAC betastar_lameq >> rw [])
 >> MATCH_MP_TAC lameq_SYM
 >> MATCH_MP_TAC betastar_lameq >> rw []
QED

Theorem lameq_principle_hnf_size_eq :
    !M N. has_hnf M /\ has_hnf N /\ M == N ==>
          LAMl_size (principle_hnf M) = LAMl_size (principle_hnf N)
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘N0 = principle_hnf N’
 >> Know ‘M0 == N0’
 >- (MATCH_MP_TAC lameq_TRANS >> Q.EXISTS_TAC ‘M’ \\
     CONJ_TAC >- (qunabbrev_tac ‘M0’ \\
                  MATCH_MP_TAC lameq_principle_hnf >> art []) \\
     MATCH_MP_TAC lameq_TRANS >> Q.EXISTS_TAC ‘N’ >> art [] \\
     MATCH_MP_TAC lameq_SYM \\
     qunabbrev_tac ‘N0’ \\
     MATCH_MP_TAC lameq_principle_hnf >> art [])
 >> DISCH_TAC
 >> ‘hnf M0 /\ hnf N0’ by METIS_TAC [hnf_principle_hnf]
 >> qabbrev_tac ‘X = FV M0 UNION FV N0’
 >> MP_TAC (Q.SPECL [‘X’, ‘M0’, ‘N0’] lameq_principle_hnf_lemma)
 >> rw [Abbr ‘X’]
QED

(* |- !M N.
        solvable M /\ solvable N /\ M == N ==>
        LAMl_size (principle_hnf M) = LAMl_size (principle_hnf N)
 *)
Theorem lameq_principle_hnf_size_eq' =
        lameq_principle_hnf_size_eq |> REWRITE_RULE [GSYM solvable_iff_has_hnf]

Theorem lameq_principle_hnf_head_eq :
    !X M N M0 N0 n vs M1 N1.
         FINITE X /\ FV M UNION FV N SUBSET X /\
         has_hnf M /\ has_hnf N /\ M == N /\
         M0 = principle_hnf M /\ N0 = principle_hnf N /\
         n = LAMl_size M0 /\ vs = FRESH_list n X /\
         M1 = principle_hnf (M0 @* MAP VAR vs) /\
         N1 = principle_hnf (N0 @* MAP VAR vs)
     ==> hnf_head M1 = hnf_head N1
Proof
    RW_TAC std_ss [UNION_SUBSET]
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘N0 = principle_hnf N’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> qabbrev_tac ‘vs = FRESH_list n X’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> qabbrev_tac ‘N1 = principle_hnf (N0 @* MAP VAR vs)’
 >> Know ‘M0 == N0’
 >- (MATCH_MP_TAC lameq_TRANS >> Q.EXISTS_TAC ‘M’ \\
     CONJ_TAC >- (qunabbrev_tac ‘M0’ \\
                  MATCH_MP_TAC lameq_principle_hnf >> art []) \\
     MATCH_MP_TAC lameq_TRANS >> Q.EXISTS_TAC ‘N’ >> art [] \\
     MATCH_MP_TAC lameq_SYM \\
     qunabbrev_tac ‘N0’ \\
     MATCH_MP_TAC lameq_principle_hnf >> art [])
 >> DISCH_TAC
 >> ‘hnf M0 /\ hnf N0’ by METIS_TAC [hnf_principle_hnf]
 (* applying lameq_principle_hnf_lemma *)
 >> MP_TAC (Q.SPECL [‘X’, ‘M0’, ‘N0’] lameq_principle_hnf_lemma)
 >> Suff ‘FV M0 SUBSET X /\ FV N0 SUBSET X’ >- rw []
 (* applying principle_hnf_FV_SUBSET *)
 >> METIS_TAC [principle_hnf_FV_SUBSET, SUBSET_TRANS]
QED

Theorem lameq_principle_hnf_head_eq' =
        lameq_principle_hnf_head_eq |> REWRITE_RULE [GSYM solvable_iff_has_hnf]

(* Corollary 8.3.17 (ii) [1, p.176] (outer part) *)
Theorem lameq_principle_hnf_thm :
    !X M N M0 N0 n vs M1 N1.
         FINITE X /\ FV M UNION FV N SUBSET X /\
         has_hnf M /\ has_hnf N /\ M == N /\
         M0 = principle_hnf M /\ N0 = principle_hnf N /\
         n = LAMl_size M0 /\ vs = FRESH_list n X /\
         M1 = principle_hnf (M0 @* MAP VAR vs) /\
         N1 = principle_hnf (N0 @* MAP VAR vs)
     ==> LAMl_size M0 = LAMl_size N0 /\
         hnf_head M1 = hnf_head N1 /\
         LENGTH (hnf_children M1) = LENGTH (hnf_children N1) /\
         !i. i < LENGTH (hnf_children M1) ==>
             EL i (hnf_children M1) == EL i (hnf_children N1)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> NTAC 6 POP_ORW
 >> qabbrev_tac ‘M0 = principle_hnf M’
 >> qabbrev_tac ‘N0 = principle_hnf N’
 >> qabbrev_tac ‘n = LAMl_size M0’
 >> qabbrev_tac ‘vs = FRESH_list n X’
 >> qabbrev_tac ‘M1 = principle_hnf (M0 @* MAP VAR vs)’
 >> qabbrev_tac ‘N1 = principle_hnf (N0 @* MAP VAR vs)’
 >> Know ‘M0 == N0’
 >- (MATCH_MP_TAC lameq_TRANS >> Q.EXISTS_TAC ‘M’ \\
     CONJ_TAC >- (qunabbrev_tac ‘M0’ \\
                  MATCH_MP_TAC lameq_principle_hnf >> art []) \\
     MATCH_MP_TAC lameq_TRANS >> Q.EXISTS_TAC ‘N’ >> art [] \\
     MATCH_MP_TAC lameq_SYM \\
     qunabbrev_tac ‘N0’ \\
     MATCH_MP_TAC lameq_principle_hnf >> art [])
 >> DISCH_TAC
 >> ‘hnf M0 /\ hnf N0’ by METIS_TAC [hnf_principle_hnf]
 (* applying lameq_principle_hnf_lemma *)
 >> MP_TAC (Q.SPECL [‘X’, ‘M0’, ‘N0’] lameq_principle_hnf_lemma)
 >> Suff ‘FV M0 SUBSET X /\ FV N0 SUBSET X’ >- rw []
 (* applying principle_hnf_FV_SUBSET *)
 >> METIS_TAC [principle_hnf_FV_SUBSET, SUBSET_TRANS, UNION_SUBSET]
QED

Theorem lameq_principle_hnf_thm' =
        lameq_principle_hnf_thm |> REWRITE_RULE [GSYM solvable_iff_has_hnf]

(* NOTE: the difficulty of applying this theorem is to prove the antecedents *)
Theorem principle_hnf_substitutive :
    !M N v P. has_hnf M /\ has_hnf ([P/v] M) /\ has_hnf ([P/v] N) /\
              principle_hnf M = N ==>
              principle_hnf ([P/v] M) = principle_hnf ([P/v] N)
Proof
    rpt STRIP_TAC
 >> POP_ASSUM MP_TAC
 >> reverse (rw [principle_hnf_thm])
 >- (MATCH_MP_TAC hnf_principle_hnf >> art [])
 >> MATCH_MP_TAC hreduce_TRANS
 >> Q.EXISTS_TAC ‘[P/v] N’
 >> CONJ_TAC
 >- (MATCH_MP_TAC hreduce_substitutive >> art [])
 >> qabbrev_tac ‘M' = [P/v] M’
 >> qabbrev_tac ‘N' = [P/v] N’
 >> qabbrev_tac ‘Q = principle_hnf N'’
 >> Know ‘principle_hnf N' = Q’ >- rw [Abbr ‘Q’]
 >> rw [principle_hnf_thm]
QED

Theorem principle_hnf_substitutive_hnf :
    !M N v P. has_hnf M /\ has_hnf ([P/v] M) /\ hnf ([P/v] N) /\
              principle_hnf M = N ==>
              principle_hnf ([P/v] M) = [P/v] N
Proof
    rpt STRIP_TAC
 >> Know ‘principle_hnf ([P/v] M) = principle_hnf ([P/v] N)’
 >- (MATCH_MP_TAC principle_hnf_substitutive >> art [] \\
     MATCH_MP_TAC hnf_has_hnf >> art [])
 >> Rewr'
 >> MATCH_MP_TAC principle_hnf_reduce >> art []
QED

(* This is an important theroem, hard to prove.

   To use this theorem, first one defines ‘M0 = principle_hnf M’ as abbreviation,
   then define ‘n = LAMl_size M0’ and ‘vs = FRESH_list n (FV M)’ (or ‘FV M0’, or
  ‘X UNION FV M0’, ‘X UNION FV M’), and this give us the needed antecedents:

       ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M) /\ LENGTH vs = n

   Then use hnf_cases_shared to derive ‘M0 = LAMl vs (VAR y @* args)’ and then
  ‘M1 = principle_hnf (M0 @* MAP VAR vs) = VAR y @* args’.

   The conclusion is that ‘principle_hnf (M @* MAP VAR vs) = M1’.

   Now ‘principle_hnf’ can be used to "denude" the outer LAMl of a solvable term.

   An extra list of free variables ‘l’ may need to append after MAP VAR vs.
 *)
Theorem principle_hnf_denude_lemma[local] :
    !M vs l y Ns. solvable M /\
                  ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M) /\
                  M -h->* LAMl vs (VAR y @* Ns) ==>
                  M @* MAP VAR vs @* MAP VAR l -h->* VAR y @* Ns @* MAP VAR l
Proof
    rpt STRIP_TAC
 (* eliminating MAP VAR l *)
 >> MATCH_MP_TAC hreduce_rules_appstar'
 >> rw [is_abs_appstar]
 >- (fs [] >> CCONTR_TAC >> fs [] \\
    ‘is_abs (VAR y @* Ns)’ by PROVE_TAC [hreduce_abs] >> fs [])
 (* now l is eliminated *)
 >> NTAC 4 (POP_ASSUM MP_TAC)
 >> Suff ‘!M M0. M -h->* M0 ==>
                 solvable M ==>
                   !vs t. ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M) /\
                          M0 = LAMl vs t /\ ~is_abs t ==>
                          M @* MAP VAR vs -h->* t’
 >- (rpt STRIP_TAC >> FIRST_X_ASSUM irule >> rw [])
 >> HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1
 >> rw [hreduce_BETA] (* only one goal is left *)
 >> Q.PAT_X_ASSUM ‘solvable M ==> P’ MP_TAC
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
 >> Know ‘ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M0) /\ M0 -h-> LAMl vs t /\ ~is_abs t’
 >- art []
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
 >- (MATCH_MP_TAC hreduce1_rules_appstar >> art [] \\
     fs [is_comb_APP_EXISTS])
 >> MATCH_MP_TAC hreduce_rules_appstar' >> art []
 >> rw [is_abs_appstar]
 >> CCONTR_TAC >> fs []
 >> ‘is_abs N’ by PROVE_TAC [hreduce_abs]
QED

Theorem principle_hnf_denude_solvable :
    !M vs l y args. solvable M /\
       ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M) /\
       principle_hnf M = LAMl vs (VAR y @* args) ==>
       solvable (M @* MAP VAR vs @* MAP VAR l)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> qabbrev_tac ‘M0 = principle_hnf M’
 (* applying principle_hnf_thm' *)
 >> Know ‘principle_hnf M = M0’ >- rw [Abbr ‘M0’]
 >> simp [principle_hnf_thm', hnf_appstar]
 >> DISCH_TAC
 >> ‘M0 == M’ by rw [lameq_principle_hnf', Abbr ‘M0’]
 >> ‘M0 @* MAP VAR vs == VAR y @* args’ by rw []
 >> ‘M0 @* MAP VAR vs == M @* MAP VAR vs’ by rw [lameq_appstar_cong]
 >> Know ‘M @* MAP VAR vs @* MAP VAR l == VAR y @* args @* MAP VAR l’
 >- (MATCH_MP_TAC lameq_appstar_cong \\
     PROVE_TAC [lameq_SYM, lameq_TRANS])
 >> DISCH_TAC
 >> Suff ‘solvable (VAR y @* args @* MAP VAR l)’
 >- PROVE_TAC [lameq_solvable_cong]
 >> REWRITE_TAC [solvable_iff_has_hnf]
 >> MATCH_MP_TAC hnf_has_hnf >> rw [hnf_appstar]
QED

Theorem principle_hnf_denude_thm :
    !l M vs y args. solvable M /\
       ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M) /\
       principle_hnf M = LAMl vs (VAR y @* args) ==>
       principle_hnf (M @* MAP VAR vs @* MAP VAR l) = VAR y @* args @* MAP VAR l
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> qabbrev_tac ‘M0 = principle_hnf M’
 (* applying principle_hnf_thm' *)
 >> Know ‘principle_hnf M = M0’ >- rw [Abbr ‘M0’]
 >> simp [principle_hnf_thm', hnf_appstar]
 >> DISCH_TAC
 >> Know ‘solvable (M @* MAP VAR vs @* MAP VAR l)’
 >- (MATCH_MP_TAC principle_hnf_denude_solvable \\
     qexistsl_tac [‘y’, ‘args’] \\
     Q.PAT_X_ASSUM ‘M0 = _’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     rw [Abbr ‘M0’])
 >> DISCH_TAC
 (* applying again principle_hnf_thm' *)
 >> simp [principle_hnf_thm', hnf_appstar]
 (* now all ‘principle_hnf’ are eliminated, leaving only -h->* *)
 >> MATCH_MP_TAC principle_hnf_denude_lemma >> art []
QED

(* |- !M vs y args.
        solvable M /\ ALL_DISTINCT vs /\ DISJOINT (set vs) (FV M) /\
        principle_hnf M = LAMl vs (VAR y @* args) ==>
        principle_hnf (M @* MAP VAR vs) = VAR y @* args
 *)
Theorem principle_hnf_denude_thm' =
        principle_hnf_denude_thm |> Q.SPEC ‘[]’ |> SIMP_RULE (srw_ss()) []

Theorem principle_hnf_permutator_lemma[local] :
    !vs Ns. ALL_DISTINCT vs /\ ~MEM y vs /\ LENGTH vs = LENGTH Ns /\
            EVERY (\e. DISJOINT (FV e) (set (SNOC y vs))) (SNOC N Ns) ==>
            LAMl vs (LAM y (VAR y @* MAP VAR vs)) @* Ns @@ N -h->* N @* Ns
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [GSYM LAMl_SNOC, GSYM appstar_SNOC]
 >> qabbrev_tac ‘vs' = SNOC y vs’
 >> qabbrev_tac ‘Ns' = SNOC N Ns’
 >> qabbrev_tac ‘t = VAR y @* MAP VAR vs’
 >> Suff ‘N @* Ns = fromPairs vs' Ns' ' t’
 >- (Rewr' >> REWRITE_TAC [fromPairs_def] \\
     MATCH_MP_TAC hreduce_LAMl_appstar \\
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
 >> Know ‘EL i vs = EL i vs' /\ EL i Ns = EL i Ns'’
 >- ASM_SIMP_TAC std_ss [EL_SNOC, Abbr ‘vs'’, Abbr ‘Ns'’]
 >> rw []
 >> MATCH_MP_TAC fromPairs_FAPPLY_EL
 >> rw [Abbr ‘vs'’, Abbr ‘Ns'’, ALL_DISTINCT_SNOC]
QED

Theorem principle_hnf_permutator :
    !n N Ns. hnf N /\ ~is_abs N /\ LENGTH Ns = n ==>
             principle_hnf (permutator n @* Ns @@ N) = N @* Ns
Proof
    rpt STRIP_TAC
 >> Know ‘solvable (permutator n @* Ns @@ N)’
 >- (‘permutator n @* Ns @@ N == N @* Ns’
       by PROVE_TAC [permutator_thm] \\
     Suff ‘solvable (N @* Ns)’ >- PROVE_TAC [lameq_solvable_cong] \\
     REWRITE_TAC [solvable_iff_has_hnf] \\
     MATCH_MP_TAC hnf_has_hnf \\
     rw [hnf_appstar])
 >> DISCH_TAC
 >> rw [principle_hnf_thm', hnf_appstar]
 >> RW_TAC std_ss [permutator_def]
 >> qabbrev_tac ‘n = LENGTH Ns’
 >> ‘ALL_DISTINCT Z /\ LENGTH Z = n + 1’
       by (rw [Abbr ‘Z’, ALL_DISTINCT_GENLIST])
 >> ‘Z <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> ‘MEM z Z’ by rw [Abbr ‘z’, MEM_LAST_NOT_NIL]
 >> qabbrev_tac ‘M = VAR z @* MAP VAR (FRONT Z)’
 (* preparing for LAMl_ALPHA_ssub *)
 >> qabbrev_tac ‘Y = FRESH_list (n + 1)
                       (set Z UNION (FV N) UNION (BIGUNION (IMAGE FV (set Ns))))’
 >> ‘FINITE (set Z UNION (FV N) UNION (BIGUNION (IMAGE FV (set Ns))))’
       by (rw [] >> rw [FINITE_FV])
 >> Know ‘ALL_DISTINCT Y /\
          DISJOINT (set Y) (set Z UNION (FV N) UNION (BIGUNION (IMAGE FV (set Ns)))) /\
          LENGTH Y = n + 1’
 >- (ASM_SIMP_TAC std_ss [FRESH_list_def, Abbr ‘Y’])
 >> rw [] (* this breaks all unions in the DISJOINT *)
 (* applying LAMl_ALPHA_ssub *)
 >> Know ‘LAMl Z M = LAMl Y ((FEMPTY |++ ZIP (Z,MAP VAR Y)) ' M)’
 >- (MATCH_MP_TAC LAMl_ALPHA_ssub >> rw [DISJOINT_SYM] \\
     Suff ‘FV M = set Z’ >- METIS_TAC [DISJOINT_SYM] \\
     rw [Abbr ‘M’, FV_appstar] \\
    ‘Z = SNOC (LAST Z) (FRONT Z)’ by PROVE_TAC [SNOC_LAST_FRONT] \\
     POP_ORW \\
     simp [LIST_TO_SET_SNOC] \\
     rw [Once EXTENSION, MEM_MAP] \\
     EQ_TAC >> rw [] >> fs [] \\
     DISJ2_TAC \\
     Q.EXISTS_TAC ‘FV (VAR x)’ >> rw [] \\
     Q.EXISTS_TAC ‘VAR x’ >> rw [])
 >> Rewr'
 >> ‘Y <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> REWRITE_TAC [GSYM fromPairs_def]
 >> qabbrev_tac ‘fm = fromPairs Z (MAP VAR Y)’
 >> ‘FDOM fm = set Z’ by rw [FDOM_fromPairs, Abbr ‘fm’]
 >> qabbrev_tac ‘y = LAST Y’
 (* postfix for LAMl_ALPHA_ssub *)
 >> ‘!t. LAMl Y t = LAMl (SNOC y (FRONT Y)) t’
       by (ASM_SIMP_TAC std_ss [Abbr ‘y’, SNOC_LAST_FRONT]) >> POP_ORW
 >> REWRITE_TAC [LAMl_SNOC]
 >> Know ‘fm ' M = VAR y @* MAP VAR (FRONT Y)’
 >- (simp [Abbr ‘M’, ssub_appstar] \\
     Know ‘fm ' z = VAR y’
     >- (rw [Abbr ‘fm’, Abbr ‘z’, LAST_EL] \\
         Know ‘fromPairs Z (MAP VAR Y) ' (EL (PRE (n + 1)) Z) =
               EL (PRE (n + 1)) (MAP VAR Y)’
         >- (MATCH_MP_TAC fromPairs_FAPPLY_EL >> rw []) >> Rewr' \\
         rw [EL_MAP, Abbr ‘y’, LAST_EL]) >> Rewr' \\
     Suff ‘MAP ($' fm) (MAP VAR (FRONT Z)) = MAP VAR (FRONT Y)’ >- rw [] \\
     rw [LIST_EQ_REWRITE, LENGTH_FRONT] \\
    ‘PRE (n + 1) = n’ by rw [] >> POP_ASSUM (fs o wrap) \\
     rename1 ‘i < n’ \\
     simp [EL_MAP, LENGTH_FRONT] \\
     Know ‘MEM (EL i (FRONT Z)) Z’
     >- (rw [MEM_EL] \\
         Q.EXISTS_TAC ‘i’ >> rw [] \\
         MATCH_MP_TAC EL_FRONT >> rw [LENGTH_FRONT, NULL_EQ]) \\
     rw [Abbr ‘fm’] \\
     Know ‘EL i (FRONT Z) = EL i Z’
     >- (MATCH_MP_TAC EL_FRONT >> rw [LENGTH_FRONT, NULL_EQ]) >> Rewr' \\
     Know ‘EL i (FRONT Y) = EL i Y’
     >- (MATCH_MP_TAC EL_FRONT >> rw [LENGTH_FRONT, NULL_EQ]) >> Rewr' \\
     Know ‘fromPairs Z (MAP VAR Y) ' (EL i Z) = EL i (MAP VAR Y)’
     >- (MATCH_MP_TAC fromPairs_FAPPLY_EL >> rw []) >> Rewr' \\
     rw [EL_MAP])
 >> Rewr'
 >> qabbrev_tac ‘vs = FRONT Y’
 >> Know ‘ALL_DISTINCT vs /\ ~MEM y vs’
 >- (Q.PAT_X_ASSUM ‘ALL_DISTINCT Y’ MP_TAC \\
    ‘Y = SNOC y vs’ by METIS_TAC [SNOC_LAST_FRONT] >> POP_ORW \\
     rw [ALL_DISTINCT_SNOC])
 >> STRIP_TAC
 >> MATCH_MP_TAC principle_hnf_permutator_lemma
 >> ‘SNOC y vs = Y’ by METIS_TAC [SNOC_LAST_FRONT] >> POP_ORW
 >> rw [EVERY_MEM, Abbr ‘vs’, LENGTH_FRONT] >- art []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘e’ >> art []
QED

Theorem principle_hnf_tpm :
    !pi M. has_hnf M ==> principle_hnf (tpm pi M) = tpm pi (principle_hnf M)
Proof
    rpt GEN_TAC >> DISCH_TAC
 >> qabbrev_tac ‘N = principle_hnf M’
 >> Know ‘principle_hnf M = N’ >- rw [Abbr ‘N’]
 >> DISCH_THEN (STRIP_ASSUME_TAC o
                (REWRITE_RULE [MATCH_MP principle_hnf_thm (ASSUME “has_hnf M”)]))
 >> ‘solvable (tpm pi M)’ by rw [solvable_tpm, solvable_iff_has_hnf]
 >> rw [principle_hnf_thm']
QED

Theorem principle_hnf_tpm' =
        principle_hnf_tpm |> REWRITE_RULE [GSYM solvable_iff_has_hnf]

val _ = export_theory ();
val _ = html_theory "solvable";

(* References:

   [1] Barendregt, H.P.: The Lambda Calculus, Its Syntax and Semantics.
       College Publications, London (1984).
   [2] Hankin, C.: Lambda Calculi: A Guide for Computer Scientists.
       Clarendon Press, Oxford (1994).
 *)
