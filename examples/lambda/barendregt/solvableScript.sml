(*---------------------------------------------------------------------------*
 * solvableScript.sml (or chap8_3): Theory of Solvable Lambda Terms          *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;

(* core theories *)
open arithmeticTheory pred_setTheory listTheory rich_listTheory sortingTheory
     finite_mapTheory pathTheory hurdUtils;

(* lambda theories *)
open binderLib nomsetTheory termTheory appFOLDLTheory chap2Theory chap3Theory
     reductionEval standardisationTheory head_reductionTheory;

val _ = new_theory "solvable";

(*---------------------------------------------------------------------------*
 * closed terms and closures of (open or closed) terms
 *---------------------------------------------------------------------------*)

(* By prefixing a list of abstractions of FVs, any term can be "closed". The
   set ‘closures M’ represent such closures with different order of FVs.
 *)
Definition closures_def :
    closures M = {LAMl vs M | vs | ALL_DISTINCT vs /\ set vs = FV M}
End

Theorem closures_not_empty :
    !M. closures M <> {}
Proof
    Q.X_GEN_TAC ‘M’
 >> rw [GSYM MEMBER_NOT_EMPTY]
 >> Q.EXISTS_TAC ‘LAMl (SET_TO_LIST (FV M)) M’
 >> rw [closures_def]
 >> Q.EXISTS_TAC ‘SET_TO_LIST (FV M)’
 >> rw [SET_TO_LIST_INV]
QED

Theorem closures_of_closed[simp] :
    !M. closed M ==> closures M = {M}
Proof
    rw [closures_def, closed_def]
 >> rw [Once EXTENSION]
QED

Theorem closures_of_open_sing :
    !M v. FV M = {v} ==> closures M = {LAM v M}
Proof
    rw [closures_def, LIST_TO_SET_SING]
 >> rw [Once EXTENSION]
QED

(* ‘closure M’ is just one arbitrary element in ‘closures M’. *)
Overload closure = “\M. CHOICE (closures M)”

Theorem closure_in_closures :
    !M. closure M IN closures M
Proof
    rw [CHOICE_DEF, closures_not_empty]
QED

Theorem closure_idem[simp] :
    !M. closed M ==> closure M = M
Proof
    rw [closures_of_closed]
QED

Theorem closure_open_sing :
    !M v. FV M = {v} ==> closure M = LAM v M
Proof
    rpt STRIP_TAC
 >> ‘closures M = {LAM v M}’ by PROVE_TAC [closures_of_open_sing]
 >> rw []
QED

(*---------------------------------------------------------------------------*
 * solvable terms and some equivalent definitions
 *---------------------------------------------------------------------------*)

(* 8.3.1 (ii) [1, p.171] *)
Definition solvable_def :
    solvable (M :term) = ?M' Ns. M' IN closures M /\ M' @* Ns == I
End

(* 8.3.1 (i) [1, p.171] *)
Theorem solvable_alt_closed :
    !M. closed M ==> (solvable M <=> ?Ns. M @* Ns == I)
Proof
    rw [solvable_def, closed_def]
QED

(* |- !M. FV M = {} ==> (solvable M <=> ?Ns. M @* Ns == I) *)
Theorem solvable_alt_closed'[local] =
    REWRITE_RULE [closed_def] solvable_alt_closed

(* 8.3.1 (iii) [1, p.171] *)
Overload unsolvable = “\M. ~(solvable M)”

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

Theorem closure_VAR[simp] :
    closure (VAR x) = I
Proof
    Know ‘closure (VAR x) = LAM x (VAR x)’
 >- (MATCH_MP_TAC closure_open_sing >> rw [])
 >> Rewr'
 >> REWRITE_TAC [Q.SPEC ‘x’ I_alt]
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
     MATCH_MP_TAC lameq_LAMl_appstar >> rw [])
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
 (* preparing for lameq_LAMl_appstar *)
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
 >- (MATCH_MP_TAC lameq_LAMl_appstar >> art [] \\
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
     MATCH_MP_TAC lameq_LAMl_appstar >> rw [])
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
     MATCH_MP_TAC lameq_LAMl_appstar >> rw [])
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
        >- (MATCH_MP_TAC ssub_update_apply' \\
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
 >- (Q.UNABBREV_TAC ‘M0’ \\
     KILL_TAC >> Induct_on ‘vs’ >- rw [] \\
     rw [solvable_iff_LAM, has_hnf_LAM_E])
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
 (* applying lameq_LAMl_appstar and ssub_appstar *)
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘(FEMPTY |++ ZIP (vs,Ms)) ' (VAR y @* Ns)’
 >> CONJ_TAC
 >- (MATCH_MP_TAC lameq_LAMl_appstar >> art [] \\
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

(* Definition 8.3.20 [1, p.177]

   A term may have several hnf's, e.g. if any of its hnf can still do beta
   reductions, after such reductions the term is still an hnf by definition.
   The (unique) terminating term of head reduction path is called "principle"
   hnf, which is used for defining Boehm trees.
 *)
Definition principle_hnf_def :
    principle_hnf = last o head_reduction_path
End

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

Theorem principle_hnf_eq_self :
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
 >> MATCH_MP_TAC principle_hnf_eq_self
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
 >- (qunabbrevl_tac [‘M’, ‘N’] \\
     rw [Once hreduce1_cases] \\
     qexistsl_tac [‘v’, ‘t’] >> rw [])
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

Theorem principle_hnf_LAMl_appstar_lemma[local] :
    !t. hnf t /\
        ALL_DISTINCT (MAP FST pi) /\
        ALL_DISTINCT (MAP SND pi) /\
        DISJOINT (set (MAP FST pi)) (set (MAP SND pi)) /\
       (!y. MEM y (MAP SND pi) ==> y # t) ==>
        principle_hnf (LAMl (MAP FST pi) t @* MAP VAR (MAP SND pi)) = tpm pi t
Proof
    Induct_on ‘pi’ (* using SNOC_INDUCT *)
 >- rw [principle_hnf_eq_self]
 >> rw [] (* rw [FOLDR_SNOC, MAP_SNOC] *)
 >> Cases_on ‘h’ (* ‘x’ *) >> fs []
 >> qabbrev_tac ‘M = LAMl (MAP FST pi) t’
 >> ‘hnf M’ by rw [Abbr ‘M’, hnf_LAMl]
 >> qabbrev_tac ‘args :term list = MAP VAR (MAP SND pi)’
 >> Know ‘principle_hnf (LAM q M @@ VAR r @* args) =
          principle_hnf ([VAR r/q] M @* args)’
 >- (MATCH_MP_TAC principle_hnf_hreduce1 \\
     MATCH_MP_TAC hreduce1_rules_appstar >> simp [] \\
     rw [Once hreduce1_cases] \\
     qexistsl_tac [‘q’, ‘M’] >> rw [])
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

(* ‘principle_hnf’ can be used to do final beta-reductions to make a hnf abs-free

   NOTE: to satisfy ‘DISJOINT (set xs) (set ys)’, one first get ‘LENGTH xs’
         without knowing ‘xs’ (e.g. by ‘LAMl_size’), then generate ‘ys’ by
        ‘FRESH_list’, and then call ‘hnf_cases’ (more general version) using ‘ys’
         as the excluded list.
 *)
Theorem principle_hnf_LAMl_appstar :
    !t xs ys. hnf t /\
              ALL_DISTINCT xs /\ ALL_DISTINCT ys /\
              LENGTH xs = LENGTH ys /\
              DISJOINT (set xs) (set ys) /\
              DISJOINT (set ys) (FV t)
          ==> principle_hnf (LAMl xs t @* (MAP VAR ys)) = tpm (ZIP (xs,ys)) t
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

val _ = export_theory ();
val _ = html_theory "solvable";

(* References:

   [1] Barendregt, H.P.: The Lambda Calculus, Its Syntax and Semantics.
       College Publications, London (1984).
   [2] Hankin, C.: Lambda Calculi: A Guide for Computer Scientists.
       Clarendon Press, Oxford (1994).
 *)
