open HolKernel Parse bossLib boolLib pairTheory relationTheory set_relationTheory pred_setTheory arithmeticTheory

open alterATheory

val _ = new_theory "waaSimpl"

(*
  Reducing the amount of transitions
*)

val trans_implies_def = Define`
  trans_implies (a1,q1) (a2,q2) = a2 ⊆ a1 ∧ q1 ⊆ q2`;

val TRANS_IMPL_PO = store_thm
  ("TRANS_IMPL_PO",
  ``!d. partial_order (rrestrict (rel_to_reln trans_implies) d) d``,
  fs[partial_order_def, rrestrict_def, rel_to_reln_def] >> rpt strip_tac
    >- (fs[domain_def,SUBSET_DEF] >> rpt strip_tac)
    >- (fs[range_def, SUBSET_DEF] >> rpt strip_tac)
    >- (fs[transitive_def,SUBSET_DEF,trans_implies_def] >> rpt strip_tac
        >> Cases_on `x` >> Cases_on `y` >> Cases_on `z`
        >> fs[trans_implies_def] >> metis_tac[SUBSET_TRANS])
    >- (fs[reflexive_def,SUBSET_DEF,trans_implies_def] >> rpt strip_tac
        >> Cases_on `x` >> fs[trans_implies_def] >> metis_tac[SUBSET_REFL])
    >- (fs[antisym_def,SUBSET_DEF,trans_implies_def] >> rpt strip_tac
        >> Cases_on `x` >> Cases_on `y`
        >> fs[trans_implies_def] >> metis_tac[SUBSET_ANTISYM])
  );

val TRANS_IMPL_FINITE = store_thm
  ("TRANS_IMPL_FINITE",
   ``!d. FINITE d ==> finite_prefixes (rrestrict (rel_to_reln trans_implies) d) d``,
   fs[finite_prefixes_def, rrestrict_def, rel_to_reln_def] >> rpt strip_tac
   >> `FINITE {e' | e' ∈ (\x. trans_implies x e) ∧ e' ∈ d }` suffices_by fs[IN_DEF]
   >> metis_tac[INTER_DEF, INTER_FINITE,INTER_COMM]
  );

val TRANS_IMPL_MIN_LEMM = store_thm
  ("TRANS_IMPL_MIN_LEMM",
   ``!run q aut w i. validAARunFor aut run w ∧ q ∈ run.V i ∧ isValidAlterA aut
  ∧ FINITE aut.states ∧ FINITE aut.alphabet
  ==> ?t. t ∈ minimal_elements (aut.trans q)
  (rrestrict (rel_to_reln trans_implies) (aut.trans q)) ∧
  trans_implies t
  ((@a. (a,run.E (i,q)) ∈ aut.trans q ∧ at w i ∈ a),
   run.E (i,q))``,
    rpt strip_tac
    >> `FINITE (aut.trans q)`
        by metis_tac[FINITE_LEMM,SUBSET_DEF,validAARunFor_def]
    >> qabbrev_tac `a' = (@a. (a,run.E (i,q)) ∈ aut.trans q ∧ at w i ∈ a)`
    >> qabbrev_tac `trans_impl_r = (rrestrict (rel_to_reln trans_implies) (aut.trans q))`
    >> `?t. t ∈ minimal_elements (aut.trans q) trans_impl_r ∧
              (t, (a',run.E (i,q))) ∈ trans_impl_r` suffices_by (
         qunabbrev_tac `trans_impl_r` >> qunabbrev_tac `a'`
         >> fs[rrestrict_def, rel_to_reln_def] >> rpt strip_tac
         >> metis_tac[]
    )
    >> Cases_on `(a', run.E (i,q)) ∈ minimal_elements (aut.trans q) trans_impl_r`
     >- (qexists_tac `(a', run.E (i,q))` >> qunabbrev_tac `trans_impl_r`
         >> fs[rrestrict_def, rel_to_reln_def, trans_implies_def]
         >> qunabbrev_tac `a'`
         >> fs[validAARunFor_def]
         >> metis_tac[SELECT_THM,SUBSET_DEF]
        )
     >-(HO_MATCH_MP_TAC finite_prefix_po_has_minimal_path
        >> qexists_tac `aut.trans q`
        >> fs[validAARunFor_def] >> qunabbrev_tac `a'`
        >> qunabbrev_tac `trans_impl_r`
        >> metis_tac[SUBSET_DEF,SELECT_THM,TRANS_IMPL_FINITE,TRANS_IMPL_PO]
       )
  );

val removeImplied_def = Define`
  removeImplied trans x =
    (trans x) DIFF {t | ?t'. ~(t = t') ∧ t' ∈ (trans x) ∧ trans_implies t' t}`;

val reduceTransSimpl_def = Define`
  reduceTransSimpl (ALTER_A s i f a trans) =
    ALTER_A s i f a (removeImplied trans)`;

val REDUCE_IS_WEAK = store_thm
  ("REDUCE_IS_WEAK",
   ``!aut. isWeakAlterA aut ==> isWeakAlterA (reduceTransSimpl aut)``,
   rpt strip_tac >> fs[isWeakAlterA_def] >> qexists_tac `ord`
   >> fs[isWeakWithOrder_def] >> Cases_on `aut` >> fs[reduceTransSimpl_def]
   >> fs[removeImplied_def] >> metis_tac[]
  );

val reduced_E_def = Define`
  reduced_E run trans word (i,q) =
    let a = $@ (\a. (a,run.E (i,q)) ∈ trans q ∧ at word i ∈ a)
    in if ?a' q'. (a',q') ∈ trans q ∧ trans_implies (a',q') (a,run.E (i,q))
       then SND
        ($@ \t. (t ∈ minimal_elements
                    (trans q)
                    (rrestrict (rel_to_reln trans_implies) (trans q)))
           ∧ trans_implies t (a,run.E (i,q)))
       else run.E(i,q)`;

val reduced_run_def = Define`
  reduced_run run w trans =
            run_restr (run.V 0) (ALTERA_RUN run.V (reduced_E run trans w))`;

val REDUCE_TRANS_CORRECT = store_thm
  ("REDUCE_TRANS_CORRECT",
   ``!aut. FINITE aut.states ∧ FINITE aut.alphabet ∧ isValidAlterA aut
         ∧ isWeakAlterA aut
      ==> (alterA_lang aut = alterA_lang (reduceTransSimpl aut))``,
   rw[SET_EQ_SUBSET, SUBSET_DEF] >> rpt strip_tac >> fs[alterA_lang_def]
    >- (qexists_tac `reduced_run run x aut.trans` >> fs[runForAA_def]
        >> `(validAARunFor (reduceTransSimpl aut) (reduced_run run x aut.trans) x ∧
           (validAARunFor (reduceTransSimpl aut) (reduced_run run x aut.trans) x
             ==> acceptingAARun (reduceTransSimpl aut) (reduced_run run x aut.trans))) ∧
                    word_range x ⊆ (reduceTransSimpl aut).alphabet` suffices_by fs[]
        >> rpt strip_tac
        >> `!i. (reduced_run run x aut.trans).V i ⊆ run.V i` by (
             Induct_on `i` >> simp[SUBSET_DEF] >> rpt strip_tac
             >> fs[reduced_run_def, run_restr_def, run_restr_V_def,reduced_E_def]
             >> Cases_on `∃a' q'.
                         (a',q') ∈ aut.trans q ∧
                         trans_implies (a',q')
                         ((@a. (a,run.E (i,q)) ∈ aut.trans q ∧ at x i ∈ a),
                          run.E (i,q))`
             >> fs[]
             >> qabbrev_tac `minE = \t. t ∈ minimal_elements (aut.trans q)
                                     (rrestrict (rel_to_reln trans_implies) (aut.trans q)) ∧
                                     trans_implies t
                                     ((@a. (a,run.E (i,q)) ∈ aut.trans q ∧ at x i ∈ a),
                                      run.E (i,q))`
             >- (`?t. minE t` by (
                   qunabbrev_tac `minE`
                   >> `q ∈ run.V i` by fs[SUBSET_DEF] >> fs[]
                   >> HO_MATCH_MP_TAC TRANS_IMPL_MIN_LEMM >> fs[]
                 )
                   >> Cases_on `$@ minE`
                   >> `minE (q'',r)` by metis_tac[SELECT_THM]
                   >> qunabbrev_tac `minE`
                   >> fs[minimal_elements_def, rrestrict_def, rel_to_reln_def]
                   >> fs[validAARunFor_def,trans_implies_def]
                   >> metis_tac[SUC_ONE_ADD,ADD_COMM,SUBSET_TRANS,SUBSET_DEF]
                )
             >- (fs[validAARunFor_def] >> metis_tac[SUC_ONE_ADD,ADD_COMM,SUBSET_DEF])
         )
         >- (simp[validAARunFor_def] >> rpt strip_tac
              >- (Cases_on `aut`
                  >> fs[validAARunFor_def,reduced_run_def,run_restr_def,run_restr_V_def]
                  >> fs[reduceTransSimpl_def])
              >- (`run.V i ⊆ (reduceTransSimpl aut).states`
                    suffices_by metis_tac[SUBSET_TRANS]
                  >> Cases_on `aut` >> simp[reduceTransSimpl_def]
                  >> fs[validAARunFor_def]
                 )
              >- (simp[reduced_run_def, reduced_E_def,run_restr_def,run_restr_E_def]
                  >> fs[reduced_run_def]
                  >> Cases_on `∃a' q'.
                                 (a',q') ∈ aut.trans q ∧
                                 trans_implies (a',q')
                                 ((@a. (a,run.E (i,q)) ∈ aut.trans q ∧ at x i ∈ a),
                                  run.E (i,q))`
                   >- (fs[] >> rw[]
                       >> qabbrev_tac `minE =
                           \t. (t ∈ minimal_elements (aut.trans q)
                           (rrestrict (rel_to_reln trans_implies) (aut.trans q))) ∧
                           trans_implies t
                           ((@a. (a,run.E (i,q)) ∈ aut.trans q ∧ at x i ∈ a),
                            run.E (i,q))`
                       >> `?t. minE t` by (
                            qunabbrev_tac `minE`
                            >> `q ∈ run.V i` by fs[SUBSET_DEF] >> fs[]
                            >> HO_MATCH_MP_TAC TRANS_IMPL_MIN_LEMM >> fs[]
                        )
                       >> fs[run_restr_def]
                       >> Cases_on `$@ minE` >> fs[SND]
                       >> `minE (q''',r)` by metis_tac[SELECT_THM]
                       >> qunabbrev_tac `minE` >> fs[minimal_elements_def,rrestrict_def]
                       >> fs[rel_to_reln_def, trans_implies_def]
                       >> qabbrev_tac `a''' =
                              (@a. (a,run.E (i,q)) ∈ aut.trans q ∧ at x i ∈ a)`
                       >> `(a''', run.E (i,q)) ∈ aut.trans q ∧ at x i ∈ a'''` by (
                            fs[validAARunFor_def]
                            >> `q ∈ run.V i` by metis_tac[SUBSET_DEF]
                            >> metis_tac[SELECT_THM,IN_DEF]
                        )
                       >- (qexists_tac `q'''` >> Cases_on `aut` >> fs[reduceTransSimpl_def]
                           >> fs[removeImplied_def]
                           >> rpt strip_tac
                            >- (CCONTR_TAC >> fs[] >> metis_tac[])
                            >- metis_tac[SUBSET_TRANS,SUBSET_DEF])
                       >- metis_tac[]
                      )
                   >- (simp[] >> fs[run_restr_def] >> simp[]
                       >> Cases_on `aut` >> simp[reduceTransSimpl_def, removeImplied_def]
                       >> `?a. (a, run.E (i,q)) ∈ f3 q ∧ at x i ∈ a` by (
                              fs[validAARunFor_def] >> metis_tac[SUBSET_DEF]
                        )
                       >> qabbrev_tac `a' = (@a. (a,run.E (i,q)) ∈ f3 q ∧ at x i ∈ a)`
                       >> `(a', run.E (i,q)) ∈ f3 q ∧ at x i ∈ a'` by metis_tac[SELECT_THM]
                       >> qexists_tac `a'` >> rpt strip_tac >> fs[]
                       >> Cases_on `t'` >> metis_tac[]
                      )
                 )
              >- (simp[SUBSET_DEF, reduced_run_def] >> rpt strip_tac
                  >> fs[run_restr_def, run_restr_E_def]
                  >> rw[run_restr_V_def, DECIDE ``i + 1 = SUC i``]
                  >> metis_tac[MEMBER_NOT_EMPTY]
                 )
              >- (Cases_on `i = 0` >> fs[]
                  >> `?j. i = SUC j` by (Cases_on `i` >> fs[])
                  >> fs[reduced_run_def, run_restr_def, run_restr_V_def]
                  >> simp[run_restr_E_def]
                  >> metis_tac[]
                 )
            )
         >- (`∀b f. infBranchOf (reduced_run run x aut.trans) b
                ∧ branchFixP b f ⇒ f ∉ (reduceTransSimpl aut).final` suffices_by (
                 `isWeakAlterA (reduceTransSimpl aut)` by metis_tac[REDUCE_IS_WEAK]
                 >> `FINITE (reduceTransSimpl aut).states` by
                      (Cases_on `aut` >> fs[reduceTransSimpl_def])
                 >> metis_tac[BRANCH_ACC_LEMM]
             )
             >> `∀b f. infBranchOf run b ∧ branchFixP b f ⇒ f ∉ aut.final`
                by metis_tac[BRANCH_ACC_LEMM]
             >> `!b. infBranchOf (reduced_run run x aut.trans) b
                ==> infBranchOf run b` by (
                rpt strip_tac >> simp[infBranchOf_def] >> rpt strip_tac
                    >- metis_tac[infBranchOf_def,SUBSET_DEF]
                    >- (`!i. b i ∈ run.V i` by (
                          rpt strip_tac >> fs[infBranchOf_def,validAARunFor_def]
                          >> Cases_on `i = 0` >> fs[SUBSET_DEF]
                          >> `?j. i = j + 1` by (
                              Cases_on `i` >> metis_tac[SUC_ONE_ADD, ADD_COMM]
                          )
                          >> metis_tac[]
                        )
                        >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
                        >> simp[infBranchOf_def, reduced_run_def]
                        >> simp[run_restr_def, run_restr_E_def] >> rpt strip_tac
                        >> POP_ASSUM mp_tac
                        >> first_x_assum (qspec_then `i` mp_tac) >> rpt strip_tac
                        >> `b (i+1) ∈ reduced_E run aut.trans x (i, b i)`
                           by metis_tac[MEMBER_NOT_EMPTY]
                        >> POP_ASSUM mp_tac >> simp[reduced_E_def] >> rpt strip_tac
                        >> Cases_on `∃a' q'.
                                      (a',q') ∈ aut.trans (b i) ∧
                                      trans_implies (a',q')
                                      ((@a. (a,run.E (i,b i)) ∈ aut.trans (b i)
                                            ∧ at x i ∈ a),
                                       run.E (i,b i))`
                          >- (fs[]
                              >> qabbrev_tac `minE = \t.
                                    t ∈
                                      minimal_elements (aut.trans (b i))
                                      (rrestrict (rel_to_reln trans_implies)
                                                 (aut.trans (b i))) ∧
                                      trans_implies t
                                      ((@a. (a,run.E (i,b i)) ∈ aut.trans (b i)
                                            ∧ at x i ∈ a),
                                       run.E (i,b i))`
                              >> `?t. minE t` by (
                                   qunabbrev_tac `minE` >> fs[]
                                   >> HO_MATCH_MP_TAC TRANS_IMPL_MIN_LEMM >> fs[]
                               )
                              >> `minE ($@ minE)` by metis_tac[SELECT_THM]
                              >> Cases_on `$@ minE`
                              >> `r ⊆ run.E (i,b i)` suffices_by metis_tac[SUBSET_DEF,SND]
                              >> qunabbrev_tac `minE` >> fs[minimal_elements_def]
                              >> fs[rrestrict_def, rel_to_reln_def,trans_implies_def]
                             )
                          >- metis_tac[]
                       )
             )
             >> rpt strip_tac >> `f ∈ aut.final` suffices_by metis_tac[]
             >> Cases_on `aut` >> fs[reduceTransSimpl_def]
            )
         >- (Cases_on `aut` >> fs[reduceTransSimpl_def])
       )
    >- (qexists_tac `run` >> fs[runForAA_def]
        >> `(validAARunFor aut run x ∧ (validAARunFor aut run x ==> acceptingAARun aut run))
          ∧ word_range x ⊆ aut.alphabet` suffices_by fs[]
        >> rpt strip_tac
         >- (simp[validAARunFor_def] >> rpt strip_tac
             >- (Cases_on `aut` >> fs[validAARunFor_def, reduceTransSimpl_def])
             >- (Cases_on `aut` >> fs[validAARunFor_def, reduceTransSimpl_def])
             >- (Cases_on `aut` >> fs[validAARunFor_def, reduceTransSimpl_def]
                 >> metis_tac[removeImplied_def,IN_DIFF])
             >- (Cases_on `aut` >> fs[validAARunFor_def, reduceTransSimpl_def])
             >- (Cases_on `aut` >> fs[validAARunFor_def, reduceTransSimpl_def])
            )
         >- (`∀b x. infBranchOf run b ∧ branchFixP b x ⇒ x ∉ aut.final`
               suffices_by metis_tac[BRANCH_ACC_LEMM]
             >> `FINITE (reduceTransSimpl aut).states` by
                    (Cases_on `aut` >> fs[reduceTransSimpl_def])
             >> `aut.final = (reduceTransSimpl aut).final` by
                  (Cases_on `aut` >> fs[reduceTransSimpl_def])
             >> metis_tac[BRANCH_ACC_LEMM,REDUCE_IS_WEAK]
            )
         >- (Cases_on `aut` >> fs[reduceTransSimpl_def])
       )
  );

(*
  Remove unreachable states
*)

val nStepReachable_def = Define`
   (nStepReachable trans init 0 = init)
 ∧ (nStepReachable trans init (SUC i) =
    {s | ?a qs s'. (a, qs) ∈ trans s' ∧ s' ∈ nStepReachable trans init i
          ∧ s ∈ qs})`;

val reachable_def = Define`
  (reachable trans init = {s | ?n. s ∈ nStepReachable trans init n })`;

val removeStatesSimpl_def = Define`
  removeStatesSimpl (ALTER_A s i f a t) =
            (ALTER_A (s ∩ reachable t (BIGUNION i)) i f a t)`;

val REDUCE_STATE_CORRECT = store_thm
  ("REDUCE_STATE_CORRECT",
   ``!aut. alterA_lang aut = alterA_lang (removeStatesSimpl aut)``,
   rw[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> fs[alterA_lang_def]
     >- (qexists_tac `run` >> fs[runForAA_def] >> rpt strip_tac
          >- (simp[validAARunFor_def] >> rpt strip_tac
             >- (Cases_on `aut` >> fs[validAARunFor_def, removeStatesSimpl_def])
             >- (Cases_on `aut` >> fs[validAARunFor_def, removeStatesSimpl_def]
                 >> `!n. run.V n ⊆ reachable f3 (BIGUNION f0)` by (
                      Induct_on `n`
                      >- (fs[reachable_def, nStepReachable_def]
                          >> simp[SUBSET_DEF] >> rpt strip_tac
                          >> qexists_tac `0` >> simp[nStepReachable_def]
                          >> metis_tac[]
                         )
                      >- (simp[SUBSET_DEF,reachable_def] >> rpt strip_tac
                          >> fs[reachable_def]
                          >> `!x. x ∈ run.V n ==> ?n. x ∈ nStepReachable f3 (BIGUNION f0) n`
                              by fs[SUBSET_DEF]
                          >> first_x_assum (qspec_then `SUC n` mp_tac) >> rpt strip_tac
                          >> first_x_assum (qspec_then `x'` mp_tac) >> rpt strip_tac
                          >> fs[] >> `∃q'. x' ∈ run.E (n,q') ∧ q' ∈ run.V n` by fs[]
                          >> `∃n. q' ∈ nStepReachable f3 (BIGUNION f0) n` by fs[]
                          >> qexists_tac `SUC n'` >> simp[nStepReachable_def]
                          >> metis_tac[]
                         )
                  ) >> fs[]
                )
             >- (Cases_on `aut` >> fs[validAARunFor_def, removeStatesSimpl_def])
             >- (Cases_on `aut` >> fs[validAARunFor_def, removeStatesSimpl_def])
             >- (Cases_on `aut` >> fs[validAARunFor_def, removeStatesSimpl_def])
             )
          >- (Cases_on `aut` >> fs[acceptingAARun_def, removeStatesSimpl_def])
          >- (Cases_on `aut` >> fs[removeStatesSimpl_def])
        )
     >- (qexists_tac `run` >> fs[runForAA_def] >> rpt strip_tac
         >- (simp[validAARunFor_def] >> rpt strip_tac
             >> Cases_on `aut`
             >> fs[validAARunFor_def, removeStatesSimpl_def])
         >- (Cases_on `aut` >> fs[acceptingAARun_def,removeStatesSimpl_def])
         >- (Cases_on `aut` >> fs[removeStatesSimpl_def])
        )
  );

(*
  Merge equivalent states
*)

val equivalentStates_def = Define`
  equivalentStates final trans s s' =
            (trans s = trans s') ∧ (s ∈ final = s' ∈ final)`;

val replaceSingleTrans_def = Define`
  replaceSingleTrans s s' (a,e) =
            if s ∈ e
            then (a, (e DIFF {s}) ∪ {s'})
            else (a,e)`;

val replaceState_def = Define`
  replaceState s s' qs =
                 if s ∈ qs
                 then qs DIFF {s} ∪ {s'}
                 else qs`;

val REPL_STATE_LEMM = store_thm
  ("REPL_STATE_LEMM",
   ``!x s d1 d2. d1 ⊆ d2 ==> replaceState x s d1 ⊆ replaceState x s d2``,
   rpt strip_tac >> fs[replaceState_def] >> Cases_on `x ∈ d1`
   >> Cases_on `x ∈ d2` >> fs[SUBSET_DEF, IN_DIFF, IN_UNION] >> rpt strip_tac
   >> metis_tac[]
  );

val replaceBy_def = Define`
  replaceBy trans s s' q = IMAGE (replaceSingleTrans s s') (trans q)`;

val mergeState_def = Define`
  mergeState x (ALTER_A states i f a trans) =
            if ?s. s ∈ states ∧ ~(s = x) ∧ equivalentStates f trans s x
            then
                let s' = $@ (\s. s ∈ states ∧ ~(s = x)
                              ∧ equivalentStates f trans s x)
                in ALTER_A
                       (states DIFF {x})
                       (IMAGE (replaceState x s') i)
                       (replaceState x s' f)
                       a
                       (replaceBy trans x s')
            else (ALTER_A states i f a trans)`;

val mergeStatesSimpl = Define`
  mergeStatesSimpl aut = ITSET mergeState aut.states aut`;

(* val MERGE_STATE_COMMUTES = store_thm *)
(*  ("MERGE_STATE_COMMUTES", *)
(*   ``!f x y z. mergeState f x (mergeStates f y z) = *)
(*                  mergeState f y (mergeState f x z)``, *)


(* val ITSET_IND_SPEC_MERGE = store_thm *)
(*   ("ITSET_IND_SPEC_MERGE", *)
(*   ``∀P. *)
(*   (∀s b. *)
(*     (FINITE s ∧ s ≠ ∅ ⇒ P (REST s) ((mergeState final) (CHOICE s) b)) ⇒ P s b) ⇒ *)
(*   ∀v v1. P v v1``, *)
(*   metis_tac[ITSET_IND] *)
(*   ); *)

(* val EQUIV_EXISTS_IN_MERGESET = store_thm *)
(*   ("EQUIV_EXISTS_IN_MERGESET", *)
(*    ``!final states trans x. FINITE states ∧ (x ∈ states) *)
(*   ==> ?x'. (x' ∈ FST (mergeStates final states trans)) *)
(*          ∧ (equivalentStates final trans x x')``, *)
(*      simp[mergeStates_def] >> gen_tac *)
(*      >> `!v v1 trans. FINITE v ==> *)
(*           !x. x ∈ v ==> *)
(*           ?x'. x' ∈ FST (ITSET (mergeState final) v v1) ∧ *)
(*           equivalentStates final trans x x'` by ( *)
(*          HO_MATCH_MP_TAC ITSET_IND_SPEC_MERGE >> rpt strip_tac *)
(*          >> `∀trans x. *)
(*               x ∈ REST v ⇒ *)
(*               ∃x'. x' ∈ FST *)
(*                 (ITSET (mergeState final) (REST v) *)
(*                        (mergeState final (CHOICE v) v1)) ∧ *)
(*                 equivalentStates final trans x x'` *)
(*               by metis_tac[MEMBER_NOT_EMPTY] *)
(*          >> Cases_on `x ∈ REST v` *)
(*            >- metis_tac[ITSET_THM,MEMBER_NOT_EMPTY] *)
(*            >- (rw[ITSET_THM] >> fs[MEMBER_NOT_EMPTY] *)
(*                  >- (Cases_on `v1` >> simp[mergeState_def] *)
(*                      >> Cases_on `∃s. *)
(*                             s ∈ q ∧ (s ≠ CHOICE v) *)
(*                             ∧ equivalentStates final r s (CHOICE v)` *)
(*                       >- (rw[] >> metis_tac[]) *)
(* ) *)

(* ) *)
(*      >> HO_MATCH_MP_TAC ITSET_IND_SPEC_MERGE >> rpt strip_tac *)
(*      >> Cases_on `(states = {})` *)
(*        >- (simp[ITSET_THM] >> metis_tac[MEMBER_NOT_EMPTY]) *)
(*        >- (fs[] *)
(*            >>  *)
(*            >>  *)

(* ) *)

(*    `!states. FINITE states ==> *)
(*          !final trans x. (x ∈ states) *)
(*          ==> ?x'. (x' ∈ FST (mergeStates final states trans)) *)
(*          ∧ (equivalentStates final trans x x')` suffices_by metis_tac[] *)
(*    >> Induct_on `states` >> rpt strip_tac >> fs[mergeStates_def] *)
(*      >- () *)


(* ) *)

val replace_run_def = Define`
  replace_run old_run x_old x_new =
    ALTERA_RUN
        (replaceState x_old x_new o old_run.V)
        (λ(i,q). if (q = x_new) ∧ ~(x_new ∈ old_run.V i)
                 then replaceState x_old x_new (old_run.E (i,x_old))
                 else replaceState x_old x_new (old_run.E (i,q)))`;

val MERGE_STATE_CORRECT = store_thm
  ("MERGE_STATE_CORRECT",
  ``!aut x. x ∈ aut.states ==>
       (alterA_lang aut = alterA_lang (mergeState x aut))``,
  rw[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> fs[alterA_lang_def]
  >> rename[`word_range x'`]
    >- (`word_range x' ⊆ (mergeState x aut).alphabet` by
           (Cases_on `aut` >> fs[mergeState_def] >> rw[COND_EXPAND_OR])
        >> fs[]
        >> Cases_on `∃s. s ∈ aut.states
                ∧ s ≠ x ∧ equivalentStates aut.final aut.trans s x`
        >- (qabbrev_tac `s' =
              $@ (\s. s ∈ aut.states ∧ s ≠ x
                   ∧ equivalentStates aut.final aut.trans s x)`
            >> qexists_tac `replace_run run x s'`
            >> fs[runForAA_def] >> rpt strip_tac
            >> `!i q. ((q ∈ (replace_run run x s').V i) ∧ ~(q = s')
                                                ==> (q ∈ run.V i))` by (
                 Induct_on `i` >> fs[] >> rpt strip_tac
                  >- (fs[replace_run_def,replaceState_def]
                      >> Cases_on `x ∈ run.V 0` >> fs[]
                     )
                  >- (fs[replace_run_def, replaceState_def]
                      >> Cases_on `x ∈ run.V (SUC i)` >> fs[]
                     )
             )
            >> simp[validAARunFor_def]
            >> rpt strip_tac
              >- (fs[replace_run_def, replaceState_def]
                  >> Cases_on `x ∈ run.V 0` >> fs[]
                   >- (`s' ∈ aut.states ∧ ~(s' = x)
                      ∧ equivalentStates aut.final aut.trans s' x`
                         by metis_tac[SELECT_THM]
                       >> Cases_on `aut` >> fs[mergeState_def]
                       >> simp[] >> rw[]
                       >- (qexists_tac `run.V 0` >> fs[validAARunFor_def]
                           >> fs[replaceState_def]
                          )
                       >- metis_tac[]
                      )
                   >- (Cases_on `aut` >> fs[mergeState_def] >> rw[]
                      >- (qexists_tac `run.V 0` >> fs[validAARunFor_def]
                         >> fs[replaceState_def]
                         )
                      >- metis_tac[]
                      )
                 )
              >- (simp[SUBSET_DEF, replace_run_def] >> rpt strip_tac
                  >> fs[replaceState_def] >> Cases_on `x ∈ run.V i`
                    >- (fs[]
                        >- (Cases_on `aut` >> fs[mergeState_def]
                            >> rw[] >> fs[validAARunFor_def]
                            >> metis_tac[SUBSET_DEF])
                        >- (Cases_on `aut` >> fs[mergeState_def]
                            >> rw[] >> metis_tac[SELECT_THM])
                       )
                    >- (Cases_on `aut` >> fs[mergeState_def] >> rw[]
                        >> fs[validAARunFor_def] >> metis_tac[SUBSET_DEF]
                       )
                 )
              >- (simp[replace_run_def, replaceState_def]
                  >> Cases_on `(q = s') ∧ ~(s' ∈ run.V i)` >> fs[]
                    >- (rw[] >> fs[replace_run_def, replaceState_def]
                        >> Cases_on `x ∈ run.V i` >> fs[]
                        >> `?a. (a, run.E (i,x)) ∈ aut.trans x ∧ at x' i ∈ a`
                              by metis_tac[validAARunFor_def]
                        >> qexists_tac `a` >> fs[]
                        >> Cases_on `aut` >> fs[mergeState_def] >> rw[]
                               >- (simp[replaceBy_def]
                                   >> qexists_tac `(a,run.E (i,x))`
                                   >> fs[replaceSingleTrans_def]
                                   >> `equivalentStates f1 f3 q x`
                                      by metis_tac[SELECT_THM]
                                   >> metis_tac[equivalentStates_def])
                               >- metis_tac[]
                               >- (simp[replaceBy_def]
                                   >> qexists_tac `(a,run.E (i,x))`
                                   >> fs[replaceSingleTrans_def]
                                   >> `equivalentStates f1 f3 q x`
                                      by metis_tac[SELECT_THM]
                                   >> metis_tac[equivalentStates_def])
                               >- metis_tac[]
                       )
                    >- (rw[] >> fs[replace_run_def, replaceState_def]
                        >> `q ∈ run.V i` by metis_tac[IN_UNION,IN_DIFF]
                        >> `?a. (a, run.E (i,q)) ∈ aut.trans q ∧ at x' i ∈ a`
                                 by metis_tac[validAARunFor_def]
                        >> qexists_tac `a` >> fs[] >> Cases_on `aut`
                        >> fs[mergeState_def] >> rw[]
                              >- (simp[replaceBy_def]
                                  >> qexists_tac `(a,run.E (i,q))`
                                  >> fs[replaceSingleTrans_def]
                                 )
                              >- metis_tac[]
                              >- (simp[replaceBy_def]
                                 >> qexists_tac `(a,run.E (i,q))`
                                 >> fs[replaceSingleTrans_def]
                                 )
                       )
                    >- (rw[] >> fs[replace_run_def, replaceState_def]
                        >> rw[] >> `?a. (a, run.E (i,q)) ∈ aut.trans q
                               ∧ at x' i ∈ a`
                               by metis_tac[validAARunFor_def]
                        >> qexists_tac `a` >> fs[] >> Cases_on `aut`
                        >> fs[mergeState_def] >> rw[]
                           >- (simp[replaceBy_def]
                                >> qexists_tac `(a,run.E (i,q))`
                                >> fs[replaceSingleTrans_def]
                              )
                           >- metis_tac[]
                           >- (simp[replaceBy_def]
                               >> qexists_tac `(a,run.E (i,q))`
                               >> fs[replaceSingleTrans_def]
                              )
                       )
                    >- (simp[replace_run_def] >> rpt strip_tac
                        >> Cases_on `(q = s') ∧ ~(s' ∈ run.V i)` >> fs[]
                        >> metis_tac[validAARunFor_def, REPL_STATE_LEMM]
                       )
                    >- (Cases_on `i = 0` >> fs[replace_run_def, replaceState_def]
                        >> Cases_on `q = s'` >> Cases_on `x ∈ run.V i`
                         >- (fs[]
                             >> `?x1. x ∈ run.E (i - 1, x1)
                                ∧ x1 ∈ run.V (i-1)` by metis_tac[validAARunFor_def]
                             >> 
)
)


)
                 )
 )


)
simp[replace_run_def,replaceState_def]
                      >> Cases_on `aut` >> fs[mergeState_def] >> rw[]
                       >- (fs[replaceBy_def,replaceSing])
)


