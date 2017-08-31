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

val EQUIV_STATES_SYMM = store_thm
  ("EQUIV_STATES_SYMM",
   ``!f t x y. equivalentStates f t x y = equivalentStates f t y x``,
   metis_tac[equivalentStates_def]
  );

val EQUIV_STATES_REFL = store_thm
  ("EQUIV_STATES_SYMM",
  ``!f t x. equivalentStates f t x x``,
   metis_tac[equivalentStates_def]
  );


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

(* val REPLACE_TRANS_REACHABLE_LEMM = store_thm *)
(*   ("REPLACE_TRANS_LEMM", *)
(*    ``!f trans a b s. equivalentStates f trans a b ∧ ~(a ∈ s) *)
(*       ==> ((reachable (replaceBy trans a b) s) = *)
(*            replaceState a b (reachable trans s))`` *)
(*    rpt strip_tac *)
(*    >> `!n. (replaceState a b (nStepReachable trans s n) *)
(*             = nStepReachable (replaceBy trans a b) s n)` by ( *)
(*          Induct_on `n` >> rw[SET_EQ_SUBSET, SUBSET_DEF] >> rpt strip_tac *)
(*          >> fs[nStepReachable_def,replaceState_def] *)
(*           >- metis_tac[] *)
(*           >- (Cases_on `∃a' qs s'. *)
(*                    (a',qs) ∈ trans s' ∧ s' ∈ nStepReachable trans s n ∧ a ∈ qs` *)
(*               >> fs[] >> metis_tac[] *)
(*                >- (qexists_tac `a'` >> qexists_tac `qs` *)
(*                    >> qexists_tac `b` >> fs[] >> fs[replaceBy_def,EXISTS_PROD] *)
                   
(*                    >> fs[replaceSingleTrans_def] > *)
(* ) *)
(* `s' ∈ nStepReachable (replaceBy trans a b) s n` by metis_tac[] *)
(*               >> qexists_tac `a'` >> qexists_tac `qs` >> qexists_tac `s'` *)
(*               >> simp[replaceBy_def] *)
(*               >> fs[EXISTS_PROD] >> qexists_tac `a'` >> qexists_tac `qs` *)
(*               >> simp[replaceSingleTrans_def] >>  *)
(* ) *)

(* ) *)

(* rw[SET_EQ_SUBSET] >> rpt strip_tac >> fs[reachable_def, replaceBy_def] *)
(*   >> fs[equivalentStates_def,SUBSET_DEF] >> rpt strip_tac *)
(*   >> qexists_tac `n` *)
(*    >- (Induct_on `n`) *)

(* ) *)


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

val replace_ord_def = Define`
  replace_ord old_ord x x' =
      { (s,s') | ~(s = x) ∧ ~(s' = x) ∧ (s,s') ∈ old_ord }
    ∪ { (x',s) | ~(s = x) ∧ (x,s) ∈ old_ord }
    ∪ { (s,x') | ~(s = x) ∧ (s,x) ∈ old_ord }
    ∪ if (x,x) ∈ old_ord then { (x',x') } else {}`;

(* val REPL_ORD_TRANS_LEMM = store_thm *)
(*   ("REPL_ORD_TRANS_LEMM", *)
(*    ``!ord a b. transitive ord ==> transitive (replace_ord ord a b)``, *)
(*    fs[transitive_def] >> rpt strip_tac *)
(*    >> Cases_on `(x = a) \/ (y = a) \/ (z = a)` *)
(*      >- (fs[replace_ord_def] >> rw[] >> fs[] *)
(*          >> metis_tac[MEMBER_NOT_EMPTY,IN_SING]) *)
(*      >- (fs[replace_ord_def] *)
(*          >- metis_tac[] *)
(*          >- dsimp[] *)


(* ) *)
(* ) *)

val oneStep_def = Define`
  oneStep aut = \x y. ?a qs. (a,qs) ∈ aut.trans y ∧ x ∈ qs ∧ y ∈ aut.states`;

val reachRel_def = Define`
  reachRel aut = (oneStep aut)^*`;

val EQUIV_REACH_LEMM = store_thm
  ("EQUIV_REACH_LEMM",
   ``!aut x y. x ∈ aut.states ∧ y ∈ aut.states
              ∧ equivalentStates aut.final aut.trans x y ==>
         (!v. ~(x = v) ∧ ~(y = v)
              ==> ((reachRel aut) v x = (reachRel aut) v y))``,
   `!aut x y. x ∈ aut.states ∧ y ∈ aut.states
            ∧ equivalentStates aut.final aut.trans x y ==>
         (!v. ~(x = v) ∧ ~(y = v)
              ==> ((reachRel aut) v x ==> (reachRel aut) v y))`
         suffices_by metis_tac[EQUIV_STATES_SYMM]
    >> gen_tac >> fs[reachRel_def]
    >> simp[RTC_eq_NRC]
    >> `∀n x y.
         x ∈ aut.states ∧ y ∈ aut.states
         ∧ equivalentStates aut.final aut.trans x y ⇒
         ∀v.
         x ≠ v ∧ y ≠ v ⇒
         NRC (oneStep aut) n v x ⇒ NRC (oneStep aut) n v y` suffices_by metis_tac[]
    >> Induct_on `n`
      >- (rpt strip_tac >> fs[NRC])
      >- (rpt strip_tac >> fs[NRC_SUC_RECURSE_LEFT]
          >> `oneStep aut z y` by (
               fs[oneStep_def,equivalentStates_def]
               >> qexists_tac `a` >> qexists_tac `qs`
               >> fs[] >> metis_tac[]
           )
          >> metis_tac[]
         )
  );

val MERGE_REACH_LEMM = store_thm
  ("MERGE_REACH_LEMM",
  ``!aut x y. isValidAlterA aut ∧ equivalentStates aut.final aut.trans y x
          ∧ x ∈ aut.states ∧ y ∈ aut.states ∧ ~(x = y)
          ==> let mergedAut = mergeState x aut
              in !q1 q2. (reachRel mergedAut) q1 q2
                 ==>
                ((q1 = @s. s ∈ aut.states ∧ ~(s = x)
                   ∧ equivalentStates aut.final aut.trans s x)
                 \/ (reachRel aut) q1 q2)``,
  rpt strip_tac >> fs[reachRel_def]
  >> HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 >> rpt strip_tac
  >> fs[rel_to_reln_def]
  >> qabbrev_tac `s_new = @s.
          s ∈ aut.states ∧ s ≠ x ∧ equivalentStates aut.final aut.trans s x`
  >> Cases_on `q1 = s_new` >> fs[]
  >> `?q3. (oneStep aut) q3 q2' ∧ equivalentStates aut.final aut.trans q2 q3`
      suffices_by (
        rpt strip_tac >> Cases_on `q1 = q2` >> Cases_on `q1 = q3`
        >> rw[]
          >- (`(oneStep aut) q1 q2'` suffices_by metis_tac[RTC_SUBSET]
              >> fs[] >> Cases_on `aut` >> fs[mergeState_def,oneStep_def] >> fs[]
              >> rpt (POP_ASSUM mp_tac) >> rw[] >> fs[] >> rw[]
                >- (fs[replaceBy_def] >> Cases_on `x'` >> fs[replaceSingleTrans_def]
                    >> rw[] >> Cases_on `x ∈ r` >> fs[] >> rw[]
                     >- (qexists_tac `a` >> qexists_tac `r` >> fs[])
                     >- metis_tac[]
                   )
                >- metis_tac[]
             )
          >- (`q2 ∈ aut.states ∧ q3 ∈ aut.states` by (
                 fs[oneStep_def,isValidAlterA_def] >> Cases_on `aut`
                 >> fs[mergeState_def] >> rw[]
                 >> Cases_on `∃s. s ∈ f ∧ s ≠ x ∧ equivalentStates f1 f3 s x`
                 >> fs[replaceBy_def]
                   >- (Cases_on `x'` >> fs[replaceSingleTrans_def]
                       >> Cases_on `x ∈ r` >> fs[] >> rw[IN_DIFF, IN_UNION]
                       >> `s_new ∈ f` by metis_tac[]
                       >> metis_tac[IN_DIFF,IN_UNION,IN_SING,SUBSET_DEF]
                      )
                   >- metis_tac[IN_DIFF,IN_UNION,IN_SING,SUBSET_DEF]
                   >- metis_tac[IN_DIFF,IN_UNION,IN_SING,SUBSET_DEF]
                   >- metis_tac[IN_DIFF,IN_UNION,IN_SING,SUBSET_DEF]
             )
            >> `(oneStep aut)^* q1 q3` by metis_tac[EQUIV_REACH_LEMM,reachRel_def]
            >> metis_tac[RTC_CASES_RTC_TWICE,RTC_SUBSET]
             )
  )
  >> fs[] >> Cases_on `aut` >> fs[mergeState_def,oneStep_def] >> fs[]
  >> rpt (POP_ASSUM mp_tac) >> rw[] >> fs[]
    >- (fs[replaceBy_def] >> Cases_on `x'` >> fs[replaceSingleTrans_def]
        >> Cases_on `x ∈ r` >> fs[]
        >> rw[] >> fs[IN_UNION] >> metis_tac[EQUIV_STATES_REFL]
       )
    >- metis_tac[]
  );

val MERGE_REACH_LEMM2 = store_thm
  ("MERGE_REACH_LEMM2",
   ``!aut v x y. isValidAlterA aut ∧ equivalentStates aut.final aut.trans x y
               ∧ x ∈ aut.states ∧ y ∈ aut.states ∧ ~(y = x)
         ==> let mergedAut = mergeState x aut
                 and s_new = @s. s ∈ aut.states ∧ s ≠ x ∧
                                 equivalentStates aut.final aut.trans s x
             in !v. reachRel mergedAut s_new v
                    ==> reachRel aut s_new v \/ reachRel aut x v``,
   rpt strip_tac >> fs[]
   >> qabbrev_tac `s_new = @s.
                         s ∈ aut.states ∧ s ≠ x ∧
                         equivalentStates aut.final aut.trans s x`
   >> fs[reachRel_def] >> gen_tac
   >> `!m n. (oneStep (mergeState x aut))^* m n ⇒ (m = s_new)
                   ==> (oneStep aut)^* m n ∨ (oneStep aut)^* x n`
       suffices_by metis_tac[]
   >> HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 >> rpt strip_tac >> rw[]
   >> (Cases_on `n = m`
        >- (`(oneStep aut) m n' ∨ (oneStep aut) x n'`
             suffices_by metis_tac[RTC_SUBSET]
             >> fs[] >> Cases_on `aut` >> fs[mergeState_def,oneStep_def]
             >> fs[] >> rpt (POP_ASSUM mp_tac) >> rw[] >> fs[]
               >- (fs[replaceBy_def] >> Cases_on `x'` >> fs[replaceSingleTrans_def]
                   >> Cases_on `x ∈ r` >> fs[]
                   >> rw[] >> fs[IN_UNION] >> metis_tac[]
                  )
               >- metis_tac[]
           )
        >- (`reachRel aut n n'` by (
               fs[reachRel_def]
               >> `reachRel (mergeState x aut) n n'` by
                   (fs[reachRel_def] >> metis_tac[RTC_SUBSET])
               >> qunabbrev_tac `m`
               >> `reachRel aut n n'` suffices_by metis_tac[reachRel_def]
               >> `(let mergedAut = mergeState x aut
                    in
                        ∀q1 q2.
                         reachRel mergedAut q1 q2 ⇒
                         (q1 =
                          @s.
                               s ∈ aut.states ∧ s ≠ x ∧
                               equivalentStates aut.final aut.trans s x) ∨
                         reachRel aut q1 q2)`
                  by (HO_MATCH_MP_TAC MERGE_REACH_LEMM
                      >> metis_tac[EQUIV_STATES_SYMM])
              >> fs[] >> metis_tac[]
              )
            >> fs[reachRel_def] >> metis_tac[RTC_CASES_RTC_TWICE]
           )
      )
  );

val MERGE_PO_LEMM = store_thm
  ("MERGE_PO_LEMM",
  ``!aut x y. isValidAlterA aut ∧ equivalentStates aut.final aut.trans x y
            ∧ x ∈ aut.states ∧ y ∈ aut.states
      ∧ partial_order (rrestrict (rel_to_reln (reachRel aut)) aut.states)
             aut.states
      ==> (let mergedAut = mergeState x aut
          in partial_order (rrestrict (rel_to_reln (reachRel mergedAut))
                                       mergedAut.states)
                           mergedAut.states)``,
  rpt strip_tac >> fs[]
  >> simp[partial_order_def,reachableRel_def,mergeState_def] >> rpt strip_tac
   >- (fs[domain_def,SUBSET_DEF,rel_to_reln_def,rrestrict_def] >> rpt strip_tac)
   >- (fs[range_def,SUBSET_DEF,rel_to_reln_def,rrestrict_def] >> rpt strip_tac)
   >- (fs[reln_rel_conv_thms,RTC_TRANSITIVE,reachRel_def,rrestrict_def]
       >> qabbrev_tac `R = (REL_RESTRICT (oneStep (mergeState x aut))^*
                                         (mergeState x aut).states)`
       >> `!x y z. R x y ∧ R y z ==> R x z` suffices_by rw[transitive_def]

   >- (rw[reln_rel_conv_thms] >> simp[RREFL_EXP_def,RUNION] >> fs[]


   >- (fs[antisym_def,rel_to_reln_def]
       >> `∀x' y'. oneStep^* x' y' ==> (oneStep^* y' x' ⇒ (x' = y'))`
            suffices_by metis_tac[]
       >> HO_MATCH_MP_TAC RTC_INDUCT >> strip_tac
         >- (POP_ASSUM mp_tac
             >> `!x. oneStep^* x x ⇒ (x = x)` suffices_by metis_tac[]
             >> HO_MATCH_MP_TAC RTC_INDUCT >> rpt strip_tac
            )
         >- (`!x1 x2. oneStep x1 x2
                ==> !y. (oneStep^* y x2 ==> (x2 = y))
                   ==> oneStep^* y x1 ==> (x1 = y)` suffices_by metis_tac[]
             >> rpt gen_tac >> strip_tac 
             >> HO_MATCH_MP_TAC RTC_INDUCT

            
        )

)


)



val MERGE_IS_WEAK = store_thm
  ("MERGE_IS_WEAK",
   ``!aut x. isWeakAlterA aut ∧ x ∈ aut.states ∧ isValidAlterA aut
           ==> isWeakAlterA (mergeState x aut)``,
   rpt strip_tac >> imp_res_tac WAA_REACH_IS_PO >> simp[isWeakAlterA_def]
   >> simp[isWeakWithOrder_def] >> rpt strip_tac
   >> Cases_on `aut` >> fs[mergeState_def]
   >> qabbrev_tac
        `s_new = @s. s ∈ f ∧ s ≠ x ∧ equivalentStates f1 f3 s x`
   >> Cases_on `∃s. s ∈ f ∧ s ≠ x ∧ equivalentStates f1 f3 s x`
   >> qexists_tac
        `rrestrict (replace_ord (reachableRel aut) x s_new) (f DIFF {x})`
   >> simp[] >> fs[isWeakWithOrder_def]
     >- (fs[partial_order_def,reachableRel_def] >> rpt strip_tac
           >- (fs[domain_def,SUBSET_DEF,DIFF_DEF,rrestrict_def]
                 >> rpt strip_tac >> metis_tac[])
           >- (fs[range_def,SUBSET_DEF,DIFF_DEF,rrestrict_def]
                 >> rpt strip_tac >> metis_tac[])
           >- (fs[transitive_def,SUBSET_DEF,DIFF_DEF,rrestrict_def]
                 >> rpt strip_tac >> fs[reachable_def]
                 >> fs[replace_ord_def]
                 >> Cases_on `(x' = x) \/ (y = x) \/ (z = x)`
                   >- (fs[replace_ord_def] >> rw[] >> fs[]
                       >> metis_tac[MEMBER_NOT_EMPTY,IN_SING])
                   >- (`s_new ∈ f ∧ s_new ≠ x ∧ equivalentStates f1 f3 s_new x`
                        by metis_tac[]
                       >> fs[replace_ord_def]
                        >- metis_tac[]
                        >- 
)

 >> simp[replace_ord_def] >> rw[] >> dsimp[]
                 >> fs[reflexive_def]
                   >- (fs[replace_ord_def] >> rw[] >> fs[] >> dsimp[]
                       >- metis_tac[]
                       >- (`s_new ∈ f ∧ s_new ≠ x
                            ∧ equivalentStates f1 f3 s_new x` by metis_tac[]
                           >> fs[] >> metis_tac[]
)
                      )
 >> metis_tac[])
           >- (fs[reflexive_def,SUBSET_DEF,DIFF_DEF,rrestrict_def]
                 >> rpt strip_tac >> metis_tac[])
           >- (fs[antisym_def,SUBSET_DEF,DIFF_DEF,rrestrict_def]
                 >> rpt strip_tac >> metis_tac[])
           >- (fs[replaceBy_def] >> Cases_on `x'` >> fs[replaceSingleTrans_def]
               >> Cases_on `x ∈ r`
                >- (fs[]
                    >> 
                    >> `s_new ∈ f ∧ ~(s_new = x)
                        ∧ equivalentStates f1 f3 s_new x` by metis_tac[]
                    >> `(x, s') ∈ ord` by metis_tac[]
                    >> fs[equivalentStates_def]
                    >> rw[]
)
        )
     >- 

)



val MERGE_STATE_CORRECT = store_thm
  ("MERGE_STATE_CORRECT",
  ``!aut x. x ∈ aut.states ∧ isWeakAlterA aut ∧ FINITE aut.states  ==>
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
            >> qabbrev_tac `repl_run = replace_run run x s'`
            >> qabbrev_tac `new_run = run_restr (repl_run.V 0) repl_run`
            >> qexists_tac `new_run`
            >> fs[runForAA_def]
            >> `validAARunFor (mergeState x aut) new_run x' ∧
                (validAARunFor (mergeState x aut) new_run x'
                 ==> acceptingAARun (mergeState x aut) new_run)`
                suffices_by fs[]
            >> rpt strip_tac
            >> `!i q. ((q ∈ new_run.V i) ∧ ~(q = s')
                     ==> (q ∈ run.V i) ∧ ~(q = x))` by (
                 Induct_on `i` >> fs[] >> rpt strip_tac
                  >- (qunabbrev_tac `new_run` >> qunabbrev_tac `repl_run`
                      >> fs[replace_run_def,replaceState_def,run_restr_def]
                      >> fs[run_restr_V_def]
                      >> Cases_on `x ∈ run.V 0` >> fs[]
                     )
                  >- (qunabbrev_tac `new_run` >> qunabbrev_tac `repl_run`
                      >> fs[replace_run_def,replaceState_def,run_restr_def]
                      >> fs[run_restr_V_def]
                      >> Cases_on `x ∈ run.V 0` >> fs[]
                     )
                  >- (qunabbrev_tac `new_run` >> qunabbrev_tac `repl_run`
                      >> fs[run_restr_def, run_restr_V_def]
                      >> rename [`q' ∈ _`]
                      >> Cases_on `q'' = s'`
                      >> fs[replace_run_def, replaceState_def]
                       >- (Cases_on `s' ∈ run.V i` >> fs[validAARunFor_def]
                          >> Cases_on `(q' = x)` >> Cases_on `x ∈ run.E (i,x)`
                          >> Cases_on `x ∈ run.E (i,s')`
                          >> rw[] >> fs[]
                          >> metis_tac[SUC_ONE_ADD,ADD_COMM,SUBSET_DEF]
                          )
                       >- (`q'' ∈ run.V i` by metis_tac[]
                          >> fs[validAARunFor_def]
                          >> Cases_on `x ∈ run.E (i,q'')` >> fs[]
                          >> metis_tac[SUC_ONE_ADD,ADD_COMM,SUBSET_DEF]
                          )
                     )
                  >- (qunabbrev_tac `new_run` >> qunabbrev_tac `repl_run`
                      >> fs[run_restr_def, replace_run_def, replaceState_def]
                      >> fs[run_restr_V_def]
                      >> Cases_on `(q' = s') ∧ (s' ∉ run.V i)`
                      >> Cases_on `x ∈ run.E (i,x)`
                      >> Cases_on `x ∈ run.E (i,q')`
                      >> rpt (fs[])
                     )
             )
            >> `!i. (s' ∈ new_run.V i) ∧ ~(s' ∈ run.V i) ==> (x ∈ run.V i)` by (
                 Cases_on `i` >> qunabbrev_tac `new_run`
                 >> qunabbrev_tac `repl_run` >> fs[] >> rpt strip_tac
                 >> fs[run_restr_def,run_restr_V_def,replace_run_def]
                 >> fs[replaceState_def]
                  >- (Cases_on `x ∈ run.V 0` >> metis_tac[])
                  >- (rw[] >> Cases_on `(q = s') ∧ s' ∉ run.V i`
                      >> Cases_on `x ∈ run.E (i,x)`
                      >> Cases_on `x ∈ run.E (i,q)`
                      >> fs[validAARunFor_def]
                      >> metis_tac[SUC_ONE_ADD,ADD_COMM,SUBSET_DEF]
                     )
             )
            >> simp[validAARunFor_def]
            >> rpt strip_tac
              >- (Cases_on `x ∈ run.V 0` >> fs[]
                  >> qunabbrev_tac `new_run` >> qunabbrev_tac `repl_run`
                  >> fs[run_restr_def, run_restr_V_def]
                  >> fs[replace_run_def, replaceState_def]
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
              >- (qunabbrev_tac `new_run` >> qunabbrev_tac `repl_run`
                  >> simp[SUBSET_DEF, replace_run_def] >> rpt strip_tac
                  >> fs[replaceState_def] >> Cases_on `x ∈ run.V i`
                  >> rename[`x'' ∈ _`]
                  >> (fs[] >> Cases_on `~(x'' = s')`
                        >- (Cases_on `aut` >> fs[mergeState_def]
                            >> rw[] >> fs[validAARunFor_def]
                            >> fs[run_restr_def,replace_run_def]
                            >> fs[replaceState_def]
                            >> `x'' ∈ run.V i` by metis_tac[]
                            >> metis_tac[SUBSET_DEF])
                        >- (Cases_on `aut` >> fs[mergeState_def]
                            >> rw[] >> metis_tac[SELECT_THM])
                      )
                 )
              >- (Cases_on `(q = s') ∧ ~(s' ∈ run.V i)` >> fs[]
                    >- (`x ∈ run.V i` by fs[]
                        >> `?a. (a, run.E (i,x)) ∈ aut.trans x ∧ at x' i ∈ a`
                              by metis_tac[validAARunFor_def]
                        >> qexists_tac `a` >> fs[]
                        >> Cases_on `aut` >> fs[mergeState_def] >> rw[]
                               >- (simp[replaceBy_def]
                                   >> qexists_tac `(a,run.E (i,x))`
                                   >> fs[replaceSingleTrans_def]
                                   >> `equivalentStates f1 f3 q x`
                                      by metis_tac[SELECT_THM]
                                   >> simp[run_restr_E_def,run_restr_def]
                                   >> qunabbrev_tac `new_run` >> rw[]
                                   >> qunabbrev_tac `repl_run`
                                   >> fs[run_restr_def,run_restr_E_def]
                                   >> fs[replace_run_def,replaceState_def]
                                   >> fs[validAARunFor_def,equivalentStates_def]
                                  )
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
                                  >> qunabbrev_tac `new_run`
                                  >> fs[run_restr_def, run_restr_E_def]
                                  >> qunabbrev_tac `repl_run` >> rw[]
                                 )
                              >- (qunabbrev_tac `new_run`
                                  >> simp[run_restr_def,run_restr_E_def]
                                  >> fs[run_restr_def]
                                  >> qunabbrev_tac `repl_run`
                                  >> fs[] >> metis_tac[]
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
                                >> qunabbrev_tac `new_run`
                                >> fs[run_restr_def, run_restr_E_def]
                                >> qunabbrev_tac `repl_run` >> rw[]
                              )
                           >- metis_tac[]
                       )
                 )
              >- (qunabbrev_tac `new_run` >> simp[run_restr_def,run_restr_E_def]
                  >> simp[run_restr_V_def, DECIDE ``i + 1 = SUC i``]
                  >> Cases_on `q ∈ run_restr_V (repl_run.V 0) repl_run i`
                  >> fs[EMPTY_SUBSET]
                  >> simp[BIGUNION,SUBSET_DEF] >> rpt strip_tac
                  >> metis_tac[]
                 )
              >- (Cases_on `i = 0` >> fs[replace_run_def, replaceState_def]
                  >> qunabbrev_tac `new_run`
                  >> `?j. i = SUC j` by (Cases_on `i` >> fs[])
                  >> rw[] >> fs[run_restr_def, run_restr_V_def]
                  >> metis_tac[run_restr_E_def]
                 )
              >- (`FINITE (mergeState x aut).states` by (
                     Cases_on `aut` >> simp[mergeState_def]
                     >> Cases_on `∃s. s ∈ f ∧ s ≠ x
                               ∧ equivalentStates f1 f3 s x` >> simp[]
                     >> fs[] >> metis_tac[FINITE_DIFF]
                    )
                  >> `isWeakAlterA (mergeState x aut)` by (
                     Cases_on `aut` >> simp[mergeState_def]
                     >> Cases_on `∃s. s ∈ f ∧ s ≠ x
                                  ∧ equivalentStates f1 f3 s x` >> simp[]
                     >> fs[] >> fs[isWeakAlterA_def]
                     >> qexists_tac `ord` >> simp[isWeakWithOrder_def]



)

`∀b q. infBranchOf new_run b ∧ branchFixP b q
                     ⇒ q ∉ (mergeState x aut).final`
                   suffices_by metis_tac[BRANCH_ACC_LEMM]

)
