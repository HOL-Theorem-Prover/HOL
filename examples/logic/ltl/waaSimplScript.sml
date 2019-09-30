open HolKernel Parse bossLib boolLib pairTheory relationTheory set_relationTheory pred_setTheory arithmeticTheory whileTheory

open alterATheory ltlTheory ltl2waaTheory

val _ = new_theory "waaSimpl"
val _ = ParseExtras.temp_loose_equality()

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
  reduceTransSimpl (ALTER_A s a trans i f) =
     ALTER_A s a (removeImplied trans) i f`;

val REDUCE_IS_WEAK = store_thm
  ("REDUCE_IS_WEAK",
   ``!aut. isVeryWeakAlterA aut ==> isVeryWeakAlterA (reduceTransSimpl aut)``,
   rpt strip_tac >> fs[isVeryWeakAlterA_def] >> qexists_tac `ord`
   >> fs[isVeryWeakWithOrder_def] >> Cases_on `aut` >> fs[reduceTransSimpl_def]
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
         ∧ isVeryWeakAlterA aut
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
                       >> `?a. (a, run.E (i,q)) ∈ f1 q ∧ at x i ∈ a` by (
                              fs[validAARunFor_def] >> metis_tac[SUBSET_DEF]
                        )
                       >> qabbrev_tac `a' = (@a. (a,run.E (i,q)) ∈ f1 q ∧ at x i ∈ a)`
                       >> `(a', run.E (i,q)) ∈ f1 q ∧ at x i ∈ a'` by metis_tac[SELECT_THM]
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
                 `isVeryWeakAlterA (reduceTransSimpl aut)` by metis_tac[REDUCE_IS_WEAK]
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
   removeStatesSimpl (ALTER_A s a t i f) =
     (ALTER_A
      (s ∩ reachRelFromSet (ALTER_A s a t i f) (BIGUNION i))
      a
      (λq. if q ∈ (s ∩ reachRelFromSet (ALTER_A s a t i f) (BIGUNION i))
          then t q
          else {})
      i
      (f ∩ reachRelFromSet (ALTER_A s a t i f) (BIGUNION i))
      )`;

val REACHREL_LEMM = store_thm
  ("REACHREL_LEMM",
   ``!x f qs. (x ∈ reachRelFromSet (ltl2vwaa f) qs) ∧ (qs ⊆ tempSubForms f)
            ==> (x ∈ tempSubForms f)``,
    simp[reachRelFromSet_def,reachRel_def]
    >> `!f x y. (oneStep (ltl2vwaa f))^* x y
                     ==> (!qs. x ∈ qs ∧ (qs ⊆ tempSubForms f)
                               ==> y ∈ tempSubForms f)` suffices_by metis_tac[]
    >> gen_tac >> HO_MATCH_MP_TAC RTC_INDUCT >> rpt strip_tac >> fs[]
    >- metis_tac[SUBSET_DEF]
    >- (first_x_assum (qspec_then `tempSubForms f` mp_tac) >> simp[]
        >> rpt strip_tac >> fs[oneStep_def,ltl2vwaa_def,ltl2vwaa_free_alph_def]
                      >> `(x',x) ∈ TSF` by metis_tac[TRANS_REACHES_SUBFORMS]
                      >> metis_tac[TSF_def,TSF_TRANS_LEMM,transitive_def,IN_DEF]
       )
  );

val REDUCE_STATE_IS_WEAK = store_thm
  ("REDUCE_STATE_IS_WEAK",
   ``!aut. (isVeryWeakAlterA aut ∧ isValidAlterA aut)
               ==> isVeryWeakAlterA (removeStatesSimpl aut)``,
   simp[isVeryWeakAlterA_def,isVeryWeakWithOrder_def] >> rpt strip_tac
   >> Cases_on `aut`
   >> simp[removeStatesSimpl_def,ALTER_A_component_equality]
   >> qabbrev_tac `reachable =
                     reachRelFromSet (ALTER_A f f0 f1 f2 f3) (BIGUNION f2)`
   >> qexists_tac `rrestrict ord (f ∩ reachable)`
   >> fs[ALTER_A_component_equality]
   >> strip_tac
   >- metis_tac[INTER_SUBSET,partial_order_subset]
   >- (rpt strip_tac >> `(a,d) ∈ f1 s` by metis_tac[]
       >> simp[rrestrict_def] >> rpt strip_tac
       >- metis_tac[]
       >- (fs[isValidAlterA_def] >> metis_tac[SUBSET_DEF])
       >- (qunabbrev_tac `reachable` >> fs[reachRelFromSet_def,reachRel_def]
           >> `∃x. (oneStep (ALTER_A f f0 f1 f2 f3))^* x s ∧ ∃s. x ∈ s ∧ s ∈ f2`
               by metis_tac[]
           >> fs[] >> qexists_tac `x'` >> rpt strip_tac
           >- (`oneStep (ALTER_A f f0 f1 f2 f3) s s'` by (
                simp[oneStep_def,ALTER_A_component_equality]
                >> metis_tac[]
              )
              >> metis_tac[RTC_RTC,RTC_SUBSET]
              )
           >- metis_tac[]
          )
      )
  );

val REDUCE_STATE_IS_VALID = store_thm
  ("REDUCE_STATE_IS_VALID",
   ``!aut. isValidAlterA aut ==> isValidAlterA (removeStatesSimpl aut)``,
   rpt strip_tac >> simp[isValidAlterA_def] >> rpt strip_tac
   >> fs[isValidAlterA_def,removeStatesSimpl_def]
   >- (Cases_on `aut` >> simp[removeStatesSimpl_def] >> fs[]
       >> `!init a. init ⊆ reachRelFromSet a init` by (
            rpt strip_tac >> simp[reachRelFromSet_def,reachRel_def]
            >> simp[SUBSET_DEF] >> rpt strip_tac
            >> qexists_tac `x` >> fs[]
        )
       >> simp[SUBSET_DEF,IN_POW] >> rpt strip_tac
       >- metis_tac[SUBSET_DEF,IN_POW]
       >- (simp[reachRelFromSet_def,reachRel_def] >> qexists_tac `x'`
           >> simp[RTC_SUBSET] >> metis_tac[]
          )
      )
   >- (Cases_on `aut` >> simp[removeStatesSimpl_def] >> fs[]
       >> simp[SUBSET_DEF,IN_INTER] >> rpt strip_tac
       >> metis_tac[SUBSET_DEF]
      )
   >- (Cases_on `aut` >> fs[removeStatesSimpl_def]
       >> rfs[]
       >> `d ⊆ f` by metis_tac[] >> fs[]
       >> fs[reachRelFromSet_def] >> simp[SUBSET_DEF] >> rpt strip_tac
       >> fs[]
       >> rename [‘reachRel (ALTER_A f f0 f1 f2 f3) b s’, ‘b ∈ s1’, ‘s1 ∈ f2’,
                  ‘d ⊆ f’, ‘x ∈ d’]
       >> qexists_tac `b` >> simp[reachRel_def] >> conj_tac
           >- (`oneStep (ALTER_A f f0 f1 f2 f3) s x` by (
                 simp[oneStep_def] >> metis_tac[]
               )
               >> metis_tac[RTC_TRANSITIVE,relationTheory.transitive_def,
                            RTC_SUBSET,reachRel_def]
              )
           >- metis_tac[]
      )
   >- (Cases_on `aut` >> fs[removeStatesSimpl_def]
       >> rfs[] >> metis_tac[])
  );

val REDUCE_STATE_CORRECT = store_thm
  ("REDUCE_STATE_CORRECT",
   ``!aut. alterA_lang aut = alterA_lang (removeStatesSimpl aut)``,
   rw[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> fs[alterA_lang_def]
     >- (qexists_tac `run` >> fs[runForAA_def] >> rpt strip_tac
          >- (simp[validAARunFor_def]
              >> Q.HO_MATCH_ABBREV_TAC `B1 ∧ B2 ∧ B3 ∧ B4 ∧ B5`
              >> `B1 ∧ B2 ∧ (B2 ==> (B3 ∧ B4 ∧ B5))` suffices_by metis_tac[]
              >> rpt strip_tac >> qunabbrev_tac `B1` >> qunabbrev_tac `B2`
              >> qunabbrev_tac `B3` >> qunabbrev_tac `B4` >> qunabbrev_tac `B5`
             >- (Cases_on `aut` >> fs[validAARunFor_def, removeStatesSimpl_def])
             >- ((* Cases_on `aut` >> fs[validAARunFor_def, removeStatesSimpl_def] *)
                 `!n. run.V n ⊆ reachRelFromSet aut (BIGUNION aut.initial)`
                      by (
                      Induct_on `n`
                      >- (fs[reachRel_def,reachRelFromSet_def]
                          >> simp[SUBSET_DEF] >> rpt strip_tac
                          >> qexists_tac `x'` >> fs[RTC_REFL]
                          >> fs[validAARunFor_def] >> metis_tac[]
                         )
                      >- (fs[validAARunFor_def]
                          >> fs[SUBSET_DEF,reachRelFromSet_def]
                          >> rpt strip_tac >> fs[reachRel_def]
                          >> `∃q'. x' ∈ run.E (n,q') ∧ q' ∈ run.V n`
                              by metis_tac[DECIDE ``~(SUC n = 0)``
                                          ,DECIDE ``SUC n -1 = n``]
                          >> first_x_assum (qspec_then `q'` mp_tac) >> simp[]
                          >> rpt strip_tac >> qexists_tac `x''` >> simp[]
                          >> `oneStep aut q' x'`
                                 suffices_by metis_tac[RTC_CASES2]
                          >> simp[oneStep_def]
                          >> `∃a. (a,run.E (n,q')) ∈ aut.trans q' ∧ at x n ∈ a`
                              by metis_tac[]
                          >> qexists_tac `a` >> qexists_tac `run.E (n,q')`
                          >> simp[] >> metis_tac[SUBSET_DEF]
                         )
                  )
                  >> Cases_on `aut`
                  >> fs[validAARunFor_def,removeStatesSimpl_def]
                )
             >- (Cases_on `aut` >> fs[validAARunFor_def, removeStatesSimpl_def]
                 >> rpt strip_tac
                 >> `q ∈ f
                   ∧ q ∈ reachRelFromSet (ALTER_A f f0 f1 f2 f3) (BIGUNION f2)`
                     by metis_tac[SUBSET_DEF] >> fs[]
                )
             >- (Cases_on `aut` >> fs[validAARunFor_def, removeStatesSimpl_def])
             >- (Cases_on `aut` >> fs[validAARunFor_def, removeStatesSimpl_def])
             )
          >- (Cases_on `aut` >> fs[acceptingAARun_def, removeStatesSimpl_def]
              >> rpt strip_tac
              >> Q.HO_MATCH_ABBREV_TAC `FINITE {i | b i ∈ A ∧ b i ∈ B }`
              >> `{i | b i ∈ A ∧ b i ∈ B } ⊆ {i | b i ∈ A }` by (
                   simp[SUBSET_DEF] >> rpt strip_tac >> metis_tac[]
               )
              >> metis_tac[PSUBSET_DEF,PSUBSET_FINITE]
             )
          >- (Cases_on `aut` >> fs[removeStatesSimpl_def])
        )
     >- (qexists_tac `run` >> fs[runForAA_def] >> rpt strip_tac
         >- (simp[validAARunFor_def] >> rpt strip_tac
             >> Cases_on `aut`
             >> fs[validAARunFor_def, removeStatesSimpl_def]
             >> metis_tac[SUBSET_DEF])
         >- (Cases_on `aut` >> fs[acceptingAARun_def,removeStatesSimpl_def]
             >> rpt strip_tac
             >> `∀i. b i ∈ run.V i` by metis_tac[BRANCH_V_LEMM]
             >> fs[validAARunFor_def] >> first_x_assum (qspec_then `b` mp_tac)
             >> simp[] >> rpt strip_tac
             >> `{i | b i ∈ f3}
                   ⊆ {i | b i ∈ f3 ∧
                        b i ∈ reachRelFromSet
                        (ALTER_A f f0 f1 f2 f3) (BIGUNION f2)}` by (
                  simp[SUBSET_DEF] >> rpt strip_tac
                  >> metis_tac[SUBSET_DEF]
              )
             >> metis_tac[PSUBSET_DEF,PSUBSET_FINITE]
            )
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
  ("EQUIV_STATES_REFL",
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
  mergeState x (ALTER_A states a trans i f) =
            if ?s. s ∈ states ∧ ~(s = x) ∧ equivalentStates f trans s x
            then
                let s' = $@ (\s. s ∈ states ∧ ~(s = x)
                              ∧ equivalentStates f trans s x)
                in ALTER_A
                       (states DIFF {x})
                       a
                       (replaceBy trans x s')
                       (IMAGE (replaceState x s') i)
                       (replaceState x s' f)
            else (ALTER_A states a trans i f)`;

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



(* val replace_ord_def = Define` *)
(*   replace_ord old_ord x x' = *)
(*       { (s,s') | ~(s = x) ∧ ~(s' = x) ∧ (s,s') ∈ old_ord } *)
(*     ∪ { (x',s) | ~(s = x) ∧ (x,s) ∈ old_ord } *)
(*     ∪ { (s,x') | ~(s = x) ∧ (s,x) ∈ old_ord } *)
(*     ∪ if (x,x) ∈ old_ord then { (x',x') } else {}`; *)


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


(*change to new reach relation*)

(* val EQUIV_REACH_LEMM = store_thm *)
(*   ("EQUIV_REACH_LEMM", *)
(*    ``!aut x y. x ∈ aut.states ∧ y ∈ aut.states *)
(*               ∧ equivalentStates aut.final aut.trans x y ==> *)
(*          (!v. ~(x = v) ∧ ~(y = v) *)
(*               ==> ((reachRel aut) v x = (reachRel aut) v y))``, *)
(*    `!aut x y. x ∈ aut.states ∧ y ∈ aut.states *)
(*             ∧ equivalentStates aut.final aut.trans x y ==> *)
(*          (!v. ~(x = v) ∧ ~(y = v) *)
(*               ==> ((reachRel aut) v x ==> (reachRel aut) v y))` *)
(*          suffices_by metis_tac[EQUIV_STATES_SYMM] *)
(*     >> gen_tac >> fs[reachRel_def] *)
(*     >> simp[RTC_eq_NRC] *)
(*     >> `∀n x y. *)
(*          x ∈ aut.states ∧ y ∈ aut.states *)
(*          ∧ equivalentStates aut.final aut.trans x y ⇒ *)
(*          ∀v. *)
(*          x ≠ v ∧ y ≠ v ⇒ *)
(*          NRC (oneStep aut) n v x ⇒ NRC (oneStep aut) n v y` suffices_by metis_tac[] *)
(*     >> Induct_on `n` *)
(*       >- (rpt strip_tac >> fs[NRC]) *)
(*       >- (rpt strip_tac >> fs[NRC_SUC_RECURSE_LEFT] *)
(*           >> `oneStep aut z y` by ( *)
(*                fs[oneStep_def,equivalentStates_def] *)
(*                >> qexists_tac `a` >> qexists_tac `qs` *)
(*                >> fs[] >> metis_tac[] *)
(*            ) *)
(*           >> metis_tac[] *)
(*          ) *)
(*   ); *)

(* val MERGE_REACH_LEMM = store_thm *)
(*   ("MERGE_REACH_LEMM", *)
(*   ``!aut x y. isValidAlterA aut ∧ equivalentStates aut.final aut.trans y x *)
(*           ∧ x ∈ aut.states ∧ y ∈ aut.states ∧ ~(x = y) *)
(*           ==> let mergedAut = mergeState x aut *)
(*               in !q1 q2. (reachRel mergedAut) q1 q2 *)
(*                  ==> *)
(*                 ((q1 = @s. s ∈ aut.states ∧ ~(s = x) *)
(*                    ∧ equivalentStates aut.final aut.trans s x) *)
(*                  \/ (reachRel aut) q1 q2)``, *)
(*   rpt strip_tac >> fs[reachRel_def] *)
(*   >> HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 >> rpt strip_tac *)
(*   >> fs[rel_to_reln_def] *)
(*   >> qabbrev_tac `s_new = @s. *)
(*           s ∈ aut.states ∧ s ≠ x ∧ equivalentStates aut.final aut.trans s x` *)
(*   >> Cases_on `q1 = s_new` >> fs[] *)
(*   >> `?q3. (oneStep aut) q3 q2' ∧ equivalentStates aut.final aut.trans q2 q3` *)
(*       suffices_by ( *)
(*         rpt strip_tac >> Cases_on `q1 = q2` >> Cases_on `q1 = q3` *)
(*         >> rw[] *)
(*           >- (`(oneStep aut) q1 q2'` suffices_by metis_tac[RTC_SUBSET] *)
(*               >> fs[] >> Cases_on `aut` >> fs[mergeState_def,oneStep_def] >> fs[] *)
(*               >> rpt (POP_ASSUM mp_tac) >> rw[] >> fs[] >> rw[] *)
(*                 >- (fs[replaceBy_def] >> Cases_on `x'` >> fs[replaceSingleTrans_def] *)
(*                     >> rw[] >> Cases_on `x ∈ r` >> fs[] >> rw[] *)
(*                      >- (qexists_tac `a` >> qexists_tac `r` >> fs[]) *)
(*                      >- metis_tac[] *)
(*                    ) *)
(*                 >- metis_tac[] *)
(*              ) *)
(*           >- (`q2 ∈ aut.states ∧ q3 ∈ aut.states` by ( *)
(*                  fs[oneStep_def,isValidAlterA_def] >> Cases_on `aut` *)
(*                  >> fs[mergeState_def] >> rw[] *)
(*                  >> Cases_on `∃s. s ∈ f ∧ s ≠ x ∧ equivalentStates f1 f3 s x` *)
(*                  >> fs[replaceBy_def] *)
(*                    >- (Cases_on `x'` >> fs[replaceSingleTrans_def] *)
(*                        >> Cases_on `x ∈ r` >> fs[] >> rw[IN_DIFF, IN_UNION] *)
(*                        >> `s_new ∈ f` by metis_tac[] *)
(*                        >> metis_tac[IN_DIFF,IN_UNION,IN_SING,SUBSET_DEF] *)
(*                       ) *)
(*                    >- metis_tac[IN_DIFF,IN_UNION,IN_SING,SUBSET_DEF] *)
(*                    >- metis_tac[IN_DIFF,IN_UNION,IN_SING,SUBSET_DEF] *)
(*                    >- metis_tac[IN_DIFF,IN_UNION,IN_SING,SUBSET_DEF] *)
(*              ) *)
(*             >> `(oneStep aut)^* q1 q3` by metis_tac[EQUIV_REACH_LEMM,reachRel_def] *)
(*             >> metis_tac[RTC_CASES_RTC_TWICE,RTC_SUBSET] *)
(*              ) *)
(*   ) *)
(*   >> fs[] >> Cases_on `aut` >> fs[mergeState_def,oneStep_def] >> fs[] *)
(*   >> rpt (POP_ASSUM mp_tac) >> rw[] >> fs[] *)
(*     >- (fs[replaceBy_def] >> Cases_on `x'` >> fs[replaceSingleTrans_def] *)
(*         >> Cases_on `x ∈ r` >> fs[] *)
(*         >> rw[] >> fs[IN_UNION] >> metis_tac[EQUIV_STATES_REFL] *)
(*        ) *)
(*     >- metis_tac[] *)
(*   ); *)

(* val MERGE_REACH_LEMM2 = store_thm *)
(*   ("MERGE_REACH_LEMM2", *)
(*    ``!aut v x y. isValidAlterA aut ∧ equivalentStates aut.final aut.trans x y *)
(*                ∧ x ∈ aut.states ∧ y ∈ aut.states ∧ ~(y = x) *)
(*          ==> let mergedAut = mergeState x aut *)
(*                  and s_new = @s. s ∈ aut.states ∧ s ≠ x ∧ *)
(*                                  equivalentStates aut.final aut.trans s x *)
(*              in !v. reachRel mergedAut s_new v *)
(*                     ==> reachRel aut s_new v \/ reachRel aut x v``, *)
(*    rpt strip_tac >> fs[] *)
(*    >> qabbrev_tac `s_new = @s. *)
(*                          s ∈ aut.states ∧ s ≠ x ∧ *)
(*                          equivalentStates aut.final aut.trans s x` *)
(*    >> fs[reachRel_def] >> gen_tac *)
(*    >> `!m n. (oneStep (mergeState x aut))^* m n ⇒ (m = s_new) *)
(*                    ==> (oneStep aut)^* m n ∨ (oneStep aut)^* x n` *)
(*        suffices_by metis_tac[] *)
(*    >> HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 >> rpt strip_tac >> rw[] *)
(*    >> (Cases_on `n = m` *)
(*         >- (`(oneStep aut) m n' ∨ (oneStep aut) x n'` *)
(*              suffices_by metis_tac[RTC_SUBSET] *)
(*              >> fs[] >> Cases_on `aut` >> fs[mergeState_def,oneStep_def] *)
(*              >> fs[] >> rpt (POP_ASSUM mp_tac) >> rw[] >> fs[] *)
(*                >- (fs[replaceBy_def] >> Cases_on `x'` >> fs[replaceSingleTrans_def] *)
(*                    >> Cases_on `x ∈ r` >> fs[] *)
(*                    >> rw[] >> fs[IN_UNION] >> metis_tac[] *)
(*                   ) *)
(*                >- metis_tac[] *)
(*            ) *)
(*         >- (`reachRel aut n n'` by ( *)
(*                fs[reachRel_def] *)
(*                >> `reachRel (mergeState x aut) n n'` by *)
(*                    (fs[reachRel_def] >> metis_tac[RTC_SUBSET]) *)
(*                >> qunabbrev_tac `m` *)
(*                >> `reachRel aut n n'` suffices_by metis_tac[reachRel_def] *)
(*                >> `(let mergedAut = mergeState x aut *)
(*                     in *)
(*                         ∀q1 q2. *)
(*                          reachRel mergedAut q1 q2 ⇒ *)
(*                          (q1 = *)
(*                           @s. *)
(*                                s ∈ aut.states ∧ s ≠ x ∧ *)
(*                                equivalentStates aut.final aut.trans s x) ∨ *)
(*                          reachRel aut q1 q2)` *)
(*                   by (HO_MATCH_MP_TAC MERGE_REACH_LEMM *)
(*                       >> metis_tac[EQUIV_STATES_SYMM]) *)
(*               >> fs[] >> metis_tac[] *)
(*               ) *)
(*             >> fs[reachRel_def] >> metis_tac[RTC_CASES_RTC_TWICE] *)
(*            ) *)
(*       ) *)
(*   ); *)

(* val MERGE_PO_LEMM = store_thm *)
(*   ("MERGE_PO_LEMM", *)
(*   ``!aut x y. isValidAlterA aut ∧ equivalentStates aut.final aut.trans x y *)
(*             ∧ x ∈ aut.states ∧ y ∈ aut.states ∧ ~(y = x) *)
(*       ∧ partial_order (rrestrict (rel_to_reln (reachRel aut)) aut.states) *)
(*              aut.states *)
(*       ==> (let mergedAut = mergeState x aut *)
(*           in partial_order (rrestrict (rel_to_reln (reachRel mergedAut)) *)
(*                                        mergedAut.states) *)
(*                            mergedAut.states)``, *)
(*   rpt strip_tac >> fs[] *)
(*   >> simp[partial_order_def,reachableRel_def,mergeState_def] >> rpt strip_tac *)
(*    >- (fs[domain_def,SUBSET_DEF,rel_to_reln_def,rrestrict_def] >> rpt strip_tac) *)
(*    >- (fs[range_def,SUBSET_DEF,rel_to_reln_def,rrestrict_def] >> rpt strip_tac) *)
(*    >- (fs[reachRel_def,rrestrict_def,transitive_def] *)
(*        >> rpt strip_tac >> fs[rel_to_reln_def] *)
(*        >> metis_tac[RTC_TRANSITIVE]) *)
(*    >- (fs[reflexive_def, rrestrict_def, rel_to_reln_def, reachRel_def]) *)
(*    >- (fs[antisym_def,rel_to_reln_def,rrestrict_def] >> rpt strip_tac *)
(*        >> qabbrev_tac `s_new = *)
(*                          @s. s ∈ aut.states ∧ s ≠ x ∧ *)
(*                               equivalentStates aut.final aut.trans s x` *)
(*        >> Cases_on `x' = s_new` >> Cases_on `y' = s_new` >> fs[] *)
(*        >- (`reachRel aut y' s_new` by ( *)
(*              `let mergedAut = mergeState x aut *)
(*               in *)
(*                   ∀q1 q2. *)
(*                    reachRel mergedAut q1 q2 ⇒ *)
(*                    (q1 = *)
(*                     @s. *)
(*                          s ∈ aut.states ∧ s ≠ x ∧ *)
(*                          equivalentStates aut.final aut.trans s x) ∨ *)
(*                    reachRel aut q1 q2` *)
(*                 by (HO_MATCH_MP_TAC MERGE_REACH_LEMM *)
(*                      >> metis_tac[EQUIV_STATES_SYMM]) *)
(*                 >> fs[] >> metis_tac[] *)
(*           ) *)
(*           >> `s_new ∈ aut.states` by metis_tac[EQUIV_STATES_SYMM] *)
(*           >> `y' ∈ aut.states` by ( *)
(*                  Cases_on `aut` >> fs[mergeState_def] *)
(*                  >> `y' ∈ *)
(*                        (ALTER_A (f DIFF {x}) (IMAGE (replaceState x s_new) f0) *)
(*                        (replaceState x s_new f1) f2 (replaceBy f3 x s_new)).states` *)
(*                  by metis_tac[EQUIV_STATES_SYMM] *)
(*                  >> fs[] *)
(*           ) *)
(*           >> `reachRel aut s_new y' \/ reachRel aut x y'` by ( *)
(*                 `let *)
(*                      mergedAut = mergeState x aut and *)
(*                      s_new = *)
(*                      @s. *)
(*                           s ∈ aut.states ∧ s ≠ x ∧ *)
(*                           equivalentStates aut.final aut.trans s x *)
(*                  in *)
(*                      ∀v. *)
(*                       reachRel mergedAut s_new v ⇒ *)
(*                       reachRel aut s_new v ∨ reachRel aut x v` *)
(*                    by (HO_MATCH_MP_TAC MERGE_REACH_LEMM2 >> metis_tac[]) *)
(*                  >> fs[] >> metis_tac[]) *)
(*              >- (fs[partial_order_def, antisym_def] >> metis_tac[]) *)
(*              >- (Cases_on `x = y'` *)
(*                  >- (rw[] >> Cases_on `aut` >> fs[mergeState_def] *)
(*                      >> `x ∈ *)
(*                  (ALTER_A (f DIFF {x}) (IMAGE (replaceState x s_new) f0) *)
(*                  (replaceState x s_new f1) f2 (replaceBy f3 x s_new)).states` *)
(*                         by metis_tac[EQUIV_STATES_SYMM] *)
(*                      >> fs[]) *)
(*                  >- (rw[] >> `reachRel aut y' x ⇔ reachRel aut y' s_new` by ( *)
(*                           metis_tac[EQUIV_REACH_LEMM,EQUIV_STATES_SYMM] *)
(*                     ) *)
(*                     >> fs[partial_order_def,antisym_def] *)
(*                     >> metis_tac[] *)
(*                     ) *)
(*                 ) *)
(*           ) *)
(*        >- (`reachRel aut x' s_new` by ( *)
(*              `let mergedAut = mergeState x aut *)
(*               in *)
(*                   ∀q1 q2. *)
(*                    reachRel mergedAut q1 q2 ⇒ *)
(*                    (q1 = *)
(*                     @s. *)
(*                          s ∈ aut.states ∧ s ≠ x ∧ *)
(*                          equivalentStates aut.final aut.trans s x) ∨ *)
(*                    reachRel aut q1 q2` *)
(*                 by (HO_MATCH_MP_TAC MERGE_REACH_LEMM *)
(*                      >> metis_tac[EQUIV_STATES_SYMM]) *)
(*                 >> fs[] >> metis_tac[] *)
(*           ) *)
(*           >> `s_new ∈ aut.states` by metis_tac[EQUIV_STATES_SYMM] *)
(*           >> `x' ∈ aut.states` by ( *)
(*                  Cases_on `aut` >> fs[mergeState_def] *)
(*                  >> `x' ∈ *)
(*                        (ALTER_A (f DIFF {x}) (IMAGE (replaceState x s_new) f0) *)
(*                        (replaceState x s_new f1) f2 (replaceBy f3 x s_new)).states` *)
(*                  by metis_tac[EQUIV_STATES_SYMM] *)
(*                  >> fs[] *)
(*           ) *)
(*           >> `reachRel aut s_new x' \/ reachRel aut x x'` by ( *)
(*                 `let *)
(*                      mergedAut = mergeState x aut and *)
(*                      s_new = *)
(*                      @s. *)
(*                           s ∈ aut.states ∧ s ≠ x ∧ *)
(*                           equivalentStates aut.final aut.trans s x *)
(*                  in *)
(*                      ∀v. *)
(*                       reachRel mergedAut s_new v ⇒ *)
(*                       reachRel aut s_new v ∨ reachRel aut x v` *)
(*                    by (HO_MATCH_MP_TAC MERGE_REACH_LEMM2 >> metis_tac[]) *)
(*                  >> fs[] >> metis_tac[]) *)
(*              >- (fs[partial_order_def, antisym_def] >> metis_tac[]) *)
(*              >- (Cases_on `x = x'` *)
(*                  >- (rw[] >> Cases_on `aut` >> fs[mergeState_def] *)
(*                      >> `x ∈ *)
(*                  (ALTER_A (f DIFF {x}) (IMAGE (replaceState x s_new) f0) *)
(*                  (replaceState x s_new f1) f2 (replaceBy f3 x s_new)).states` *)
(*                         by metis_tac[EQUIV_STATES_SYMM] *)
(*                      >> fs[]) *)
(*                  >- (rw[] >> `reachRel aut x' x ⇔ reachRel aut x' s_new` by ( *)
(*                           metis_tac[EQUIV_REACH_LEMM,EQUIV_STATES_SYMM] *)
(*                     ) *)
(*                     >> fs[partial_order_def,antisym_def] *)
(*                     >> metis_tac[] *)
(*                     ) *)
(*                 ) *)
(*           ) *)
(*        >- (`reachRel aut x' y' *)
(*           ∧ reachRel aut y' x'` by ( *)
(*             `let mergedAut = mergeState x aut *)
(*              in *)
(*                  ∀q1 q2. *)
(*                   reachRel mergedAut q1 q2 ⇒ *)
(*                   (q1 = *)
(*                    @s. *)
(*                         s ∈ aut.states ∧ s ≠ x ∧ *)
(*                         equivalentStates aut.final aut.trans s x) ∨ *)
(*                   reachRel aut q1 q2` by *)
(*               (HO_MATCH_MP_TAC MERGE_REACH_LEMM >> metis_tac[EQUIV_STATES_SYMM]) *)
(*            >> fs[] >> metis_tac[]) *)
(*           >> fs[partial_order_def,antisym_def] *)
(*           >> `x' ∈ aut.states ∧ y' ∈ aut.states` by ( *)
(*                Cases_on `aut` >> fs[mergeState_def] *)
(*                >> strip_tac *)
(*                  >- (`x' ∈ *)
(*                  (ALTER_A (f DIFF {x}) (IMAGE (replaceState x s_new) f0) *)
(*                  (replaceState x s_new f1) f2 (replaceBy f3 x s_new)).states` *)
(*                        by metis_tac[EQUIV_STATES_SYMM] *)
(*                      >> fs[]) *)
(*                  >- (`y' ∈ *)
(*                  (ALTER_A (f DIFF {x}) (IMAGE (replaceState x s_new) f0) *)
(*                  (replaceState x s_new f1) f2 (replaceBy f3 x s_new)).states` *)
(*                        by metis_tac[EQUIV_STATES_SYMM] >> fs[]) *)
(*            ) *)
(*           >> metis_tac[] *)
(*           ) *)
(*       ) *)
(*   ); *)

(* val WAA_REACH_IS_PO__ = store_thm *)
(*   ("WAA_REACH_IS_PO__", *)
(*    ``!aut. isWeakAlterA aut ∧ isValidAlterA aut *)
(*              ==> isWeakWithOrder aut *)
(*                    (rrestrict (rel_to_reln (reachRel aut)) aut.states)``, *)
(*    fs[isWeakAlterA_def] >> simp[isWeakWithOrder_def] >> rpt strip_tac *)
(*     >- (fs[partial_order_def,rrestrict_def,rel_to_reln_def] >> rpt strip_tac *)
(*         >- (simp[domain_def,SUBSET_DEF] >> rpt strip_tac) *)
(*         >- (simp[range_def,SUBSET_DEF] >> rpt strip_tac) *)
(*         >- (simp[transitive_def,reachRel_def] >> rpt strip_tac *)
(*             >> metis_tac[RTC_TRANSITIVE]) *)
(*         >- fs[reflexive_def,reachRel_def] *)
(*         >- (fs[antisym_def] *)
(*             >> `!m n. m ∈ aut.states ∧ reachRel aut m n ==> n ∈ aut.states` by ( *)
(*                  fs[reachRel_def] >> HO_MATCH_MP_TAC RTC_lifts_invariants *)
(*                  >> rpt strip_tac >> fs[oneStep_def] *)
(*              ) *)
(*             >> `!m n. reachRel aut m n ==> *)
(*                       m ∈ aut.states ==> (m,n) ∈ ord` by ( *)
(*                  fs[reachRel_def] >> HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 *)
(*                  >> strip_tac *)
(*                    >- (rpt strip_tac >> fs[reflexive_def]) *)
(*                    >- (rpt strip_tac >> fs[] >> fs[oneStep_def] *)
(*                       >> fs[transitive_def] >> metis_tac[]) *)
(*              ) *)
(*             >> rpt strip_tac *)
(*             >> metis_tac[] *)
(*            ) *)
(*        ) *)
(*     >- (simp[rrestrict_def,rel_to_reln_def,reachRel_def] *)
(*         >> fs[isValidAlterA_def] >> strip_tac *)
(*           >- (`(oneStep aut) s' s` suffices_by metis_tac[RTC_SUBSET] *)
(*               >> simp[oneStep_def] >> metis_tac[] *)
(*              ) *)
(*           >- (fs[isValidAlterA_def] >> metis_tac[SUBSET_DEF]) *)
(*        ) *)
(*   ); *)

(* val MERGE_IS_VALID = store_thm *)
(*   ("MERGE_IS_VALID", *)
(*    ``!aut x. isValidAlterA aut ∧ x ∈ aut.states *)
(*                ==> isValidAlterA (mergeState x aut)``, *)
(*    rpt strip_tac *)
(*    >> Cases_on `∃s. s ∈ aut.states ∧ s ≠ x *)
(*                ∧ equivalentStates aut.final aut.trans s x` *)
(*      >- (Cases_on `aut` >> simp[mergeState_def] >> rpt strip_tac *)
(*          >> qabbrev_tac `fullAuto = *)
(*           ALTER_A (f DIFF {x}) *)
(*                   (IMAGE *)
(*                        (replaceState x *)
(*                          (@s. s ∈ f ∧ s ≠ x ∧ equivalentStates f1 f3 s x)) f0) *)
(*                   (replaceState x (@s. s ∈ f ∧ s ≠ x ∧ equivalentStates f1 f3 s x) *)
(*                                 f1) f2 *)
(*                   (replaceBy f3 x (@s. s ∈ f ∧ s ≠ x ∧ equivalentStates f1 f3 s x))` *)
(*          >> fs[] >> `isValidAlterA fullAuto` suffices_by metis_tac[] *)
(*          >> simp[isValidAlterA_def] >> rpt strip_tac *)
(*            >- (qunabbrev_tac `fullAuto` >> fs[IMAGE_DEF,replaceState_def] *)
(*                >> fs[SUBSET_DEF] >> rpt strip_tac *)
(*                >> `f0 ⊆ POW f` by fs[isValidAlterA_def] *)
(*                >> Cases_on `x ∈ x''` >> fs[] *)
(*                 >- (rw[] >> fs[DIFF_DEF,UNION_DEF,IN_POW] >> rpt strip_tac *)
(*                       >- (fs[SUBSET_DEF] >> rpt strip_tac *)
(*                             >> metis_tac[IN_POW,SUBSET_DEF]) *)
(*                       >- metis_tac[] *)
(*                       >- metis_tac[] *)
(*                    ) *)
(*                 >- (`f0 ⊆ POW f` by fs[isValidAlterA_def] *)
(*                     >> fs[IN_POW,IN_DIFF,SUBSET_DEF] >> rpt strip_tac *)
(*                     >> metis_tac[] *)
(*                    ) *)
(*               ) *)
(*            >- (qunabbrev_tac `fullAuto` >> fs[IMAGE_DEF,replaceState_def] *)
(*                >> fs[SUBSET_DEF] >> rpt strip_tac *)
(*                >> `f1 ⊆ f` by fs[isValidAlterA_def] *)
(*                >> Cases_on `x ∈ f1` >> fs[] *)
(*                >> metis_tac[SUBSET_DEF] *)
(*               ) *)
(*            >- (qunabbrev_tac `fullAuto` >> fs[IMAGE_DEF,replaceState_def] *)
(*                >> fs[SUBSET_DEF,replaceBy_def] >> rpt strip_tac *)
(*                >> Cases_on `x'` >> fs[replaceSingleTrans_def] *)
(*                >> Cases_on `x ∈ r` >> fs[] >> rw[] *)
(*                  >- (`r ⊆ f` by (fs[isValidAlterA_def] >> metis_tac[]) *)
(*                      >> Cases_on `x'' = x` *)
(*                      >> fs[IN_DIFF,IN_UNION] *)
(*                      >> metis_tac[SUBSET_DEF] *)
(*                     ) *)
(*                  >- (`d ⊆ f` by (fs[isValidAlterA_def] >> metis_tac[]) *)
(*                      >> metis_tac[SUBSET_DEF] *)
(*                     ) *)
(*                  >- (fs[IN_DIFF,IN_UNION] >> metis_tac[]) *)
(*                  >- metis_tac[] *)
(*               ) *)
(*            >- (qunabbrev_tac `fullAuto` >> fs[isValidAlterA_def,replaceBy_def] *)
(*                >> Cases_on `x'` >> fs[replaceSingleTrans_def] *)
(*                >> `a = q` by (Cases_on `x ∈ r` >> fs[]) *)
(*                >> metis_tac[] *)
(*               ) *)
(*         ) *)
(*      >- (`mergeState x aut = aut` by ( *)
(*             Cases_on `aut` >> simp[mergeState_def,COND_EXPAND] *)
(*             >> fs[COND_EXPAND] >> metis_tac[] *)
(*           ) >> metis_tac[] *)
(*         ) *)
(*   ); *)

(* val MERGE_IS_WEAK = store_thm *)
(*   ("MERGE_IS_WEAK", *)
(*    ``!aut x. isWeakAlterA aut ∧ x ∈ aut.states ∧ isValidAlterA aut *)
(*            ∧ isValidAlterA (mergeState x aut) *)
(*            ==> isWeakAlterA (mergeState x aut)``, *)
(*    rpt strip_tac *)
(*     >> `isWeakWithOrder aut (rrestrict (rel_to_reln (reachRel aut)) aut.states)` *)
(*        by metis_tac[WAA_REACH_IS_PO__] *)
(*     >> fs[isWeakWithOrder_def] *)
(*     >> qabbrev_tac *)
(*          `s_new = @s. s ∈ aut.states ∧ s ≠ x *)
(*                       ∧ equivalentStates aut.final aut.trans s x` *)
(*     >> Cases_on `∃s. s ∈ aut.states ∧ s ≠ x *)
(*                       ∧ equivalentStates aut.final aut.trans s x` *)
(*      >- (`s_new ∈ aut.states ∧ ~(s_new = x) *)
(*           ∧ equivalentStates aut.final aut.trans s_new x` by metis_tac[] *)
(*          >> `(let mergedAut = mergeState x aut *)
(*               in partial_order *)
(*                      (rrestrict (rel_to_reln (reachRel mergedAut)) *)
(*                                 mergedAut.states) mergedAut.states)` by ( *)
(*                 HO_MATCH_MP_TAC MERGE_PO_LEMM >> metis_tac[EQUIV_STATES_SYMM]) *)
(*          >> fs[] >> simp[isWeakAlterA_def,isWeakWithOrder_def] *)
(*          >> qexists_tac `(rrestrict (rel_to_reln (reachRel (mergeState x aut))) *)
(*                                     (mergeState x aut).states)` *)
(*          >> simp[] >> rpt strip_tac >> fs[rrestrict_def,rel_to_reln_def] *)
(*          >> fs[reachRel_def] >> strip_tac *)
(*            >- (`oneStep (mergeState x aut) s'' s'` *)
(*                  suffices_by metis_tac[RTC_SUBSET] *)
(*                >> fs[oneStep_def] >> metis_tac[] *)
(*               ) *)
(*            >- (fs[isValidAlterA_def] >> metis_tac[SUBSET_DEF]) *)
(*         ) *)
(*      >- (`mergeState x aut = aut` by ( *)
(*             Cases_on `aut` >> simp[mergeState_def,COND_EXPAND] *)
(*             >> fs[COND_EXPAND] >> metis_tac[] *)
(*         ) >> metis_tac[] *)
(*         ) *)
(*   ); *)

(* val RUN_WELLBEHAVED_MERGE = store_thm *)
(*   ("RUN_WELLBEHAVED_MERGE", *)
(*    ``!aut r w s x. runForAA aut r w ∧ s ∈ aut.states ∧ ~(s = x) ∧ *)
(*      equivalentStates aut.final aut.trans s x ∧ x ∈ aut.states *)
(*      ∧ isWeakAlterA aut ∧ isValidAlterA aut ∧ FINITE aut.states *)
(*       ==> ?r2. runForAA aut r2 w *)
(*       ∧ !i. (s ∈ r2.V i) ∧ (x ∈ r2.V i) ==> (r2.E (i,s) = r2.E (i,x))``, *)
(*    gen_tac >> gen_tac >> gen_tac *)
(*    >> `∀ord s x. runForAA aut r w ∧ s ∈ aut.states ∧ s ≠ x ∧ *)
(*              equivalentStates aut.final aut.trans s x ∧ x ∈ aut.states ∧ *)
(*              isWeakWithOrder aut ord ∧ isValidAlterA aut ∧ *)
(*              FINITE aut.states *)
(*              ∧ ((s,x) ∈ ord \/ (~((x,s) ∈ ord) ∧ ~((s,x) ∈ ord))) ⇒ *)
(*               ∃r2. *)
(*               runForAA aut r2 w ∧ *)
(*               ∀i. s ∈ r2.V i ∧ x ∈ r2.V i ⇒ (r2.E (i,s) = r2.E (i,x))` *)
(*        suffices_by (rpt strip_tac >> fs[isWeakAlterA_def] *)
(*                     >> first_x_assum (qspec_then `ord` mp_tac) *)
(*                     >> rpt strip_tac *)
(*                     >> `(s,x) ∈ ord \/ (x,s) ∈ ord *)
(*                     \/ (~((x,s) ∈ ord) ∧ ~((s,x) ∈ ord))` by metis_tac[] *)
(*                     >> metis_tac[EQUIV_STATES_SYMM] *)
(*                    ) *)
(*    >> rpt strip_tac *)
(*    >> (`~((x,s) ∈ ord)` by *)
(*               (fs[isWeakWithOrder_def,partial_order_def,antisym_def] *)
(*               >> metis_tac[]) *)
(*         >> qabbrev_tac `new_run = *)
(*              run_restr (r.V 0) (ALTERA_RUN r.V *)
(*                               (λ(i,q). if (q = x) ∧ (s ∈ r.V i) *)
(*                                        then r.E (i,s) else r.E (i,q)))` *)
(*         >> `!i. new_run.V i ⊆ r.V i` by ( *)
(*              Induct_on `i` *)
(*               >- (qunabbrev_tac `new_run` >> fs[run_restr_def,validAARunFor_def] *)
(*                   >> fs[run_restr_V_def]) *)
(*               >- (simp[SUBSET_DEF] >> rpt strip_tac >> qunabbrev_tac `new_run` *)
(*                   >> fs[run_restr_V_def,run_restr_def] *)
(*                   >> Cases_on `(q = x) ∧ (s ∈ r.V i)` >> fs[] *)
(*                   >> `s' ⊆ r.V (i + 1)` *)
(*                       by metis_tac[runForAA_def,validAARunFor_def] *)
(*                   >> metis_tac[SUC_ONE_ADD,ADD_COMM,SUBSET_DEF] *)
(*                  ) *)
(*          ) *)
(*         >> qexists_tac `new_run` >> fs[runForAA_def] *)
(*         >> `(validAARunFor aut new_run w *)
(*            ∧ ((validAARunFor aut new_run w ==> acceptingAARun aut new_run))) ∧ *)
(*                  ∀i. s ∈ new_run.V i ∧ x ∈ new_run.V i ==> *)
(*                    (new_run.E (i,s) = new_run.E (i,x))` suffices_by fs[] *)
(*         >> rpt strip_tac *)
(*          >- (simp[validAARunFor_def] >> rpt strip_tac *)
(*           >- (qunabbrev_tac `new_run` >> fs[run_restr_def,run_restr_V_def] *)
(*            >> metis_tac[validAARunFor_def]) *)
(*           >- metis_tac[SUBSET_TRANS,validAARunFor_def] *)
(*           >- (`q ∈ r.V i` by metis_tac[SUBSET_DEF] *)
(*               >> qunabbrev_tac `new_run` >> simp[run_restr_def,run_restr_E_def] *)
(*               >> Cases_on `(q = x) ∧ (s ∈ r.V i)` *)
(*                >- (fs[validAARunFor_def] *)
(*                    >> `∃a. (a,r.E (i,s)) ∈ aut.trans s ∧ at w i ∈ a` *)
(*                        by metis_tac[] *)
(*                    >> qexists_tac `a` >> fs[] *)
(*                    >> `(a,r.E (i,s)) ∈ aut.trans x` *)
(*                         suffices_by fs[run_restr_def] *)
(*                    >> metis_tac[equivalentStates_def] *)
(*                   ) *)
(*                >- (fs[validAARunFor_def] *)
(*                    >> `∃a. (a,r.E (i,q)) ∈ aut.trans q ∧ at w i ∈ a` *)
(*                        by metis_tac[] *)
(*                    >> qexists_tac `a` >> fs[] *)
(*                    >> `(a,r.E(i,q)) ∈ aut.trans q` suffices_by fs[run_restr_def] *)
(*                    >> metis_tac[] *)
(*                   ) *)
(*              ) *)
(*           >- (simp[SUBSET_DEF] >> rpt strip_tac >> qunabbrev_tac `new_run` *)
(*                 >> fs[run_restr_def,run_restr_V_def,run_restr_E_def] *)
(*                 >> qabbrev_tac `fullRunV = \i. *)
(*                     run_restr_V (r.V 0) *)
(*                      (ALTERA_RUN r.V *)
(*                        (λ(i,q). *)
(*                          if (q = x) ∧ s ∈ r.V i *)
(*                          then r.E (i,s) else r.E (i,q))) i` *)
(*                 >> fs[] *)
(*                 >> `q ∈ fullRunV i` by metis_tac[MEMBER_NOT_EMPTY] >> fs[] *)
(*                 >> `x' ∈ fullRunV (SUC i)` *)
(*                    suffices_by metis_tac[SUC_ONE_ADD,ADD_COMM] *)
(*                 >> qunabbrev_tac `fullRunV` >> simp[run_restr_V_def] *)
(*                 >> Cases_on `(q = x) ∧ s ∈ r.V i` >> fs[] *)
(*                 >> metis_tac[] *)
(*              ) *)
(*           >- (Cases_on `i=0` >> fs[] >> `q ∈ r.V i` by metis_tac[SUBSET_DEF] *)
(*                 >> qunabbrev_tac `new_run` *)
(*                 >> simp[] *)
(*                 >> `?j. i = SUC j` by (Cases_on `i` >> fs[]) *)
(*                 >> rw[] >> fs[] *)
(*                 >> fs[run_restr_V_def,run_restr_def,run_restr_E_def] *)
(*                 >> metis_tac[] *)
(*              ) *)
(*             ) *)
(*          >- (`∀b f. infBranchOf new_run b ∧ branchFixP b f *)
(*               ⇒ f ∉ aut.final` *)
(*                suffices_by metis_tac[BRANCH_ACC_LEMM,isWeakAlterA_def] *)
(*              >> `∀b1 f1. infBranchOf r b1 ∧ branchFixP b1 f1 *)
(*                 ⇒ f1 ∉ aut.final` by metis_tac[BRANCH_ACC_LEMM,isWeakAlterA_def] *)
(*              >> rpt strip_tac >> fs[branchFixP_def] *)
(*              >> Cases_on `(f = x) ∧ ((f = x) ==> ?j. i <= j ∧ s ∈ r.V j)` *)
(*                 >> fs[] *)
(*                >- (`?j. i <= j ∧ s ∈ r.V j` by fs[] *)
(*                   >> `!j. b j ∈ new_run.V j` by metis_tac[BRANCH_V_LEMM] *)
(*                   >> fs[infBranchOf_def] *)
(*                   >> `x ∈ new_run.E (j, x)` by ( *)
(*                        `b (j + 1) = x` by simp[] *)
(*                        >> `b j = x` by simp[] *)
(*                        >> `b (j + 1) ∈ new_run.E (j, b j)` by metis_tac[] *)
(*                        >> metis_tac[] *)
(*                   ) *)
(*                   >> qunabbrev_tac `new_run` >> POP_ASSUM mp_tac *)
(*                   >> simp[run_restr_def, run_restr_E_def] *)
(*                   >> `b j = x` by simp[] *)
(*                   >> first_x_assum (qspec_then `j` mp_tac) *)
(*                   >> simp[run_restr_def] >> rpt strip_tac *)
(*                   >> fs[validAARunFor_def] *)
(*                   >> `∃a. (a,r.E (j,s)) ∈ aut.trans s ∧ at w j ∈ a` *)
(*                       by metis_tac[] *)
(*                   >> metis_tac[isWeakWithOrder_def] *)
(*                   ) *)
(*                >- (`infBranchSuffOf r i (\p. f)` by ( *)
(*                      simp[infBranchSuffOf_def] >> rpt strip_tac *)
(*                       >- (`f ∈ new_run.V i` *)
(*                            by metis_tac[BRANCH_V_LEMM, DECIDE ``i >= i``] *)
(*                           >> metis_tac[SUBSET_DEF] *)
(*                          ) *)
(*                       >- (fs[infBranchOf_def] *)
(*                           >> `f ∈ new_run.E (i + p, f)` by ( *)
(*                               `b (i + p + 1) = f` by fs[] *)
(*                               >> `b (i + p) = f` by fs[] *)
(*                               >> metis_tac[]) *)
(*                           >> qunabbrev_tac `new_run` *)
(*                           >> fs[run_restr_def, run_restr_E_def] *)
(*                           >> metis_tac[MEMBER_NOT_EMPTY] *)
(*                          ) *)
(*                     ) *)
(*                     >> qabbrev_tac `new_branch = \p:num. f` *)
(*                     >> `∃b'. infBranchOf r b' ∧ ∀a. new_branch a = b' (a + i)` *)
(*                         by metis_tac[BRANCH_SUFF_LEMM] *)
(*                     >> rename[`infBranchOf r b'`] *)
(*                     >> first_x_assum (qspec_then `b'` mp_tac) >> rpt strip_tac *)
(*                     >> first_x_assum (qspec_then `f` mp_tac) >> simp[] *)
(*                     >> qexists_tac `i` >> qunabbrev_tac `new_branch` *)
(*                     >> rpt strip_tac >> fs[] *)
(*                      >- metis_tac[DECIDE ``0 + i = i``] *)
(*                      >- (`i <= m` by simp[] *)
(*                          >> `?p. m = i + p` by metis_tac[LESS_EQ_EXISTS] *)
(*                          >> metis_tac[ADD_COMM] *)
(*                         ) *)
(*                   ) *)
(*                >- (`infBranchSuffOf r i (\p. f)` by ( *)
(*                           simp[infBranchSuffOf_def] >> rpt strip_tac *)
(*                           >- (`f ∈ new_run.V i` *)
(*                                 by metis_tac[BRANCH_V_LEMM, DECIDE ``i >= i``] *)
(*                               >> metis_tac[SUBSET_DEF] *)
(*                              ) *)
(*                           >- (fs[infBranchOf_def] >> rw[] *)
(*                               >> `f ∈ new_run.E (i + p, f)` by ( *)
(*                                    `b (i + p + 1) = f` by fs[] *)
(*                                    >> `b (i + p) = f` by fs[] *)
(*                                    >> metis_tac[]) *)
(*                        >> qunabbrev_tac `new_run` *)
(*                        >> fs[run_restr_def, run_restr_E_def] *)
(*                        >> metis_tac[MEMBER_NOT_EMPTY,DECIDE ``i <= i + p``] *)
(*                              ) *)
(*                       ) *)
(*                    >> qabbrev_tac `new_branch = \p:num. f` *)
(*                    >> `∃b'. infBranchOf r b' ∧ ∀j. new_branch j = b' (j + i)` *)
(*                        by metis_tac[BRANCH_SUFF_LEMM] *)
(*                    >> rename[`infBranchOf r b'`] *)
(*                    >> first_x_assum (qspec_then `b'` mp_tac) >> rpt strip_tac *)
(*                    >> first_x_assum (qspec_then `f` mp_tac) >> simp[] *)
(*                    >> qexists_tac `i` >> qunabbrev_tac `new_branch` *)
(*                    >> rpt strip_tac >> fs[] *)
(*                     >- metis_tac[DECIDE ``i + 0 = i``] *)
(*                     >- (`i <= m` by simp[] *)
(*                         >> `?p. m = i + p` by metis_tac[LESS_EQ_EXISTS] *)
(*                         >> metis_tac[] *)
(*                        ) *)
(*                   ) *)
(*             ) *)
(*          >- (`s ∈ r.V i ∧ x ∈ r.V i` by metis_tac[SUBSET_DEF] *)
(*              >> qunabbrev_tac `new_run` >> simp[SET_EQ_SUBSET,SUBSET_DEF] *)
(*              >> rpt strip_tac >> fs[run_restr_def, run_restr_E_def] *)
(*              >> metis_tac[MEMBER_NOT_EMPTY] *)
(*             ) *)
(*       ) *)
(*   ); *)

(*up to here should work with new reach rel*)


(* val MERGE_STATE_CORRECT = store_thm *)
(*   ("MERGE_STATE_CORRECT", *)
(*   ``!aut x. x ∈ aut.states ∧ isWeakAlterA aut ∧ isValidAlterA aut *)
(*             ∧ FINITE aut.states  ==> *)
(*        (alterA_lang aut = alterA_lang (mergeState x aut))``, *)
(*   rw[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> fs[alterA_lang_def] *)
(*   >> rename[`word_range x'`] *)
(*     >- (`word_range x' ⊆ (mergeState x aut).alphabet` by *)
(*            (Cases_on `aut` >> fs[mergeState_def] >> rw[COND_EXPAND_OR]) *)
(*         >> fs[] *)
(*         >> Cases_on `∃s. s ∈ aut.states *)
(*                 ∧ s ≠ x ∧ equivalentStates aut.final aut.trans s x` *)
(*         >- (qabbrev_tac `s' = *)
(*               $@ (\s. s ∈ aut.states ∧ s ≠ x *)
(*                    ∧ equivalentStates aut.final aut.trans s x)` *)
(*             >> `∃r2. *)
(*                  runForAA aut r2 x' ∧ *)
(*                  ∀i. s' ∈ r2.V i ∧ x ∈ r2.V i ⇒ (r2.E (i,s') = r2.E (i,x))` *)
(*                by metis_tac[RUN_WELLBEHAVED_MERGE] *)
(*             >> qabbrev_tac `repl_run = replace_run r2 x s'` *)
(*             >> qabbrev_tac `new_run = run_restr (repl_run.V 0) repl_run` *)
(*             >> qexists_tac `new_run` *)
(*             >> fs[runForAA_def] *)
(*             >> `validAARunFor (mergeState x aut) new_run x' ∧ *)
(*                 (validAARunFor (mergeState x aut) new_run x' *)
(*                  ==> acceptingAARun (mergeState x aut) new_run)` *)
(*                 suffices_by fs[] *)
(*             >> rpt strip_tac *)
(*             >> `!i q. ((q ∈ new_run.V i) ∧ ~(q = s') *)
(*                      ==> (q ∈ r2.V i) ∧ ~(q = x))` by ( *)
(*                  Induct_on `i` >> fs[] >> rpt strip_tac *)
(*                   >- (qunabbrev_tac `new_run` >> qunabbrev_tac `repl_run` *)
(*                       >> fs[replace_run_def,replaceState_def,run_restr_def] *)
(*                       >> fs[run_restr_V_def] *)
(*                       >> Cases_on `x ∈ r2.V 0` >> fs[] *)
(*                      ) *)
(*                   >- (qunabbrev_tac `new_run` >> qunabbrev_tac `repl_run` *)
(*                       >> fs[replace_run_def,replaceState_def,run_restr_def] *)
(*                       >> fs[run_restr_V_def] *)
(*                       >> Cases_on `x ∈ r2.V 0` >> fs[] *)
(*                      ) *)
(*                   >- (qunabbrev_tac `new_run` >> qunabbrev_tac `repl_run` *)
(*                       >> fs[run_restr_def, run_restr_V_def] *)
(*                       >> rename [`q' ∈ _`] *)
(*                       >> Cases_on `q'' = s'` *)
(*                       >> fs[replace_run_def, replaceState_def] *)
(*                        >- (Cases_on `s' ∈ r2.V i` >> fs[validAARunFor_def] *)
(*                           >> Cases_on `(q' = x)` >> Cases_on `x ∈ r2.E (i,x)` *)
(*                           >> Cases_on `x ∈ r2.E (i,s')` *)
(*                           >> rw[] >> fs[] *)
(*                           >> metis_tac[SUC_ONE_ADD,ADD_COMM,SUBSET_DEF] *)
(*                           ) *)
(*                        >- (`q'' ∈ r2.V i` by metis_tac[] *)
(*                           >> fs[validAARunFor_def] *)
(*                           >> Cases_on `x ∈ r2.E (i,q'')` >> fs[] *)
(*                           >> metis_tac[SUC_ONE_ADD,ADD_COMM,SUBSET_DEF] *)
(*                           ) *)
(*                      ) *)
(*                   >- (qunabbrev_tac `new_run` >> qunabbrev_tac `repl_run` *)
(*                       >> fs[run_restr_def, replace_run_def, replaceState_def] *)
(*                       >> fs[run_restr_V_def] *)
(*                       >> Cases_on `(q' = s') ∧ (s' ∉ r2.V i)` *)
(*                       >> Cases_on `x ∈ r2.E (i,x)` *)
(*                       >> Cases_on `x ∈ r2.E (i,q')` *)
(*                       >> rpt (fs[]) *)
(*                      ) *)
(*              ) *)
(*             >> `!i. (s' ∈ new_run.V i) ∧ ~(s' ∈ r2.V i) ==> (x ∈ r2.V i)` by ( *)
(*                  Cases_on `i` >> qunabbrev_tac `new_run` *)
(*                  >> qunabbrev_tac `repl_run` >> fs[] >> rpt strip_tac *)
(*                  >> fs[run_restr_def,run_restr_V_def,replace_run_def] *)
(*                  >> fs[replaceState_def] *)
(*                   >- (Cases_on `x ∈ r2.V 0` >> metis_tac[]) *)
(*                   >- (rw[] >> Cases_on `(q = s') ∧ s' ∉ r2.V i` *)
(*                       >> Cases_on `x ∈ r2.E (i,x)` *)
(*                       >> Cases_on `x ∈ r2.E (i,q)` *)
(*                       >> fs[validAARunFor_def] *)
(*                       >> metis_tac[SUC_ONE_ADD,ADD_COMM,SUBSET_DEF] *)
(*                      ) *)
(*              ) *)
(*             >> simp[validAARunFor_def] *)
(*             >> rpt strip_tac *)
(*               >- (Cases_on `x ∈ r2.V 0` >> fs[] *)
(*                   >> qunabbrev_tac `new_run` >> qunabbrev_tac `repl_run` *)
(*                   >> fs[run_restr_def, run_restr_V_def] *)
(*                   >> fs[replace_run_def, replaceState_def] *)
(*                    >- (`s' ∈ aut.states ∧ ~(s' = x) *)
(*                       ∧ equivalentStates aut.final aut.trans s' x` *)
(*                          by metis_tac[SELECT_THM] *)
(*                        >> Cases_on `aut` >> fs[mergeState_def] *)
(*                        >> simp[] >> rw[] *)
(*                        >- (qexists_tac `r2.V 0` >> fs[validAARunFor_def] *)
(*                            >> fs[replaceState_def] *)
(*                           ) *)
(*                        >- metis_tac[] *)
(*                       ) *)
(*                    >- (Cases_on `aut` >> fs[mergeState_def] >> rw[] *)
(*                       >- (qexists_tac `r2.V 0` >> fs[validAARunFor_def] *)
(*                          >> fs[replaceState_def] *)
(*                          ) *)
(*                       >- metis_tac[] *)
(*                       ) *)
(*                  ) *)
(*               >- (qunabbrev_tac `new_run` >> qunabbrev_tac `repl_run` *)
(*                   >> simp[SUBSET_DEF, replace_run_def] >> rpt strip_tac *)
(*                   >> fs[replaceState_def] >> Cases_on `x ∈ r2.V i` *)
(*                   >> rename[`x'' ∈ _`] *)
(*                   >> (fs[] >> Cases_on `~(x'' = s')` *)
(*                         >- (Cases_on `aut` >> fs[mergeState_def] *)
(*                             >> rw[] >> fs[validAARunFor_def] *)
(*                             >> fs[run_restr_def,replace_run_def] *)
(*                             >> fs[replaceState_def] *)
(*                             >> `x'' ∈ r2.V i` by metis_tac[] *)
(*                             >> metis_tac[SUBSET_DEF]) *)
(*                         >- (Cases_on `aut` >> fs[mergeState_def] *)
(*                             >> rw[] >> metis_tac[SELECT_THM]) *)
(*                       ) *)
(*                  ) *)
(*               >- (Cases_on `(q = s') ∧ ~(s' ∈ r2.V i)` >> fs[] *)
(*                     >- (`x ∈ r2.V i` by fs[] *)
(*                         >> `?a. (a, r2.E (i,x)) ∈ aut.trans x ∧ at x' i ∈ a` *)
(*                               by metis_tac[validAARunFor_def] *)
(*                         >> qexists_tac `a` >> fs[] *)
(*                         >> Cases_on `aut` >> fs[mergeState_def] >> rw[] *)
(*                                >- (simp[replaceBy_def] *)
(*                                    >> qexists_tac `(a,r2.E (i,x))` *)
(*                                    >> fs[replaceSingleTrans_def] *)
(*                                    >> `equivalentStates f1 f3 q x` *)
(*                                       by metis_tac[SELECT_THM] *)
(*                                    >> simp[run_restr_E_def,run_restr_def] *)
(*                                    >> qunabbrev_tac `new_run` >> rw[] *)
(*                                    >> qunabbrev_tac `repl_run` *)
(*                                    >> fs[run_restr_def,run_restr_E_def] *)
(*                                    >> fs[replace_run_def,replaceState_def] *)
(*                                    >> fs[validAARunFor_def,equivalentStates_def] *)
(*                                   ) *)
(*                                >- metis_tac[] *)
(*                        ) *)
(*                     >- (rw[] >> fs[replace_run_def, replaceState_def] *)
(*                         >> `q ∈ r2.V i` by metis_tac[IN_UNION,IN_DIFF] *)
(*                         >> `?a. (a, r2.E (i,q)) ∈ aut.trans q ∧ at x' i ∈ a` *)
(*                                  by metis_tac[validAARunFor_def] *)
(*                         >> qexists_tac `a` >> fs[] >> Cases_on `aut` *)
(*                         >> fs[mergeState_def] >> rw[] *)
(*                               >- (simp[replaceBy_def] *)
(*                                   >> qexists_tac `(a,r2.E (i,q))` *)
(*                                   >> fs[replaceSingleTrans_def] *)
(*                                   >> qunabbrev_tac `new_run` *)
(*                                   >> fs[run_restr_def, run_restr_E_def] *)
(*                                   >> qunabbrev_tac `repl_run` >> rw[] *)
(*                                  ) *)
(*                               >- (qunabbrev_tac `new_run` *)
(*                                   >> simp[run_restr_def,run_restr_E_def] *)
(*                                   >> fs[run_restr_def] *)
(*                                   >> qunabbrev_tac `repl_run` *)
(*                                   >> fs[] >> metis_tac[] *)
(*                                  ) *)
(*                        ) *)
(*                     >- (rw[] >> fs[replace_run_def, replaceState_def] *)
(*                         >> rw[] >> `?a. (a, r2.E (i,q)) ∈ aut.trans q *)
(*                                ∧ at x' i ∈ a` *)
(*                                by metis_tac[validAARunFor_def] *)
(*                         >> qexists_tac `a` >> fs[] >> Cases_on `aut` *)
(*                         >> fs[mergeState_def] >> rw[] *)
(*                            >- (simp[replaceBy_def] *)
(*                                 >> qexists_tac `(a,r2.E (i,q))` *)
(*                                 >> fs[replaceSingleTrans_def] *)
(*                                 >> qunabbrev_tac `new_run` *)
(*                                 >> fs[run_restr_def, run_restr_E_def] *)
(*                                 >> qunabbrev_tac `repl_run` >> rw[] *)
(*                               ) *)
(*                            >- metis_tac[] *)
(*                        ) *)
(*                  ) *)
(*               >- (qunabbrev_tac `new_run` >> simp[run_restr_def,run_restr_E_def] *)
(*                   >> simp[run_restr_V_def, DECIDE ``i + 1 = SUC i``] *)
(*                   >> Cases_on `q ∈ run_restr_V (repl_run.V 0) repl_run i` *)
(*                   >> fs[EMPTY_SUBSET] *)
(*                   >> simp[BIGUNION,SUBSET_DEF] >> rpt strip_tac *)
(*                   >> metis_tac[] *)
(*                  ) *)
(*               >- (Cases_on `i = 0` >> fs[replace_run_def, replaceState_def] *)
(*                   >> qunabbrev_tac `new_run` *)
(*                   >> `?j. i = SUC j` by (Cases_on `i` >> fs[]) *)
(*                   >> rw[] >> fs[run_restr_def, run_restr_V_def] *)
(*                   >> metis_tac[run_restr_E_def] *)
(*                  ) *)
(*               >- (`FINITE (mergeState x aut).states` by ( *)
(*                      Cases_on `aut` >> simp[mergeState_def] *)
(*                      >> Cases_on `∃s. s ∈ f ∧ s ≠ x *)
(*                                ∧ equivalentStates f1 f3 s x` >> simp[] *)
(*                      >> fs[] >> metis_tac[FINITE_DIFF] *)
(*                     ) *)
(*                   >> `isWeakAlterA (mergeState x aut)` *)
(*                         by metis_tac[MERGE_IS_WEAK,MERGE_IS_VALID] *)
(*                   >> `∀b q. infBranchOf new_run b ∧ branchFixP b q *)
(*                      ⇒ q ∉ (mergeState x aut).final` *)
(*                       suffices_by metis_tac[BRANCH_ACC_LEMM] *)
(*                   >> `∀b1 q1. infBranchOf r2 b1 ∧ branchFixP b1 q1 *)
(*                      ⇒ q1 ∉ aut.final` by metis_tac[BRANCH_ACC_LEMM] *)
(*                   >> rpt strip_tac *)
(*                   >> `?b2. infBranchOf r2 b2 *)
(*                      ∧ (branchFixP b2 q \/ ((q = s') ∧ branchFixP b2 x))` *)
(*                         suffices_by ( *)
(*                          Cases_on `aut` >> fs[mergeState_def] *)
(*                          >> `q ∈ *)
(*                     (ALTER_A (f DIFF {x}) (IMAGE *)
(*                        (replaceState x *)
(*                         (@s. s ∈ f ∧ s ≠ x ∧ equivalentStates f1 f3 s x)) f0) *)
(*                   (replaceState x *)
(*                    (@s. s ∈ f ∧ s ≠ x ∧ equivalentStates f1 f3 s x) f1) f2 *)
(*                   (replaceBy f3 x *)
(*                    (@s. s ∈ f ∧ s ≠ x ∧ equivalentStates f1 f3 s x))).final` *)
(*                             by metis_tac[] >> fs[replaceState_def] *)
(*                          >> Cases_on `x ∈ f1` >> fs[] *)
(*                            >- metis_tac[] *)
(*                            >- (`q ∈ f1` by metis_tac[equivalentStates_def] *)
(*                                >> metis_tac[]) *)
(*                            >- (rpt strip_tac >> Cases_on `infBranchOf r2 b2` *)
(*                                >- (fs[] >> strip_tac *)
(*                                    >- metis_tac[] *)
(*                                    >- (Cases_on `q= s'` >> fs[] *)
(*                                        >> metis_tac[equivalentStates_def] *)
(*                                       ) *)
(*                                   ) *)
(*                                >- fs[] *)
(*                               ) *)
(*                   ) *)
(*                   >> Cases_on `~(q = s')` *)
(*                    >- (fs[branchFixP_def] *)
(*                        >> `infBranchSuffOf r2 i (\a. q)` by ( *)
(*                             simp[infBranchSuffOf_def] >> rpt strip_tac *)
(*                              >- (`q ∈ new_run.V i` by ( *)
(*                                   fs[infBranchOf_def,validAARunFor_def] *)
(*                                   >> `b i = q` by fs[] *)
(*                                   >> Cases_on `i = 0` >> fs[] *)
(*                                   >> `?j. SUC j = i` by *)
(*                                        (Cases_on `i` >> fs[]) *)
(*                                   >> `j + 1 = i` by simp[] *)
(*                                   >> metis_tac[SUBSET_DEF] *)
(*                                   ) *)
(*                                  >> metis_tac[] *)
(*                                 ) *)
(*                              >- (`(a + i) + 1 >= i` by simp[] *)
(*                                   >> `b (a + i + 1) = q` by fs[] *)
(*                                   >> `b (a + i) = q` by fs[] *)
(*                                   >> `q ∈ new_run.E (a + i,q)` *)
(*                                       by metis_tac[infBranchOf_def] *)
(*                                   >> qunabbrev_tac `new_run` *)
(*                                   >> qunabbrev_tac `repl_run` *)
(*                                   >> fs[run_restr_def,run_restr_E_def] *)
(*                                   >> `q ∈ (replace_run r2 x s').E (a + i,q)` *)
(*                                      by metis_tac[MEMBER_NOT_EMPTY] *)
(*                                   >> fs[replace_run_def] *)
(*                                   >> `q ∈ replaceState x s' (r2.E (a + i,q))` *)
(*                                       by metis_tac[] >> POP_ASSUM mp_tac *)
(*                                   >> simp[replaceState_def] >> rpt strip_tac *)
(*                                   >> Cases_on `x ∈ r2.E (a + i,q)` >> fs[] *)
(*                                   >> rw[] *)
(*                                 ) *)
(*                         ) *)
(*                        >> qabbrev_tac `infSuff = (\a:num. q)` *)
(*                        >> `∃b'. infBranchOf r2 b' ∧ ∀j. infSuff j = b' (j + i)` *)
(*                             by metis_tac[BRANCH_SUFF_LEMM] *)
(*                        >> qexists_tac `b'` >> fs[] >> qexists_tac `i` >> fs[] *)
(*                        >> qunabbrev_tac `infSuff` >> rw[] *)
(*                         >- (fs[] >> metis_tac[DECIDE ``i + 0 = i``]) *)
(*                         >- (fs[] >> `i <= m` by simp[] *)
(*                             >> `?p. p + i = m` by metis_tac[LESS_EQ_ADD_EXISTS] *)
(*                             >> metis_tac[ADD_COMM] *)
(*                            ) *)
(*                       ) *)
(*                    >- (fs[branchFixP_def] *)
(*                        >> Cases_on `?a. ~(s' ∈ r2.E (a + i,s'))` *)
(*                      (* >- (fs[] >> rw[] *) *)
(*                      (*     >> `q ∈ new_run.E (a + i,q)` by ( *) *)
(*                      (*         fs[infBranchOf_def] >> `a + i >= i` by simp[] *) *)
(*                      (*         >> `a + i + 1 >= i` by simp[] *) *)
(*                      (*         >> `b (a + i) = q` by fs[] *) *)
(*                      (*         >> `b (a + i + 1) = q` by simp[] *) *)
(*                      (*         >> fs[] >> rw[] >> metis_tac[ADD_ASSOC] *) *)
(*                      (*      ) *) *)
(* (*                          >> Cases_on `q ∈ r2.V (a+i)` *) *)
(* (*                           >- (`x ∈ r2.E (a + i, q)` by ( *) *)
(* (*                               qunabbrev_tac `new_run` >> fs[run_restr_def] *) *)
(* (*                               >> fs[run_restr_E_def] *) *)
(* (*                               >> `q ∈ repl_run.E (a + i,q)` *) *)
(* (*                                  by metis_tac[MEMBER_NOT_EMPTY] *) *)
(* (*                               >> qunabbrev_tac `repl_run` >> fs[replace_run_def] *) *)
(* (*                               >> `q ∈ replaceState x q (r2.E (a + i,q))` *) *)
(* (*                                  by metis_tac[] *) *)
(* (*                               >> fs[replaceState_def] >> metis_tac[] *) *)
(* (*                               ) *) *)
(* (*                               >> `infBranchSuffOf r2 (a+i+1) (\p. x)` by ( *) *)
(* (*                                   simp[infBranchSuffOf_def] >> strip_tac *) *)
(* (*                                   >- (fs[validAARunFor_def] *) *)
(* (*                                       >> metis_tac[SUBSET_DEF,ADD_ASSOC]) *) *)
(* (*                                   >- (`!p. (x ∈ r2.E (a+i+p+1,x)) *) *)
(* (*                                          ∧ (x ∈ r2.V (a+i+p+1))` *) *)
(* (*                                        suffices_by fs[] *) *)
(* (*                                       >> Induct_on `p` >> fs[] *) *)
(* (*                                       >- (rpt strip_tac >> fs[validAARunFor_def] *) *)
(* (*                                         >> `x ∈ r2.V(a+i+1)` *) *)
(* (*                                                  by metis_tac[SUBSET_DEF] *) *)
(* (*                                         >> `q ∈ new_run.E (a+i+1,q)` by ( *) *)
(* (*                                                fs[infBranchOf_def] *) *)
(* (*                                                >> `b (a+i+1) = q` by simp[] *) *)
(* (*                                                >> `b (a+i+1+1) = q` by simp[] *) *)
(* (*                                                >> metis_tac[ADD_ASSOC]) *) *)
(* (*                                         >> qunabbrev_tac `new_run` *) *)
(* (*                                         >> fs[run_restr_def,run_restr_E_def] *) *)
(* (*                                         >> `q ∈ repl_run.E (a+i+1,q)` *) *)
(* (*                                         by metis_tac[MEMBER_NOT_EMPTY,ADD_ASSOC] *) *)
(* (*                                         >> qunabbrev_tac `repl_run` *) *)
(* (*                                         >> fs[replace_run_def,replaceState_def] *) *)
(* (*                                         >> Cases_on `x ∈ r2.E(a+i+1,q)` *) *)
(* (*                                         >- (POP_ASSUM mp_tac >> POP_ASSUM mp_tac *) *)
(* (*                                             >> simp[] *) *)
(* (*                                             >> metis_tac[] *) *)
(* (* ) *) *)
(* (*                                      ) *) *)
(* (* ) *) *)
(*                          >- (fs[] *)
(*                             >> qabbrev_tac `P = \n. ~(s' ∈ r2.E (n + i, s'))` *)
(*                             >> qabbrev_tac `N = $LEAST P` *)
(*                             >> `(!n. n < N ==> ~ P n) ∧ P ($LEAST P)` by ( *)
(*                                  qunabbrev_tac `N` *)
(*                                  >> metis_tac[LEAST_EXISTS_IMP,EXISTS_THM] *)
(*                              ) *)
(*                             >> rw[] *)
(*                             >> `q ∈ new_run.E (N + i,q)` by ( *)
(*                                  fs[infBranchOf_def] >> `N + i >= i` by simp[] *)
(*                                  >> `N + i + 1 >= i` by simp[] *)
(*                                  >> `b (N + i) = q` by metis_tac[] *)
(*                                  >> `b (N + i + 1) = q` by simp[] *)
(*                                  >> fs[] >> metis_tac[ADD_ASSOC] *)
(*                              ) *)
(*                             >> Cases_on `q ∈ r2.V i` *)
(*                             >- (`!n. n <= N ==> q ∈ r2.V (n + i)` *)
(*                                  by ( *)
(*                                  Induct_on `n` >> rpt strip_tac >> fs[] *)
(*                                  >> `n < N` by simp[] *)
(*                                  >> `~P n` by fs[] >> qunabbrev_tac `P` *)
(*                                  >> fs[] >> fs[validAARunFor_def] *)
(*                                  >> `q ∈ r2.V (i + n + 1)` suffices_by *)
(*                                         metis_tac[ADD_SUC,ADD_COMM,SUC_ONE_ADD] *)
(*                                  >> metis_tac[SUBSET_DEF] *)
(*                                  ) *)
(*                               >> `q ∈ r2.V (N + i)` *)
(*                                 by metis_tac[DECIDE ``N <= N``] *)
(*                               >> `x ∈ r2.E (i + N, q)` by ( *)
(*                                 `q ∈ r2.V (i + N)` by fs[] *)
(*                                 >> `~(q ∈ r2.E (N + i, q))` by ( *)
(*                                     qunabbrev_tac `P` >> qunabbrev_tac `N` *)
(*                                     >> fs[] >> metis_tac[ADD_COMM] *)
(*                                 ) *)
(*                                 >> qunabbrev_tac `new_run` *)
(*                                 >> qunabbrev_tac `repl_run` *)
(*                                 >> fs[run_restr_def, run_restr_E_def] *)
(*                                 >> `q *)
(*                                      ∈ (replace_run r2 x (q)).E (N + i,q)` *)
(*                                    by metis_tac[MEMBER_NOT_EMPTY] *)
(*                                 >> fs[replace_run_def] *)
(*                                 >> `q ∈ *)
(*                                      replaceState x (q) (r2.E (N + i,q))` *)
(*                                    by metis_tac[] *)
(*                                 >> POP_ASSUM mp_tac >> simp[replaceState_def] *)
(*                                 >> rpt strip_tac >> metis_tac[] *)
(*                              ) *)
(*                               >> `infBranchSuffOf r2 (N+i+1) (\p. x)` by ( *)
(*                                   >> fs[infBranchSuffOf_def] >> strip_tac *)
(*                                    >- (fs[validAARunFor_def] *)
(*                                        >> metis_tac[ADD_ASSOC,SUBSET_DEF]) *)
(*                                    >- ( *)


(* `q ∈ r2.E (N+i+1,q)` by ( *)
(*                                     `q ∈ new_run.E (N+i+1,q)` by ( *)
(*                                       fs[infBranchOf_def] *)
(*                                       >> `b (N+i+1+1) = q` by simp[] *)
(*                                       >> `b (N+i+1) = q` by simp[] *)
(*                                       >> metis_tac[ADD_ASSOC] *)
(*                                     ) *)
(*                                     >> qunabbrev_tac `new_run` *)
(*                                     >> fs[run_restr_def, run_restr_E_def] *)
(*                                     >> `q ∈ repl_run.E (N+i+1,q)` *)
(*                                        by metis_tac[MEMBER_NOT_EMPTY,ADD_ASSOC] *)
(*                                     >> qunabbrev_tac `repl_run` *)
(*                                     >> fs[replace_run_def,replaceState_def] *)
(*                                     >> `~(q ∈ r2.E (N+i+1,x))` by ( *)
(*                                          fs[isWeakAlterA_def] *)
(*                                          >> `(x,q) ∈ ord` by ( *)
(*                                       fs[isWeakWithOrder_def,validAARunFor_def] *)
(*                                       >> metis_tac[SUBSET_DEF] *)
(*                                          ) *)
(*                                          >> CCONTR_TAC >> fs[] *)
(*                                          >> `(q,x) ∈ ord` by ( *)
(*                                       fs[isWeakWithOrder_def,validAARunFor_def] *)
(*                                       >> `x ∈ r2.V (N+i+1)` by *)
(*                                          metis_tac[ADD_ASSOC,SUBSET_DEF] *)
(*                                       >> metis_tac[SUBSET_DEF,ADD_ASSOC]) *)
(*                                     ) *)
(*                                     >> fs[isWeakWithOrder_def,partial_order_def] *)
(*                                     >> metis_tac[antisym_def] *)
(*                                   ) *)
(*                                   ) *)
(*                                   >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac *)
(*                                   >> simp[] >> Cases_on `x ∈ r2.E *)

(*                             >> `!n. x ∈ r2.E (i + N + n + 1,x)` by ( *)
(*                                  Induct_on `n` >> rpt strip_tac >> fs[] *)
(*                                  >- (`x ∈ r2.V (N + i + 1)` *)
(*                                       by metis_tac[validAARunFor_def,SUBSET_DEF] *)
(*                                      >> `b (N + i + 1) ∈ new_run.V (N + i + 1)` *)
(*                                          by metis_tac[BRANCH_V_LEMM] *)
(*                                      >> `b i ∈ new_run.V (N + i + 1)` by ( *)
(*                                           metis_tac[DECIDE ``N + i + 1 >= i``] *)
(*                                      ) *)
(*                                      >> `((b i ∈ r2.V (N + i + 1)) *)
(*                                        \/ (x ∈ r2.V (N + i + 1)))` *)
(*                                         by metis_tac[] *)
(*                                      >- (`r2.E (N + i + 1,b i) *)
(*                                                  ⊆ r2.E (N + i + 1,x)` by ( *)
(*                                           `x ∈ r2.V (N + i + 1)` by *)
(*                                              metis_tac[validAARunFor_def] *)
(*                                           >> metis_tac[SET_EQ_SUBSET] *)
(*                                          ) *)
(*                                          >> `x ∈ r2.E (N + i + 1,b i)` by ( *)
(*                                              `b i ∈ new_run.E (N + i + 1, b i)` *)
(*                                              by (fs[infBranchOf_def] *)
(*                                                  >> `b (N + i + 1 + 1) = b i` *)
(*                                                     by fs[] *)
(*                                                  >> `b (N + i + 1) = b i` *)
(*                                                     by fs[] *)
(*                                                  >> metis_tac[ADD_ASSOC] *)
(*                                                 ) *)
(*                                              >> `b i ∈ r2.E (N + i + 1,b i)` *)
(*                                                  by (qunabbrev_tac `P` >> fs[] *)
(*                                                     >>  *)
(* ) *)




(* ) *)
(*                                     ) *)


(* ) *)




(*                             >> `infBranchSuffOf run (a + i + 1) (\n. x)` by ( *)
(*                               simp[infBranchSuffOf_def] >> rpt strip_tac *)
(*                               >- (fs[validAARunFor_def] *)
(*                                   >> metis_tac[SUBSET_DEF,ADD_ASSOC]) *)
(*                               >- (`q ∈ new_run.E (a + i + n + 1, q)` by ( *)
(*                                        fs[infBranchOf_def] *)
(*                                        >> `a + i + n + 1 >= i` by simp[] *)
(*                                        >> `a + i + n + 1 + 1 >= i` by simp[] *)
(*                                        >> `b (a + i + n + 1) = q` by metis_tac[] *)
(*                                        >> `b (a + i + n + 1 + 1) = q` *)
(*                                            by metis_tac[] *)
(*                                        >> metis_tac[ADD_ASSOC] *)
(*                                  ) *)
(*                                  >> qunabbrev_tac `new_run` *)
(*                                  >> qunabbrev_tac `repl_run` *)
(*                                  >> fs[run_restr_def, run_restr_E_def] *)
(*                                  >> `q ∈ (replace_run run x q).E *)
(*                                           (a + (i + (n + 1)),q)` *)
(*                                     by metis_tac[MEMBER_NOT_EMPTY] *)
(*                                  >> fs[replace_run_def] *)
(*                                  >> `!n. a + i <= n ==> ~(q ∈ run.V n)` by ( *)










(* ) *)


(* ) *)



(* )) *)



(* ) *)


(* ) *)



(* ) *)
(* ) *)


val _ = export_theory();
