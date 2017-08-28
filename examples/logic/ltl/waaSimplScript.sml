open HolKernel Parse bossLib boolLib pairTheory relationTheory set_relationTheory pred_setTheory arithmeticTheory

open alterATheory

val _ = new_theory "waaSimpl"

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

val reduced_E_def = Define`
  reduced_E run trans word (i,q) =
    let a = $@ (\a. (a,run.E (i,q)) ∈ trans q ∧ at word i ∈ a)
    in if ?(a',q'). (a',q') ∈ trans q ∧ trans_implies (a',q') (a,run.E (i,q))
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
      ==> (alterA_lang aut = alterA_lang (reduceTransSimpl aut))``,
   rw[SET_EQ_SUBSET, SUBSET_DEF] >> rpt strip_tac >> fs[alterA_lang_def]
    >- (qexists_tac `reduced_run run x aut.trans` >> fs[runForAA_def]
        >> rpt strip_tac
        >> `!i. (reduced_run run x aut.trans).V i ⊆ run.V i` by (
             Induct_on `i` >> simp[SUBSET_DEF] >> rpt strip_tac
             >> fs[reduced_run_def, run_restr_def, run_restr_V_def,reduced_E_def]
             >> Cases_on `∃(a',q').
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
                   >> `minE (q',r)` by metis_tac[SELECT_THM]
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
                       >> `minE (q'',r)` by metis_tac[SELECT_THM]
                       >> qunabbrev_tac `minE` >> fs[minimal_elements_def,rrestrict_def]
                       >> fs[rel_to_reln_def, trans_implies_def]
                       >> qabbrev_tac `a'' =
                              (@a. (a,run.E (i,q)) ∈ aut.trans q ∧ at x i ∈ a)`
                       >> `(a'', run.E (i,q)) ∈ aut.trans q ∧ at x i ∈ a''` by (
                            fs[validAARunFor_def]
                            >> `q ∈ run.V i` by metis_tac[SUBSET_DEF]
                            >> metis_tac[SELECT_THM,IN_DEF]
                        )
                       >- (qexists_tac `q''` >> Cases_on `aut` >> fs[reduceTransSimpl_def]
                           >> fs[removeImplied_def]
                           >> rpt strip_tac
                            >- (CCONTR_TAC >> fs[] >> metis_tac[])
                            >- metis_tac[SUBSET_TRANS,SUBSET_DEF])
                       >- (`∃(a',q'). (a',q') ∈ aut.trans q ∧ a'' ⊆ a' ∧ q' ⊆ run.E (i,q)`
                            suffices_by metis_tac[] >> rpt strip_tac
                            >> simp[PEXISTS_THM] >> qexists_tac `(a'',run.E (i,q))`)

                      )
                   >- (fs[] >> rw[]
                         >- (Cases_on `aut` >> fs[validAARunFor_def, reduceTransSimpl_def]
                             >> fs[removeImplied_def] >> `q ∈ run.V i` by fs[SUBSET_DEF]
                             >> `∃a. (a,run.E (i,q)) ∈ f3 q ∧ at x i ∈ a` by fs[]
                             >> qabbrev_tac `a'' =
                                  (@a. (a,run.E (i,q)) ∈ f3 q ∧ at x i ∈ a)`
                             >> `(a'', run.E (i,q)) ∈ f3 q ∧ at x i ∈ a''`
                                   by metis_tac[SELECT_THM,IN_DEF]
                             >> qexists_tac `a''` >> fs[]
                             >> strip_tac >> Cases_on `t'` >> CCONTR_TAC
                             >> fs[]
                             >> metis_tac[PEXISTS_T]




)
                 )
              >- ()


)

)
)
)


)


)



