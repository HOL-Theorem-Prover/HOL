open HolKernel Parse bossLib boolLib pred_setTheory relationTheory arithmeticTheory prim_recTheory pairTheory set_relationTheory whileTheory

open generalHelpersTheory ltlTheory wordTheory alterATheory

val _ = new_theory "ltl2waa"

(*
  Defining the translation from LTL to WAA
 *)

val initForms_def = Define `(initForms f = tempDNF f)`;

val finalForms_def = Define
  `finalForms f = {U f1 f2 | (U f1 f2) ∈ tempSubForms f}`;

(*
  transition function of the automaton
*)

val trans_def = Define
   `(trans Σ (VAR a) = {((char Σ a), {})})
 /\ (trans Σ (N_VAR a) = {Σ DIFF (char Σ a), {}})
 /\ (trans Σ (CONJ f1 f2) = d_conj (trans Σ f1) (trans Σ f2))
 /\ (trans Σ (DISJ f1 f2) = (trans Σ f1) ∪ (trans Σ f2))
 /\ (trans Σ (X f) = \s. ?e. (s = (Σ, e)) /\ (e ∈ tempDNF f))
 /\ (trans Σ (U f1 f2) = (trans Σ f2) ∪ (d_conj (trans Σ f1) {(Σ,{U f1 f2})}))
 /\ (trans Σ (R f1 f2) = d_conj (trans Σ f2) ((trans Σ f1) ∪ {(Σ,{R f1 f2})}))`;

val TRANS_ALPH_LEMM = store_thm
  ("TRANS_ALPH_LEMM",
   ``!a e f Σ. (a,e) ∈ trans Σ f ==> a ⊆ Σ``,
    Induct_on `f` >> fs[trans_def, char_def, SUBSET_DEF,d_conj_def]
    >> rpt strip_tac >> metis_tac[IN_INTER]
  );

val TRANS_TEMPDNF_LEMM = store_thm
  ("TRANS_TEMPDNF_LEMM",
   “!a s Σ f.
      ((a,s) ∈ trans Σ f) ==>
      ?e t a'. (s = BIGUNION t) /\ (e ∈ tempDNF f)
               /\ (a = BIGINTER a')
               /\ (!t'. t' ∈ t ==>
                        ?q a''. a'' ∈ a' /\ q ∈ e /\ (a'',t') ∈ trans Σ q)
               /\ !q. q ∈ e ==>
                      ?t' a''. a'' ∈ a' /\ (t' ∈ t) /\ (a'',t') ∈ trans Σ q”,
   Induct_on `f` >> fs[trans_def, tempDNF_def,BIGUNION,SUBSET_DEF] >> rpt strip_tac
    >- (qexists_tac `{{}}` >> qexists_tac `{char Σ a}` >> fs[])
    >- (qexists_tac `{{}}` >> qexists_tac `{Σ DIFF char Σ a}` >> fs[])
    >- (dsimp[] >> metis_tac[])
    >- (dsimp[] >> metis_tac[])
    >- (fs[d_conj_def] >>
        rename [‘(a1,e1) ∈ trans Σ f1’, ‘a = a1 ∩ a2’, ‘(a2,e2) ∈ trans Σ f2’]
        >> `∃e t a'.
               (e1 = {x | ∃s. s ∈ t ∧ x ∈ s}) ∧ e ∈ tempDNF f1 ∧
               (a1 = BIGINTER a') ∧
               (∀t'.
                 t' ∈ t ⇒ ∃q a''. a'' ∈ a' ∧ q ∈ e ∧ (a'',t') ∈ trans Σ q) ∧
               ∀q. q ∈ e ⇒ ∃t' a''. a'' ∈ a' ∧ t' ∈ t ∧ (a'',t') ∈ trans Σ q`
           by metis_tac[]
        >> `∃e' t' a''.
               (e2 = {x | ∃s. s ∈ t' ∧ x ∈ s}) ∧ e' ∈ tempDNF f2 ∧
               (a2 = BIGINTER a'') ∧
               (∀tt.
                 tt ∈ t' ⇒ ∃q aa. aa ∈ a'' ∧ q ∈ e' ∧ (aa,tt) ∈ trans Σ q) ∧
               ∀q. q ∈ e' ⇒ ∃tt aa. aa ∈ a'' ∧ tt ∈ t' ∧ (aa,tt) ∈ trans Σ q`
           by metis_tac[]
       >> qexists_tac `e ∪ e'` >> fs[] >> qexists_tac `t ∪ t'`
       >> dsimp[] >> fs[] >> rpt strip_tac
       >> qexists_tac `a' ∪ a''`
       >> qexists_tac `e` >> qexists_tac `e'` >> fs[]
       >> fs[UNION_DEF] >> rpt strip_tac
         >- (rename1 ‘t'' ∈ t’ >>
             `∃q a''. a'' ∈ a' ∧ q ∈ e ∧ (a'',t'') ∈ trans Σ q`
                by metis_tac[] >>
             `∃q a'''.
                    ((a''' ∈ a') ∨ (a''' ∈ a'')) ∧ q ∈ e ∧
                    (a''',t'') ∈ trans Σ q` suffices_by metis_tac[]
              >> qexists_tac `q` >> qexists_tac `a'''` >> fs[])
         >- (rename1 ‘t'' ∈ t'’ >>
             `∃q a'''. a''' ∈ a'' ∧ q ∈ e' ∧ (a''',t'') ∈ trans Σ q`
                by metis_tac[]
              >> `∃q a'''.
                    ((a''' ∈ a') ∨ (a''' ∈ a'')) ∧ q ∈ e' ∧
                    (a''',t'') ∈ trans Σ q` suffices_by metis_tac[]
              >> qexists_tac `q` >> qexists_tac `a'''` >> fs[]
            )
         >- (`∃t' a''. a'' ∈ a' ∧ t' ∈ t ∧ (a'',t') ∈ trans Σ q` by metis_tac[]
             >> `(∃t'' a'''.
                   (a''' ∈ a' ∨ a''' ∈ a'') ∧ t'' ∈ t ∧ (a''',t'') ∈ trans Σ q)`
                suffices_by metis_tac[]
             >> qexists_tac `t''` >> qexists_tac `a'''` >> fs[]
            )
         >- (`∃t'' a'''. a''' ∈ a'' ∧ t'' ∈ t' ∧ (a''',t'') ∈ trans Σ q` by metis_tac[]
             >> `(∃t'' a'''.
                   (a''' ∈ a' ∨ a''' ∈ a'') ∧ t'' ∈ t' ∧ (a''',t'') ∈ trans Σ q)`
                suffices_by metis_tac[]
             >> qexists_tac `t''` >> qexists_tac `a'''` >> fs[])
       )
    >- (qexists_tac `{s}` >> qexists_tac `{a}` >> fs[])
    >- (qexists_tac `{s}` >> qexists_tac `{a}` >> fs[])
    >- (fs[d_conj_def] >> qexists_tac `{s}` >> qexists_tac `{a1 ∩ Σ}`
        >> fs[] >> rpt strip_tac
         >- (fs[UNION_DEF])
         >- (`∃a1' e1'.
             ((a1 ∩ Σ = a1' ∩ Σ) ∧ (e1 ∪ {U f f'} = e1' ∪ {U f f'})) ∧
             (a1',e1') ∈ trans Σ f` suffices_by metis_tac[]
             >> qexists_tac `a1` >> qexists_tac `e1` >> fs[])
       )
    >- (fs[d_conj_def]
        >> qexists_tac `{s}` >> qexists_tac `{a1 ∩ a2}`
        >> fs[] >> rpt strip_tac
          >- (fs[UNION_DEF])
          >- (qexists_tac `a1` >> qexists_tac `a2` >> qexists_tac `e1`
              >> qexists_tac `e2` >> fs[])
          >- (fs[UNION_DEF])
          >- (qexists_tac `a1` >> qexists_tac `a2` >> qexists_tac `e1`
              >> qexists_tac `e2` >> fs[]
             )
       )
  );

val TRANS_REACHES_SUBFORMS = store_thm
 ("TRANS_REACHES_SUBFORMS",
  ``!s a d Σ. ((a,d) ∈ trans Σ s)
      ==> !q. (q ∈ d) ==> ((q,s) ∈ TSF)``,
  `!s a d Σ. ((a,d) ∈ trans Σ s)
          ==> (d ⊆ tempSubForms s)` suffices_by metis_tac[SUBSET_DEF,TSF_def,IN_DEF]
  >> Induct_on `s` >> (rpt strip_tac >> fs[trans_def])
  >- (`!s s'. tempSubForms s ⊆ tempSubForms (DISJ s s')`
       by metis_tac[tempSubForms_def,SUBSET_UNION]
       >> `d ⊆ (tempSubForms s)` by metis_tac[]
      >> fs[SUBSET_DEF] >> rpt strip_tac)
  >- (`!s s'. tempSubForms s ⊆ tempSubForms (DISJ s' s)`
       by metis_tac[tempSubForms_def,SUBSET_UNION]
      >> `d ⊆ (tempSubForms s')` by metis_tac[]
      >> fs[SUBSET_DEF] >> rpt strip_tac
     )
  >- (fs[d_conj_def]
      >> `e1 ⊆ tempSubForms s` by metis_tac[]
      >> `e2 ⊆ tempSubForms s'` by metis_tac[]
      >> `!s s'. tempSubForms s ⊆ tempSubForms (CONJ s' s)`
          by metis_tac[tempSubForms_def, SUBSET_UNION]
      >> `!s s'. tempSubForms s' ⊆ tempSubForms (CONJ s' s)`
          by metis_tac[tempSubForms_def, SUBSET_UNION]
      >> fs[SUBSET_DEF] >> rpt strip_tac
     )
  >- (`d ⊆ tempSubForms s` by metis_tac[TEMPDNF_TEMPSUBF]
      >> `d ⊆ tempSubForms (X s)`
          suffices_by metis_tac[SUBSET_UNION, SUBSET_TRANS]
      >> `!s. tempSubForms s ⊆ tempSubForms (X s)` by rw[tempSubForms_def]
      >> metis_tac[SUBSET_TRANS])
  >- (`!s s'. tempSubForms s' ⊆ tempSubForms (U s s')`
        by metis_tac[tempSubForms_def,SUBSET_UNION]
       >> `tempSubForms s' ⊆ tempSubForms (U s s')` by metis_tac[]
       >> `d ⊆ (tempSubForms s')` by metis_tac[]
       >> fs[SUBSET_DEF] >> rpt strip_tac
      )
   >- (fs[d_conj_def] >> `e1 ⊆ (tempSubForms s)` by metis_tac[]
       >> `!s s'. tempSubForms (U s s') = {U s s'} ∪ tempSubForms s ∪ tempSubForms s'`
           by rw[tempSubForms_def]
       >> `tempSubForms (U s s') = {U s s'} ∪ tempSubForms s ∪ tempSubForms s'`
           by metis_tac[]
       >> fs[SUBSET_DEF] >> rpt strip_tac
      )
   >- (fs[d_conj_def] >> `e1 ⊆ (tempSubForms s')` by metis_tac[]
       >> `!s s'. tempSubForms (R s s') = {R s s'} ∪ tempSubForms s ∪ tempSubForms s'`
           by rw[tempSubForms_def]
           >- (`e2 ⊆ (tempSubForms s)` by metis_tac[]
               >> `tempSubForms (R s s') = {R s s'} ∪ tempSubForms s ∪ tempSubForms s'`
                   by metis_tac[]
               >> fs[SUBSET_DEF] >> rpt strip_tac
              )
           >- (fs[SUBSET_DEF] >> rpt strip_tac)
      )
  );


(*
  Defining the automaton
*)

val ltl2vwaa_free_alph_def = Define
  `ltl2vwaa_free_alph Σ f =
        ALTER_A
           (tempSubForms f)
           Σ
           (trans Σ)
           (initForms f)
           (finalForms f)`;

val ltl2vwaa_def = Define `ltl2vwaa f = ltl2vwaa_free_alph (POW (props f)) f`;

val LTL2WAA_ISVALID = store_thm
  ("LTL2WAA_ISVALID",
   ``!f. isValidAlterA (ltl2vwaa f)``,
   strip_tac >> fs[isValidAlterA_def, ltl2vwaa_def, ltl2vwaa_free_alph_def]
   >> rpt strip_tac
   >- (fs[initForms_def, tempSubForms_def, POW_DEF, SUBSET_DEF]
       >> rpt strip_tac >> `x ⊆ tempSubForms f` by metis_tac[TEMPDNF_TEMPSUBF]
       >> fs[SUBSET_DEF])
   >- (fs[finalForms_def, tempSubForms_def, POW_DEF, SUBSET_DEF]
       >> rpt strip_tac >> fs[])
   >- (`!q. (q ∈ d) ==> ((q,s) ∈ TSF)` by metis_tac[TRANS_REACHES_SUBFORMS]
       >> `!q. (q ∈ d) ==> ((q,f) ∈ TSF)` suffices_by metis_tac[SUBSET_DEF,TSF_def,IN_DEF]
       >> `(s,f) ∈ TSF` by metis_tac[TSF_def,IN_DEF]
       >> rpt strip_tac
       >> `(q,s) ∈ TSF` by metis_tac[]
       >> metis_tac[TSF_TRANS_LEMM,transitive_def,IN_DEF]
      )
   >- (`!s' a' d'. s' ∈ subForms f ∧ (a',d') ∈ trans (POW (props f)) s'
               ==> a' ⊆ (POW (props f))` suffices_by metis_tac[TSF_IMPL_SF]
       >> Induct_on `s'` >> fs[trans_def,char_def,SUBSET_DEF] >> rpt strip_tac
       >> fs[d_conj_def]
       >> metis_tac[subForms_def, IN_UNION, SUBFORMS_REFL, SUBFORMS_TRANS,IN_INTER]
      )
  );

val LTL2WAA_ISWEAK_LEMM = store_thm
  ("LTL2WAA_ISWEAK_LEMM",
   ``!f g. isVeryWeakAlterA (ltl2vwaa_free_alph (POW (props f)) g)``,
   rpt strip_tac
   >> fs[isVeryWeakAlterA_def, isVeryWeakWithOrder_def, ltl2vwaa_def, ltl2vwaa_free_alph_def]
   >> exists_tac ``rrestrict TSF (tempSubForms g)``
   >> rpt strip_tac >> fs[TSF_PO]
   >> `!q. (q ∈ d) ==> ((q,s) ∈ TSF)`
       by metis_tac[TRANS_REACHES_SUBFORMS]
   >> `(s',s) ∈  TSF` by metis_tac[]
   >> fs[in_rrestrict]
   >> `(s,g) ∈ TSF` by metis_tac[TSF_def,IN_DEF]
   >> metis_tac[TSF_TRANS_LEMM, transitive_def,TSF_def,IN_DEF]
  );

val LTL2WAA_ISWEAK = store_thm
  ("LTL2WAA_ISWEAK",
   ``!f. isVeryWeakAlterA (ltl2vwaa f)``,
   strip_tac >> fs[ltl2vwaa_def] >> metis_tac[LTL2WAA_ISWEAK_LEMM]
  );

val LTL2WAA_ISFINITE = store_thm
  ("LTL2WAA_ISFINITE",
  ``!f g. FINITE (ltl2vwaa_free_alph (POW (props f)) g).states``,
  fs[ltl2vwaa_free_alph_def] >> metis_tac[TSF_FINITE]
  );

(*
  run constructions that are needed for the correctness proof
*)

val REPL_F2_LEMM = store_thm
  ("REPL_F2_LEMM",
   ``!a r f f' f1 f2 w l qs.(runForAA (ltl2vwaa_free_alph (POW (props f')) f2) r w
                 /\ (a,qs) ∈ trans (POW (props f')) f
                 /\ at w l ∈ a
                 /\ qs ⊆ r.E (l, f1)
                            )
                 ==> ?r'. runForAA (ltl2vwaa_free_alph (POW (props f')) f) r' (suff w l)``,
   rpt strip_tac
   >> `∃e t a'.
       (qs = BIGUNION t) ∧ e ∈ tempDNF f ∧ (a = BIGINTER a') ∧
       (∀t'. t' ∈ t ⇒ ∃q a''. a'' ∈ a' ∧ q ∈ e ∧ (a'',t') ∈ trans (POW (props f')) q) ∧
       ∀q. q ∈ e ⇒ ∃t' a''. a'' ∈ a' ∧ t' ∈ t ∧ (a'',t') ∈ trans (POW (props f')) q`
      by fs[TRANS_TEMPDNF_LEMM]
   >> `∀q. ?t'.
         q ∈ e ⇒
         ∃a''. a'' ∈ a' ∧ t' ∈ t ∧ (a'',t') ∈ trans (POW (props f')) q`
      by metis_tac[]
   >> `?h. !q. q ∈ e ⇒
        ∃a''. a'' ∈ a' ∧ (h q) ∈ t ∧ (a'',(h q)) ∈ trans (POW (props f')) q`
      by metis_tac[SKOLEM_THM]
   >> `!q. q ∈ e ==> h q ∈ t` by metis_tac[]
   >> `!q. q ∈ e ==> h q ⊆ qs` by metis_tac[SUBSET_BIGUNION_I]
   >> `!q. q ∈ e ==> h q ⊆ r.V (l + 1)`
        by metis_tac[SUBSET_TRANS, runForAA_def, validAARunFor_def]
   >> fs[] >> fs[runForAA_def]
   >> qabbrev_tac `r_int =
        ALTERA_RUN (\i. if i = 0 then e else r.V (i + l))
            (λ(i,q). if i = 0 then h q else r.E (i + l,q))`
   >> qabbrev_tac `r_new = run_restr e r_int`
   >> qexists_tac `r_new`
   >> `validAARunFor (ltl2vwaa_free_alph (POW (props f')) f) r_new (suff w l) ∧
       (∀b x. infBranchOf r_new b ∧ branchFixP b x
          ⇒ x ∉ (ltl2vwaa_free_alph (POW (props f')) f).final)`
       suffices_by metis_tac[BRANCH_ACC_LEMM, LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM]
   >> strip_tac
     >- (fs[validAARunFor_def]
         >> `!n. r_new.V (n + 1) ⊆ tempSubForms f ∩ r.V (n + 1 + l)` by
           (qunabbrev_tac `r_new` >> qunabbrev_tac `r_int` >> fs[ltl2vwaa_free_alph_def]
             >> Induct_on `n` >> fs[] >> rpt strip_tac
              >- (fs[SUBSET_DEF, run_restr_def, run_restr_V_def] >> rpt strip_tac
                  >> `e ⊆ tempSubForms f` by metis_tac[TEMPDNF_TEMPSUBF]
                  >> `SUC 0 = 1` by simp[]
                  >> `x ∈ run_restr_V e
                            (ALTERA_RUN (λi. if i = 0 then e else r.V (i + l))
                            (λ(i,q). if i = 0 then h q else r.E (i + l,q))) (SUC 0)`
                      by fs[]
                  >> fs[run_restr_V_def]
                  >> `∃a''. a'' ∈ a' ∧ (a'',h q) ∈ trans (POW (props f')) q`
                      by metis_tac[]
                  >> `(x,q) ∈ TSF` by metis_tac[TRANS_REACHES_SUBFORMS]
                  >> metis_tac[TSF_def,IN_DEF,TSF_TRANS_LEMM, transitive_def,SUBSET_DEF]
                 )
              >- (fs[SUBSET_DEF, run_restr_def, run_restr_V_def] >> rpt strip_tac
                    >> `SUC 0 = 1` by simp[]
                    >> `x ∈ run_restr_V e
                            (ALTERA_RUN (λi. if i = 0 then e else r.V (i + l))
                                 (λ(i,q). if i = 0 then h q else r.E (i + l,q))) (SUC 0)`
                        by fs[]
                    >> fs[run_restr_V_def]
                    >> metis_tac[]
                 )
              >- (fs[SUBSET_DEF, run_restr_def, run_restr_V_def] >> rpt strip_tac
                  >> `SUC n + 1 = SUC (n + 1)` by simp[]
                  >> `x ∈
                      run_restr_V e
                      (ALTERA_RUN (λi. if i = 0 then e else r.V (i + l))
                           (λ(i,q). if i = 0 then h q else r.E (i + l,q))) (SUC (n + 1))`
                      by metis_tac[]
                  >> fs[run_restr_V_def]
                  >> `q ∈ r.V (l + (n + 1)) /\ q ∈ tempSubForms f` by metis_tac[]
                  >> `?a''. (a'',r.E(l + (n + 1),q)) ∈ trans (POW (props f')) q`
                      by metis_tac[]
                  >> `(x,q) ∈ TSF` by metis_tac[TRANS_REACHES_SUBFORMS]
                  >> metis_tac[TSF_def, IN_DEF, TSF_TRANS_LEMM, transitive_def]
                 )
              >- (fs[SUBSET_DEF, run_restr_def, run_restr_V_def] >> rpt strip_tac
                  >> `SUC n + 1 = SUC (n + 1)` by simp[]
                  >> `x ∈
                      run_restr_V e
                      (ALTERA_RUN (λi. if i = 0 then e else r.V (i + l))
                           (λ(i,q). if i = 0 then h q else r.E (i + l,q))) (SUC (n + 1))`
                       by metis_tac[]
                  >> fs[run_restr_V_def]
                  >> `x ∈ r.V ((l + (n + 1)) + 1)` by metis_tac[]
                  >> rw[SUC_ONE_ADD] >> fs[]
                 )
           )
       >> rpt strip_tac
         >- (qunabbrev_tac `r_new` >> qunabbrev_tac `r_int`
             >> fs[ltl2vwaa_free_alph_def, initForms_def, tempDNF_def, run_restr_def]
             >> fs[run_restr_V_def])
         >- (Cases_on `i = 0`
              >- (qunabbrev_tac `r_new` >> qunabbrev_tac `r_int`
                  >> fs[ltl2vwaa_free_alph_def, run_restr_def, run_restr_V_def]
                  >> metis_tac[TEMPDNF_TEMPSUBF]
                 )
              >- (`?j. i = SUC j` by (Cases_on `i` >> fs[])
                  >> `i = j + 1` by simp[]
                  >> `r_new.V (j + 1) ⊆ tempSubForms f` by metis_tac[SUBSET_INTER]
                  >> fs[ltl2vwaa_free_alph_def] >> metis_tac[]
                 )
            )
         >- (Cases_on `i = 0` >> fs[ltl2vwaa_free_alph_def]
              >- (qunabbrev_tac `r_int` >> qunabbrev_tac `r_new`
                  >> fs[run_restr_def, run_restr_E_def, run_restr_V_def]
                  >> `∃a''. a'' ∈ a' ∧ (a'',h q) ∈ trans (POW (props f')) q`
                      by metis_tac[] >> qexists_tac `a''`
                  >> fs[AT_SUFF_LEMM]
                  )
              >- (`?j. i = SUC j` by (Cases_on `i` >> fs[])
                  >> `i = j + 1` by simp[]
                  >> `r_new.V (j + 1) ⊆ r.V (l + (j + 1))` by metis_tac[]
                  >> `q ∈ r.V (l + (j + 1))` by metis_tac[SUBSET_DEF]
                  >> qunabbrev_tac `r_int` >> qunabbrev_tac `r_new`
                  >> fs[run_restr_def, run_restr_E_def, run_restr_V_def]
                  >> `?a''. (a'',r.E((j + l + 1),q)) ∈ trans (POW (props f')) q
                               ∧ at w (j + l + 1) ∈ a''` by fs[]
                  >> qexists_tac `a''` >> fs[AT_SUFF_LEMM]
                  )
            )
         >- (Cases_on `i = 0` >> fs[ltl2vwaa_free_alph_def]
              >- (qunabbrev_tac `r_int` >> qunabbrev_tac `r_new`
                  >> fs[run_restr_def, run_restr_E_def, run_restr_V_def]
                  >> fs[SUBSET_DEF] >> rpt strip_tac
                  >> Cases_on `q ∈ e` >> fs[]
                  >> `1 = SUC 0` by simp[]
                  >> `x ∈
                       run_restr_V e
                        (ALTERA_RUN (λi. if i = 0 then e else r.V (i + l))
                          (λ(i,q). if i = 0 then h q else r.E (i + l,q))) (SUC 0)`
                     suffices_by metis_tac[]
                  >> fs[run_restr_V_def]
                  >> qexists_tac `h q` >> strip_tac >> fs[]
                  >> qexists_tac `q` >> fs[]
                 )
              >- (`?j. i = SUC j` by (Cases_on `i` >> fs[])
                  >> `i = j + 1` by simp[]
                  >> `r_new.V (j + 1) ⊆ r.V (l + (j + 1))` by metis_tac[]
                  >> fs[SUBSET_DEF] >> rpt strip_tac
                  >> qunabbrev_tac `r_int` >> qunabbrev_tac `r_new`
                  >> fs[run_restr_def, run_restr_E_def, run_restr_V_def]
                  >> Cases_on
                       `q ∈
                       run_restr_V e
                       (ALTERA_RUN (λi. if i = 0 then e else r.V (i + l))
                            (λ(i,q). if i = 0 then h q else r.E (i + l,q))) (j + 1)`
                  >> fs[]
                  >> `q ∈ r.V (j + (l + 1))` by fs[]
                  >> `j + 2 = SUC (j + 1)` by simp[]
                  >> `x ∈
                         run_restr_V e
                          (ALTERA_RUN (λi. if i = 0 then e else r.V (i + l))
                            (λ(i,q). if i = 0 then h q else r.E (i + l,q)))
                          (SUC (j + 1))`
                       suffices_by metis_tac[]
                  >> fs[run_restr_V_def] >> qexists_tac `r.E (j + (l + 1),q)`
                  >> rpt strip_tac >> fs[] >> qexists_tac `q` >> fs[]
                 )
            )
         >- (Cases_on `i = 0` >> fs[]
             >> `?j. i = SUC j` by (Cases_on `i` >> fs[])
             >> `i = j + 1` by simp[]
             >> `r_new.V (j + 1) ⊆ r.V (l + (j + 1))` by metis_tac[]
             >> fs[run_restr_def]
             >> qunabbrev_tac `r_new`
             >> fs[run_restr_V_def]
             >> `j + 1 = SUC j` by simp[] >> rw[]
             >> `q ∈ run_restr_V e r_int (SUC j)` by metis_tac[]
             >> fs[run_restr_V_def]
             >> qexists_tac `q'` >> fs[run_restr_E_def, run_restr_V_def]
            )
          )
     >- (`∀b x. infBranchOf r b ∧ branchFixP b x
            ⇒ x ∉ (ltl2vwaa_free_alph (POW (props f')) f2).final`
          by metis_tac[BRANCH_ACC_LEMM, LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM]
         >> rpt strip_tac >> fs[ltl2vwaa_free_alph_def, finalForms_def]
         >> `!aut. (let run_int =
                   ALTERA_RUN (λi. if i = 0 then e else r.V (i+l))
                       (λ(i,q). if i = 0 then h q else r.E (i+l,q))
               in
                   validAARunFor aut r w ∧ (∀q. q ∈ e ⇒ h q ⊆ r.V (1 + l)) ∧
                   infBranchOf (run_restr e run_int) b ∧ branchFixP b x ⇒
                    ∃b'. infBranchOf r b' ∧ branchFixP b' x)`
             by metis_tac[REPL_RUN_CONSTR_LEMM2]
         >> `∃b'. infBranchOf r b' ∧ branchFixP b' x` by metis_tac[ADD_COMM]
         >> `∀i. b' i ∈ r.V i` by metis_tac[BRANCH_V_LEMM]
         >> `?i. b' i = x` by metis_tac[branchFixP_def]
         >> `x ∈ r.V i` by metis_tac[]
         >> `r.V i ⊆ tempSubForms f2` by fs[validAARunFor_def]
         >> metis_tac[SUBSET_DEF]
        )
  );

val U_REPL_F1_LEMM = store_thm
  ("U_REPL_F1_LEMM",
  ``!a r f f1 f2 w l.(runForAA (ltl2vwaa_free_alph (POW (props f)) (U f1 f2)) r w
                   /\ (a,r.E (l,U f1 f2)) ∈
                      d_conj (trans (POW (props f)) f1) {(POW (props f), {U f1 f2})}
                   /\ at w l ∈ a)
     ==> ?r'.
          runForAA
          (ltl2vwaa_free_alph (POW (props f)) (CONJ f1 (X (U f1 f2))))
          r' (suff w l)``,
   rpt strip_tac >> fs[d_conj_def]
   >> `∃e t a'.
     (e1 = BIGUNION t) ∧ e ∈ tempDNF f1 ∧ (a1 = BIGINTER a') ∧
     (∀t'. t' ∈ t ⇒ ∃q a''. a'' ∈ a' ∧ q ∈ e ∧ (a'',t') ∈ trans (POW (props f)) q) ∧
     ∀q. q ∈ e ⇒ ∃t' a''. a'' ∈ a' ∧ t' ∈ t ∧ (a'',t') ∈ trans (POW (props f)) q`
     by fs[TRANS_TEMPDNF_LEMM]
   >> `∀q. ?t'.
       q ∈ e ⇒
       ∃a''. a'' ∈ a' ∧ t' ∈ t ∧ (a'',t') ∈ trans (POW (props f)) q`
      by metis_tac[]
   >> `?h. !q. q ∈ e ⇒
       ∃a''. a'' ∈ a' ∧ (h q) ∈ t ∧ (a'',(h q)) ∈ trans (POW (props f)) q`
       by metis_tac[SKOLEM_THM]
   >> `!q. q ∈ e ==> h q ∈ t` by metis_tac[]
   >> `!q. q ∈ e ==> h q ⊆ e1` by metis_tac[SUBSET_BIGUNION_I]
   >> qabbrev_tac `h' = (\q. if (q = X (U f1 f2)) then {U f1 f2} else h q)`
   >> qabbrev_tac `e' = e ∪ {X (U f1 f2)}`
   >> `!q. q ∈ e' ==> ((h' q = h q) \/ (h' q = {U f1 f2}))`
        by metis_tac[]
   >> `!q. q ∈ e' ==> h' q ⊆ (h q ∪ {U f1 f2})`
      by metis_tac[SUBS_UNION_LEMM]
   >> `!q. e ⊆ e'` by metis_tac[SUBSET_UNION]
   >> `!q. q ∈ e ==> h' q ⊆ h q ∪ {U f1 f2}`
        by metis_tac[SUBSET_DEF]
   >> `!q. q ∈ e ==> h' q ⊆ e1 ∪ {U f1 f2}` by metis_tac[SUBS_UNION_LEMM2]
   >> `!q. q ∈ e' ==> q ∈ e \/ (q = X (U f1 f2))` by metis_tac[IN_UNION, IN_SING]
   >> `!q. q ∈ e' ==> h' q ⊆ e1 ∪ {U f1 f2}` by
         (Cases_on `q ∈ e` >> metis_tac[SUBSET_UNION])
   >> `!q. q ∈ e' ==> h' q ⊆ r.V (l + 1)`
      by metis_tac[SUBSET_TRANS, runForAA_def, validAARunFor_def]
   >> fs[] >> fs[runForAA_def]
   >> `?r'. validAARunFor
        (ltl2vwaa_free_alph (POW (props f)) (CONJ f1 (X (U f1 f2)))) r' (suff w l)
       /\ ∀b x. infBranchOf r' b ∧ branchFixP b x
          ⇒ x ∉ (ltl2vwaa_free_alph (POW (props f)) (CONJ f1 (X (U f1 f2)))).final`
       suffices_by metis_tac[BRANCH_ACC_LEMM, LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM]
   >> `∀b x. infBranchOf r b ∧ branchFixP b x
       ⇒ x ∉ (ltl2vwaa_free_alph (POW (props f)) (U f1 f2)).final`
       by metis_tac[BRANCH_ACC_LEMM, LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM]
   >> `(let run_int =
         ALTERA_RUN (λi. if i = 0 then e' else r.V (i + l))
             (λ(i,q). if i = 0 then h' q else r.E (i + l,q))
        in
         validAARunFor (ltl2vwaa_free_alph (POW (props f)) (U f1 f2)) r w
                     ∧ (∀q. q ∈ e' ⇒ h' q ⊆ r.V  (l + 1)) ⇒
                     ∀i. (run_restr e' run_int).V (i + 1) ⊆ r.V (i + l + 1))`
        by metis_tac[REPL_RUN_CONSTR_LEMM]
   >> fs[]
   >> qabbrev_tac `r_int =
                   (ALTERA_RUN (λi. if i = 0 then e' else r.V (i + l))
                        (λ(i,q). if i = 0 then h' q else r.E (i + l,q)))`
   >> `∀i. (run_restr e' r_int).V (i + 1) ⊆ r.V (i + (l + 1))` by metis_tac[]
   >> qexists_tac `run_restr e' r_int` >> strip_tac
   >- (fs[validAARunFor_def, ltl2vwaa_free_alph_def, initForms_def, tempDNF_def]
     >> rpt strip_tac
     >- (fs[] >> qexists_tac `e` >> rpt strip_tac >> fs[]
         >> simp[run_restr_def, run_restr_V_def] >> fs[]
        )
     >- (Cases_on `i = 0`
         >> simp[SUBSET_DEF]
         >> simp[run_restr_def, run_restr_V_def, tempSubForms_def, UNION_DEF]
         >> rpt strip_tac
            >- (`x ∈ e \/ (x = (X (U f1 f2)))` by metis_tac[] >> fs[]
                >> `e ⊆ tempSubForms f1` by metis_tac[TEMPDNF_TEMPSUBF]
                >> metis_tac[SUBSET_DEF])
            >- (`?j. i = SUC j` by (Cases_on `i` >> fs[])
                >> `i = j + 1` by simp[]
                >> fs[run_restr_def]
                >> `x ∈ r.V (j + (l + 1))` by metis_tac[SUBSET_DEF]
                >> `x ∈ tempSubForms (U f1 f2)` by metis_tac[SUBSET_DEF]
                >> fs[tempSubForms_def, SUBSET_DEF, UNION_DEF]
               )
        )
     >- (Cases_on `i = 0` >> simp[run_restr_def, run_restr_E_def]
         >- (fs[run_restr_def, run_restr_V_def]
             >> Cases_on `q = X (U f1 f2)`
                >- (qexists_tac `POW (props f)` >> strip_tac
                   >- (simp[trans_def] >> qunabbrev_tac `r_int`
                       >> qunabbrev_tac `h'` >> fs[]
                       >> fs[tempDNF_def]
                      )
                   >- (`at w l ∈ POW (props f)` suffices_by fs[AT_SUFF_LEMM]
                        >> metis_tac[IN_INTER])
                   )
                >- (`q ∈ e` by metis_tac[]
                     >> `∃a''. a'' ∈ a' ∧ (a'',h q) ∈ trans (POW (props f)) q`
                        by metis_tac[]
                     >> qexists_tac `a''` >> strip_tac
                        >- (simp[trans_def] >> qunabbrev_tac `r_int`
                            >> qunabbrev_tac `h'` >> fs[])
                        >- (`at w l ∈ a''` suffices_by fs[AT_SUFF_LEMM]
                            >> metis_tac[IN_INTER, IN_BIGINTER])
                   )
            )
         >- (`?j. i = SUC j` by (Cases_on `i` >> fs[])
              >> `i = j + 1` by simp[]
              >> `q ∈ r.V (j + (l + 1))` by metis_tac[SUBSET_DEF]
              >> `∃a''. (a'',r.E ((j + (l + 1)) ,q)) ∈ trans (POW (props f)) q
                           ∧ at w (j + (l + 1)) ∈ a''`
                  by metis_tac[]
              >> qexists_tac `a''`
              >> `at w (i + l) ∈ a''` by metis_tac[ADD_COMM, ADD_ASSOC]
              >> fs[run_restr_def]
              >> qunabbrev_tac `r_int` >> simp[run_restr_V_def, trans_def]
              >> metis_tac[AT_SUFF_LEMM]
            )
        )
     >- (simp[run_restr_def, run_restr_E_def, run_restr_V_def]
         >> Cases_on `q ∈ run_restr_V e' r_int i` >> fs[EMPTY_SUBSET]
         >> Cases_on `i = 0`
            >- (simp[run_restr_V_def]
                >> qunabbrev_tac `r_int` >> simp[run_restr_V_def] >> fs[]
                >> `h' q ⊆
                       run_restr_V e'
                       (ALTERA_RUN (λi. if i = 0 then e' else r.V (i + l))
                            (λ(i,q). if i = 0 then h' q else r.E (i + l,q))) (SUC 0)`
                   suffices_by simp[]
                >> simp[run_restr_V_def] >> simp[SUBSET_DEF, BIGUNION]
                >> rpt strip_tac >> qexists_tac `h' q` >> fs[]
                >> qexists_tac `q` >> fs[]
                >> metis_tac[run_restr_V_def]
               )
            >- (`?j. i = SUC j` by (Cases_on `i` >> fs[])
                >> `i = j + 1` by simp[]
                >> fs[run_restr_def]
                >> `q ∈ r.V (j + (l + 1))` by metis_tac [SUBSET_DEF]
                >> qunabbrev_tac `r_int`
                >> simp[run_restr_V_def, run_restr_E_def] >> fs[]
                >> simp[SUBSET_DEF] >> rpt strip_tac
                >> `j + 2 = SUC (j + 1)` by simp[]
                >> `x ∈
                     run_restr_V e'
                     (ALTERA_RUN (λi. if i = 0 then e' else r.V (i + l))
                          (λ(i,q). if i = 0 then h' q else r.E (i + l,q))) (SUC (j + 1))`
                      suffices_by metis_tac[]
                >> fs[run_restr_V_def]
                >> qexists_tac `r.E (j+(l+1),q)` >> strip_tac >> fs[]
                >> qexists_tac `q` >> fs[]
               )
        )
     >- (Cases_on `i = 0` >> fs[]
         >> `?j. i = SUC j` by (Cases_on `i` >> fs[])
         >> `i = j + 1` by simp[]
         >> fs[run_restr_def]
         >> `j + 1 = SUC j` by simp[]
         >> `q ∈ run_restr_V e' r_int (SUC j)` by metis_tac[]
         >> fs[run_restr_V_def]
         >> qexists_tac `q'` >> fs[]
         >> fs[run_restr_E_def]
        ))
     >- (rpt strip_tac
         >> `!aut. (let run_int =
                         ALTERA_RUN (λi. if i = 0 then e' else r.V (i + l))
                             (λ(i,q). if i = 0 then h' q else r.E (i + l,q))
                    in
             validAARunFor aut r w ∧ (∀q. q ∈ e' ⇒ h' q ⊆ r.V (1 + l)) ∧
            infBranchOf (run_restr e' run_int) b ∧ branchFixP b x ⇒
                    ∃b'. infBranchOf r b' ∧ branchFixP b' x)`
            by metis_tac[REPL_RUN_CONSTR_LEMM2]
         >> fs[]
         >> `∃b'. infBranchOf r b' ∧ branchFixP b' x` by metis_tac[]
         >> fs[ltl2vwaa_free_alph_def, finalForms_def]
         >> `tempSubForms (CONJ f1 (X (U f1 f2)))
                     = {X (U f1 f2)} ∪ tempSubForms (U f1 f2)` by
                (fs[tempSubForms_def] >> metis_tac[UNION_DEF])
         >> `U f1' f2' ∈ {X (U f1 f2)} ∪ tempSubForms (U f1 f2)` by fs[]
         >> `~(X (U f1 f2) = U f1' f2')` by rw[]
         >> `U f1' f2' ∈ tempSubForms (U f1 f2)` by metis_tac[IN_UNION,IN_SING]
         >> metis_tac[]
        )
  );

val R_REPL_F1_LEMM = store_thm
  ("R_REPL_F1_LEMM",
  ``!a r f f1 f2 w l.(runForAA (ltl2vwaa_free_alph (POW (props f)) (R f1 f2)) r w
                   /\ (a,r.E (l,R f1 f2)) ∈
                      d_conj (trans (POW (props f)) f2) {(POW (props f), {R f1 f2})}
                   /\ at w l ∈ a)
     ==> ?r'.
          runForAA
          (ltl2vwaa_free_alph (POW (props f)) (CONJ f2 (X (R f1 f2))))
          r' (suff w l)``,
   rpt strip_tac >> fs[d_conj_def]
   >> `∃e t a'.
     (e1 = BIGUNION t) ∧ e ∈ tempDNF f2 ∧ (a1 = BIGINTER a') ∧
     (∀t'. t' ∈ t ⇒ ∃q a''. a'' ∈ a' ∧ q ∈ e ∧ (a'',t') ∈ trans (POW (props f)) q) ∧
     ∀q. q ∈ e ⇒ ∃t' a''. a'' ∈ a' ∧ t' ∈ t ∧ (a'',t') ∈ trans (POW (props f)) q`
     by fs[TRANS_TEMPDNF_LEMM]
   >> `∀q. ?t'.
       q ∈ e ⇒
       ∃a''. a'' ∈ a' ∧ t' ∈ t ∧ (a'',t') ∈ trans (POW (props f)) q`
      by metis_tac[]
   >> `?h. !q. q ∈ e ⇒
       ∃a''. a'' ∈ a' ∧ (h q) ∈ t ∧ (a'',(h q)) ∈ trans (POW (props f)) q`
       by metis_tac[SKOLEM_THM]
   >> `!q. q ∈ e ==> h q ∈ t` by metis_tac[]
   >> `!q. q ∈ e ==> h q ⊆ e1` by metis_tac[SUBSET_BIGUNION_I]
   >> qabbrev_tac `h' = (\q. if (q = X (R f1 f2)) then {R f1 f2} else h q)`
   >> qabbrev_tac `e' = e ∪ {X (R f1 f2)}`
   >> `!q. q ∈ e' ==> ((h' q = h q) \/ (h' q = {R f1 f2}))`
        by metis_tac[]
   >> `!q. q ∈ e' ==> h' q ⊆ (h q ∪ {R f1 f2})`
      by metis_tac[SUBS_UNION_LEMM]
   >> `!q. e ⊆ e'` by metis_tac[SUBSET_UNION]
   >> `!q. q ∈ e ==> h' q ⊆ h q ∪ {R f1 f2}`
        by metis_tac[SUBSET_DEF]
   >> `!q. q ∈ e ==> h' q ⊆ e1 ∪ {R f1 f2}` by metis_tac[SUBS_UNION_LEMM2]
   >> `!q. q ∈ e' ==> q ∈ e \/ (q = X (R f1 f2))` by metis_tac[IN_UNION, IN_SING]
   >> `!q. q ∈ e' ==> h' q ⊆ e1 ∪ {R f1 f2}` by
         (Cases_on `q ∈ e` >> metis_tac[SUBSET_UNION])
   >> `!q. q ∈ e' ==> h' q ⊆ r.V (l + 1)`
      by metis_tac[SUBSET_TRANS, runForAA_def, validAARunFor_def]
   >> fs[] >> fs[runForAA_def]
   >> `?r'. validAARunFor
        (ltl2vwaa_free_alph (POW (props f)) (CONJ f2 (X (R f1 f2)))) r' (suff w l)
       /\ ∀b x. infBranchOf r' b ∧ branchFixP b x
          ⇒ x ∉ (ltl2vwaa_free_alph (POW (props f)) (CONJ f2 (X (R f1 f2)))).final`
       suffices_by metis_tac[BRANCH_ACC_LEMM, LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM]
   >> `∀b x. infBranchOf r b ∧ branchFixP b x
       ⇒ x ∉ (ltl2vwaa_free_alph (POW (props f)) (R f1 f2)).final`
       by metis_tac[BRANCH_ACC_LEMM, LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM]
   >> `(let run_int =
         ALTERA_RUN (λi. if i = 0 then e' else r.V (i + l))
             (λ(i,q). if i = 0 then h' q else r.E (i + l,q))
        in
         validAARunFor (ltl2vwaa_free_alph (POW (props f)) (R f1 f2)) r w
                     ∧ (∀q. q ∈ e' ⇒ h' q ⊆ r.V  (l + 1)) ⇒
                     ∀i. (run_restr e' run_int).V (i + 1) ⊆ r.V (i + l + 1))`
        by metis_tac[REPL_RUN_CONSTR_LEMM]
   >> fs[]
   >> qabbrev_tac `r_int =
                   (ALTERA_RUN (λi. if i = 0 then e' else r.V (i + l))
                        (λ(i,q). if i = 0 then h' q else r.E (i + l,q)))`
   >> `∀i. (run_restr e' r_int).V (i + 1) ⊆ r.V (i + (l + 1))` by metis_tac[]
   >> qexists_tac `run_restr e' r_int` >> strip_tac
   >- (fs[validAARunFor_def, ltl2vwaa_free_alph_def, initForms_def, tempDNF_def]
     >> rpt strip_tac
     >- (fs[] >> qexists_tac `e` >> rpt strip_tac >> fs[]
         >> simp[run_restr_def, run_restr_V_def] >> fs[]
        )
     >- (Cases_on `i = 0`
         >> simp[SUBSET_DEF]
         >> simp[run_restr_def, run_restr_V_def, tempSubForms_def, UNION_DEF]
         >> rpt strip_tac
            >- (`x ∈ e \/ (x = (X (R f1 f2)))` by metis_tac[] >> fs[]
                >> `e ⊆ tempSubForms f2` by metis_tac[TEMPDNF_TEMPSUBF]
                >> metis_tac[SUBSET_DEF])
            >- (`?j. i = SUC j` by (Cases_on `i` >> fs[])
                >> `i = j + 1` by simp[]
                >> fs[run_restr_def]
                >> `x ∈ r.V (j + (l + 1))` by metis_tac[SUBSET_DEF]
                >> `x ∈ tempSubForms (R f1 f2)` by metis_tac[SUBSET_DEF]
                >> fs[tempSubForms_def, SUBSET_DEF, UNION_DEF]
               )
        )
     >- (Cases_on `i = 0` >> simp[run_restr_def, run_restr_E_def]
         >- (fs[run_restr_def, run_restr_V_def]
             >> Cases_on `q = X (R f1 f2)`
                >- (qexists_tac `POW (props f)` >> strip_tac
                   >- (simp[trans_def] >> qunabbrev_tac `r_int`
                       >> qunabbrev_tac `h'` >> fs[]
                       >> fs[tempDNF_def]
                      )
                   >- (`at w l ∈ POW (props f)` suffices_by fs[AT_SUFF_LEMM]
                        >> metis_tac[IN_INTER])
                   )
                >- (`q ∈ e` by metis_tac[]
                     >> `∃a''. a'' ∈ a' ∧ (a'',h q) ∈ trans (POW (props f)) q`
                        by metis_tac[]
                     >> qexists_tac `a''` >> strip_tac
                        >- (simp[trans_def] >> qunabbrev_tac `r_int`
                            >> qunabbrev_tac `h'` >> fs[])
                        >- (`at w l ∈ a''` suffices_by fs[AT_SUFF_LEMM]
                            >> metis_tac[IN_INTER, IN_BIGINTER])
                   )
            )
         >- (`?j. i = SUC j` by (Cases_on `i` >> fs[])
              >> `i = j + 1` by simp[]
              >> `q ∈ r.V (j + (l + 1))` by metis_tac[SUBSET_DEF]
              >> `∃a''. (a'',r.E ((j + (l + 1)) ,q)) ∈ trans (POW (props f)) q
                           ∧ at w (j + (l + 1)) ∈ a''`
                  by metis_tac[]
              >> qexists_tac `a''`
              >> `at w (i + l) ∈ a''` by metis_tac[ADD_COMM, ADD_ASSOC]
              >> fs[run_restr_def]
              >> qunabbrev_tac `r_int` >> simp[run_restr_V_def, trans_def]
              >> metis_tac[AT_SUFF_LEMM]
            )
        )
     >- (simp[run_restr_def, run_restr_E_def, run_restr_V_def]
         >> Cases_on `q ∈ run_restr_V e' r_int i` >> fs[EMPTY_SUBSET]
         >> Cases_on `i = 0`
            >- (simp[run_restr_V_def]
                >> qunabbrev_tac `r_int` >> simp[run_restr_V_def] >> fs[]
                >> `h' q ⊆
                       run_restr_V e'
                       (ALTERA_RUN (λi. if i = 0 then e' else r.V (i + l))
                            (λ(i,q). if i = 0 then h' q else r.E (i + l,q))) (SUC 0)`
                   suffices_by simp[]
                >> simp[run_restr_V_def] >> simp[SUBSET_DEF, BIGUNION]
                >> rpt strip_tac >> qexists_tac `h' q` >> fs[]
                >> qexists_tac `q` >> fs[]
                >> metis_tac[run_restr_V_def]
               )
            >- (`?j. i = SUC j` by (Cases_on `i` >> fs[])
                >> `i = j + 1` by simp[]
                >> fs[run_restr_def]
                >> `q ∈ r.V (j + (l + 1))` by metis_tac [SUBSET_DEF]
                >> qunabbrev_tac `r_int`
                >> simp[run_restr_V_def, run_restr_E_def] >> fs[]
                >> simp[SUBSET_DEF] >> rpt strip_tac
                >> `j + 2 = SUC (j + 1)` by simp[]
                >> `x ∈
                     run_restr_V e'
                     (ALTERA_RUN (λi. if i = 0 then e' else r.V (i + l))
                          (λ(i,q). if i = 0 then h' q else r.E (i + l,q))) (SUC (j + 1))`
                      suffices_by metis_tac[]
                >> fs[run_restr_V_def]
                >> qexists_tac `r.E (j+(l+1),q)` >> strip_tac >> fs[]
                >> qexists_tac `q` >> fs[]
               )
        )
     >- (Cases_on `i = 0` >> fs[]
         >> `?j. i = SUC j` by (Cases_on `i` >> fs[])
         >> `i = j + 1` by simp[]
         >> fs[run_restr_def]
         >> `j + 1 = SUC j` by simp[]
         >> `q ∈ run_restr_V e' r_int (SUC j)` by metis_tac[]
         >> fs[run_restr_V_def]
         >> qexists_tac `q'` >> fs[]
         >> fs[run_restr_E_def]
        ))
     >- (rpt strip_tac
         >> `!aut. (let run_int =
                         ALTERA_RUN (λi. if i = 0 then e' else r.V (i + l))
                             (λ(i,q). if i = 0 then h' q else r.E (i + l,q))
                    in
             validAARunFor aut r w ∧ (∀q. q ∈ e' ⇒ h' q ⊆ r.V (1 + l)) ∧
            infBranchOf (run_restr e' run_int) b ∧ branchFixP b x ⇒
                    ∃b'. infBranchOf r b' ∧ branchFixP b' x)`
            by metis_tac[REPL_RUN_CONSTR_LEMM2]
         >> fs[]
         >> `∃b'. infBranchOf r b' ∧ branchFixP b' x` by metis_tac[]
         >> fs[ltl2vwaa_free_alph_def, finalForms_def]
         >> `tempSubForms (CONJ f2 (X (R f1 f2)))
                     = {X (R f1 f2)} ∪ tempSubForms (R f1 f2)` by
                (fs[tempSubForms_def] >> metis_tac[UNION_DEF])
         >> `U f1' f2' ∈ {X (R f1 f2)} ∪ tempSubForms (R f1 f2)` by fs[]
         >> `~(X (R f1 f2) = U f1' f2')` by rw[]
         >> `U f1' f2' ∈ tempSubForms (R f1 f2)` by metis_tac[IN_UNION,IN_SING]
         >> metis_tac[]
        )
  );

val RUN_FOR_DISJ_LEMM = store_thm
  ("RUN_FOR_DISJ_LEMM",
  ``!f1 f2 f w run.
       (runForAA (ltl2vwaa_free_alph (POW (props f)) f1) run w
     \/ runForAA (ltl2vwaa_free_alph (POW (props f)) f2) run w
       )
           ==> runForAA (ltl2vwaa_free_alph (POW (props f)) (DISJ f1 f2)) run w``,
  fs[runForAA_def] >> rpt strip_tac
    >- (fs[ltl2vwaa_free_alph_def, initForms_def, tempSubForms_def, finalForms_def]
        >> fs[tempDNF_def, tempSubForms_def, SUBSET_DEF, UNION_DEF] >> rpt strip_tac
        >> fs[validAARunFor_def,SUBSET_DEF] >> rpt strip_tac
        >> metis_tac[])
    >- (`!b x. infBranchOf run b ∧ branchFixP b x ⇒
           x ∉ (ltl2vwaa_free_alph (POW (props f)) f1).final`
         by metis_tac[BRANCH_ACC_LEMM, LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM]
         >> `validAARunFor (ltl2vwaa_free_alph (POW (props f)) (DISJ f1 f2)) run w
           /\ (∀b x. (infBranchOf run b ∧ branchFixP b x)
                ==> (x ∉ (ltl2vwaa_free_alph (POW (props f)) (DISJ f1 f2)).final))`
         suffices_by metis_tac[BRANCH_ACC_LEMM, LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM]
         >> rpt strip_tac
            >- (fs[validAARunFor_def] >> rpt strip_tac
                >> fs[SUBSET_DEF, ltl2vwaa_free_alph_def, initForms_def, tempDNF_def]
                >> rpt strip_tac >> fs[tempSubForms_def] >> metis_tac[]
               )
            >- (fs[ltl2vwaa_free_alph_def, finalForms_def]
                >> `∀f1' f2'. x ≠ U f1' f2' ∨ U f1' f2' ∉ tempSubForms f1` by metis_tac[]
                >> `x ≠ U f1' f2' ∨ U f1' f2' ∉ tempSubForms f1` by metis_tac[]
                >> `∀i. b i ∈ run.V i` by metis_tac[BRANCH_V_LEMM]
                >> fs[validAARunFor_def, branchFixP_def]
                >> `b i ∈ tempSubForms f1` by metis_tac[SUBSET_DEF]
                >> metis_tac[]
               )
       )
    >- (fs[ltl2vwaa_free_alph_def, initForms_def, tempSubForms_def, finalForms_def]
          >> fs[tempDNF_def, tempSubForms_def, SUBSET_DEF, UNION_DEF] >> rpt strip_tac
          >> fs[validAARunFor_def,SUBSET_DEF] >> rpt strip_tac
          >> metis_tac[])
    >- (`!b x. infBranchOf run b ∧ branchFixP b x ⇒
           x ∉ (ltl2vwaa_free_alph (POW (props f)) f2).final`
         by metis_tac[BRANCH_ACC_LEMM, LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM]
         >> `validAARunFor (ltl2vwaa_free_alph (POW (props f)) (DISJ f1 f2)) run w
           /\ (∀b x. (infBranchOf run b ∧ branchFixP b x)
                ==> (x ∉ (ltl2vwaa_free_alph (POW (props f)) (DISJ f1 f2)).final))`
         suffices_by metis_tac[BRANCH_ACC_LEMM, LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM]
         >> rpt strip_tac
            >- (fs[validAARunFor_def] >> rpt strip_tac
                >> fs[SUBSET_DEF, ltl2vwaa_free_alph_def, initForms_def, tempDNF_def]
                >> rpt strip_tac >> fs[tempSubForms_def] >> metis_tac[]
               )
            >- (fs[ltl2vwaa_free_alph_def, finalForms_def]
                >> `∀f1' f2'. x ≠ U f1' f2' ∨ U f1' f2' ∉ tempSubForms f2` by metis_tac[]
                >> `x ≠ U f1' f2' ∨ U f1' f2' ∉ tempSubForms f2` by metis_tac[]
                >> `∀i. b i ∈ run.V i` by metis_tac[BRANCH_V_LEMM]
                >> fs[validAARunFor_def, branchFixP_def]
                >> `b i ∈ tempSubForms f2` by metis_tac[SUBSET_DEF]
                >> metis_tac[]
               )
       )
  );

val RUN_FOR_DISJ_LEMM2 = store_thm
  ("RUN_FOR_DISJ_LEMM2",
  ``!f f1 f2 run w.
        runForAA (ltl2vwaa_free_alph (POW (props f)) (DISJ f1 f2)) run w
           ==> (runForAA (ltl2vwaa_free_alph (POW (props f)) f1) run w
            \/  runForAA (ltl2vwaa_free_alph (POW (props f)) f2) run w
               )``,
  rpt strip_tac >> fs[runForAA_def]
  >> `∀b x. infBranchOf run b ∧ branchFixP b x
        ⇒ x ∉ (ltl2vwaa_free_alph (POW (props f)) (DISJ f1 f2)).final`
      by metis_tac[LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM, BRANCH_ACC_LEMM]
  >> asm_simp_tac(srw_ss() ++ SatisfySimps.SATISFY_ss ++ boolSimps.CONJ_ss)
       [BRANCH_ACC_LEMM,LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM]
  >> fs[ltl2vwaa_free_alph_def,validAARunFor_def]
  >> rpt strip_tac >> fs[initForms_def, tempDNF_def, tempSubForms_def, finalForms_def]
    >- (`(∀i. run.V i ⊆ tempSubForms f1) ∧
           (∀b x.
            infBranchOf run b ∧ branchFixP b x ⇒
            ∀f1' f2'. x ≠ U f1' f2' ∨ U f1' f2' ∉ tempSubForms f1) `
         suffices_by metis_tac[]
     >> conj_tac
        >- (Induct_on `i` >> fs[tempSubForms_def, tempDNF_def,TEMPDNF_TEMPSUBF]
            >> fs[SUBSET_DEF] >> rpt strip_tac
            >> `(SUC i = 0) ∨ ∃q'. x ∈ run.E ((SUC i) − 1,q') ∧ q' ∈ run.V ((SUC i) − 1)`
               by metis_tac[] >> fs[]
            >> `∃a. (a,run.E (i,q')) ∈ trans (POW (props f)) q'`
               by metis_tac[]
            >> `(x,q') ∈ TSF` by metis_tac[TRANS_REACHES_SUBFORMS]
            >> `(q',f1) ∈ TSF` by metis_tac[TSF_def, IN_DEF]
            >> metis_tac[TSF_TRANS_LEMM, transitive_def, TSF_def, IN_DEF]
           )
        >- metis_tac[]
       )
    >- (`(∀i. run.V i ⊆ tempSubForms f2) ∧
            (∀b x.
              infBranchOf run b ∧ branchFixP b x ⇒
                 ∀f1' f2'. x ≠ U f1' f2' ∨ U f1' f2' ∉ tempSubForms f2) `
         suffices_by metis_tac[]
        >> conj_tac
           >- (Induct_on `i` >> fs[tempSubForms_def, tempDNF_def,TEMPDNF_TEMPSUBF]
               >> fs[SUBSET_DEF] >> rpt strip_tac
               >> `(SUC i = 0) ∨ ∃q'. x ∈ run.E ((SUC i) − 1,q') ∧ q' ∈ run.V ((SUC i) − 1)`
                   by metis_tac[] >> fs[]
               >> `∃a. (a,run.E (i,q')) ∈ trans (POW (props f)) q'`
                   by metis_tac[]
               >> `(x,q') ∈ TSF` by metis_tac[TRANS_REACHES_SUBFORMS]
               >> `(q',f2) ∈ TSF` by metis_tac[TSF_def, IN_DEF]
               >> metis_tac[TSF_TRANS_LEMM, transitive_def, TSF_def, IN_DEF]
              )
           >- metis_tac[]
       )
  );

val REPL_IN_0 = store_thm
  ("REPL_IN_0",
   ``!r w f f' f1 f2 a p.
       runForAA (ltl2vwaa_free_alph (POW (props f')) f) r w
       /\ (a, r.V 1) ∈ trans (POW (props f')) (p)
       /\ at w 0 ∈ a
       /\ {p} ∈ tempDNF p
     ==>
       ?r'. runForAA (ltl2vwaa_free_alph (POW (props f')) (p)) r' w``,
   rpt strip_tac >> fs[runForAA_def]
   >> `?r'. validAARunFor (ltl2vwaa_free_alph (POW (props f')) (p)) r' w
      /\ (∀b x. infBranchOf r' b ∧ branchFixP b x
        ⇒ x ∉ (ltl2vwaa_free_alph (POW (props f')) (p)).final)`
       suffices_by metis_tac[BRANCH_ACC_LEMM,  LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM]
   >> `(∀b x. infBranchOf r b ∧ branchFixP b x
         ⇒ x ∉ (ltl2vwaa_free_alph (POW (props f')) f).final)`
        by metis_tac[BRANCH_ACC_LEMM,  LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM]
   >> SUBGOAL_THEN ``!n. r.V (n + 1) ⊆ tempSubForms (p)`` mp_tac
     >- (Induct_on `n`
          >- (`!q. q ∈ r.V 1 ==> (q,p) ∈ TSF` by metis_tac[TRANS_REACHES_SUBFORMS]
              >> fs[SUBSET_DEF] >> rpt strip_tac
              >> metis_tac[TSF_def, IN_DEF]
             )
          >- (fs[SUBSET_DEF] >> rpt strip_tac
              >> `(((SUC n) + 1) = 0)
                \/ ∃q'. x ∈ r.E (((SUC n) + 1) − 1,q') ∧ q' ∈ r.V (((SUC n) + 1) − 1)`
                  by metis_tac[validAARunFor_def]
              >> fs[validAARunFor_def, ltl2vwaa_free_alph_def]
              >> `∃a'. (a',r.E(SUC n, q')) ∈ trans (POW (props f')) q'` by metis_tac[]
              >> `(x, q') ∈ TSF` by metis_tac[TRANS_REACHES_SUBFORMS]
              >> `q' ∈ tempSubForms (p)` by metis_tac[SUC_ONE_ADD, ADD_COMM]
              >> metis_tac[TSF_def, IN_DEF, TSF_TRANS_LEMM, transitive_def]
             )
        )
   >- (rpt strip_tac
        >> qexists_tac `ALTERA_RUN (\i. if i = 0 then {p} else r.V i)
                          (λ(i,q). if i = 0 then r.V 1 else r.E (i,q))`
        >> `!b. infBranchSuffOf r 1 b ⇒
               ∃b'. infBranchOf r b' ∧ ∀j. b j = b' (j + 1)`
           by metis_tac[BRANCH_SUFF_LEMM]
        >> `!b. infBranchOf r b ⇒ ∀i. b i ∈ r.V i` by metis_tac[BRANCH_V_LEMM]
        >> fs[validAARunFor_def] >> rpt strip_tac
           >- (fs[ltl2vwaa_free_alph_def, initForms_def, tempDNF_def])
           >- (Cases_on `i = 0` >> fs[tempSubForms_def, ltl2vwaa_free_alph_def]
                 >- (`{p} ⊆ tempSubForms p` by metis_tac[TEMPDNF_TEMPSUBF]
                     >> fs[SUBSET_DEF]
                    )
                 >- (`?j. i = SUC j` by (Cases_on `i` >> fs[])
                    >> `i = j + 1` by simp[]
                    >> metis_tac[]
                    )
              )
           >- (Cases_on `i = 0` >> fs[tempSubForms_def, ltl2vwaa_free_alph_def]
                >> qexists_tac `a` >> fs[])
           >- (Cases_on `i = 0` >> fs[])
           >- (Cases_on `i = 0` >> fs[]
               >> `?j. i = SUC j` by (Cases_on `i` >> fs[])
               >> `i = j + 1` by simp[]
               >> Cases_on `j = 0` >> fs[]
               >> `((j + 1) = 0) ∨ ∃q'. q ∈ r.E ((j + 1) − 1,q') ∧ q' ∈ r.V ((j + 1) − 1)`
                   by metis_tac[] >> fs[]
               >> qexists_tac `q'` >> fs[]
              )
           >- (fs[ltl2vwaa_free_alph_def, finalForms_def]
               >> `infBranchSuffOf r 1 (\i. b (i + 1))` by
                   (simp[infBranchSuffOf_def] >> fs[] >> rpt strip_tac
                      >- (fs[infBranchOf_def] >> fs[]
                          >> `0 + 1 = 1` by simp[]
                          >> `b (0 + 1) ∈ r.V 1` by metis_tac[]
                          >> fs[])
                      >- (fs[infBranchOf_def] >> rename [‘b (i + 2) ∈ r.E _’]
                          >> `b (i + 1 + 1) ∈ r.E(i+1, b (i+1))` suffices_by simp[]
                          >> `~(i + 1 = 0)` by simp[] >> metis_tac[]
                          )
                   )
               >> qabbrev_tac `b' = (\i. b (i+1))`
               >> `∃b''. infBranchOf r b'' ∧ ∀j. b' j = b'' (j + 1)`
                   by metis_tac[]
               >> `branchFixP b'' x` by
                      (fs[branchFixP_def] >> rpt strip_tac
                       >> qexists_tac `i + 1`
                       >> qunabbrev_tac `b'`
                       >> rpt strip_tac >> fs[]
                         >- (`i + 1 >= i` by simp[]
                             >> `b (i+1) = b'' (i + 1)` by metis_tac[]
                             >> metis_tac[])
                         >- (`m >= i` by simp[]
                              >> `b m = x` by simp[]
                              >> `m >= 1` by simp[]
                              >> `~ (m = 0)` by simp[]
                              >> `?k. m = SUC k` by (Cases_on `m` >> fs[])
                              >> `b (k + 1) = b'' (k + 1)` by metis_tac[]
                              >> `SUC k = k + 1` by simp[]
                              >> `b (SUC k) = x` by metis_tac[]
                              >> `b (k + 1) = b'' (k + 1)` by metis_tac[]
                              >> metis_tac[SUC_ONE_ADD,ADD_COMM]
                            )
                      )
               >> `x ≠ U f1' f2' ∨ U f1' f2' ∉ tempSubForms f`
                  by metis_tac[]
               >> `∀i. b'' i ∈ r.V i` by metis_tac[]
               >> `!i. b'' i ∈ tempSubForms f` by metis_tac[SUBSET_DEF]
               >> fs[branchFixP_def]
               >> metis_tac[]
              )
      )
  );

val RUN_FOR_CONJ_LEMM = store_thm
  ("RUN_FOR_DISJ_LEMM",
   ``!f1 f2 f w.
     (?r. runForAA (ltl2vwaa_free_alph (POW (props f)) f1) r w)
  /\ (?r. runForAA (ltl2vwaa_free_alph (POW (props f)) f2) r w)
      ==> (?r. runForAA (ltl2vwaa_free_alph (POW (props f)) (CONJ f1 f2)) r w)``,
   fs[runForAA_def] >> rpt gen_tac >> strip_tac
   >> `?r. validAARunFor (ltl2vwaa_free_alph (POW (props f)) (CONJ f1 f2)) r w
    /\ (∀b x. infBranchOf r b ∧ branchFixP b x
         ⇒ x ∉ (ltl2vwaa_free_alph (POW (props f)) (CONJ f1 f2)).final)`
      suffices_by metis_tac[LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM, BRANCH_ACC_LEMM]
   >> qexists_tac `conj_run r r'`
   >> conj_tac
     >- (`!i. conj_run_V r r' i ⊆ (r.V i ∪ r'.V i)` by metis_tac[CONJ_RUN_V_LEMM]
         >> fs[validAARunFor_def] >> rpt strip_tac
         >> fs[ltl2vwaa_free_alph_def, initForms_def, finalForms_def, tempSubForms_def]
         >> fs[tempDNF_def, conj_run_def, conj_run_V_def, conj_run_E_def]
           >- (qexists_tac `r.V 0` >> qexists_tac `r'.V 0` >> fs[])
           >- (`conj_run_V r r' i ⊆ r.V i ∪ r'.V i` by metis_tac[]
               >> `r.V i ⊆ (tempSubForms f1 ∪ tempSubForms f2)`
                   by metis_tac[SUBSET_UNION, SUBSET_TRANS]
               >> `r'.V i ⊆ (tempSubForms f1 ∪ tempSubForms f2)`
                   by metis_tac[SUBSET_UNION, SUBSET_TRANS]
               >> `r.V i ∪ r'.V i ⊆ (tempSubForms f1 ∪ tempSubForms f2)`
                  by metis_tac[UNION_SUBSET]
               >> metis_tac[SUBSET_TRANS]
              )
           >- (Cases_on `q ∈ r.V i`
                >- (metis_tac[conj_run_branch_cond_def])
                >- (Cases_on `q ∈ r'.V i`
                    >- (metis_tac[conj_run_branch_cond_def])
                    >- (`conj_run_V r r' i ⊆ r.V i ∪ r'.V i`
                          by metis_tac[] >> fs[SUBSET_DEF]
                        >> metis_tac[]
                       )
                   )
              )
         >- (fs[SUBSET_DEF, conj_run_V_def] >> rpt strip_tac
             >> `i + 1 = SUC i` by simp[]
             >> `x ∈ conj_run_V r r' (SUC i)` suffices_by metis_tac[]
             >> fs[conj_run_V_def, conj_run_branch_cond_def]
             >> Cases_on `q ∈ conj_run_V r r' i` >> fs[]
             >> Cases_on `q ∈ r.V i`
                >- (qexists_tac `r.E (i,q)` >> fs[]
                    >> qexists_tac `q` >> fs[conj_run_E_def])
                >- (Cases_on `q ∈ r'.V i`
                    >- (qexists_tac `r'.E (i,q)` >> fs[]
                        >> qexists_tac `q` >> fs[conj_run_E_def])
                    >- (metis_tac[NOT_IN_EMPTY])
                   )
            )
         >- (Cases_on `i=0` >> fs[]
             >> `?j. i = SUC j` by (Cases_on `i` >> fs[])
             >> rw[]
             >> fs[conj_run_V_def]
             >> qexists_tac `q'` >> rpt strip_tac >> fs[]
            )
        )
     >- (CCONTR_TAC
         >> fs[]
         >> `∀b x. infBranchOf r b ∧ branchFixP b x
               ⇒ x ∉ (ltl2vwaa_free_alph (POW (props f)) f1).final`
             by metis_tac[LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM, BRANCH_ACC_LEMM]
         >> `∀b x. infBranchOf r' b ∧ branchFixP b x
               ⇒ x ∉ (ltl2vwaa_free_alph (POW (props f)) f2).final`
             by metis_tac[LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM, BRANCH_ACC_LEMM]
         >> `∃b'. (infBranchOf r b' ∨ infBranchOf r' b') ∧ branchFixP b' x`
            by metis_tac[CONJ_RUN_FIXP_LEMM]
           >- (fs[ltl2vwaa_free_alph_def, finalForms_def,acceptingAARun_def, tempSubForms_def]
                 >- (`∀f1' f2'. x ≠ U f1' f2' ∨ U f1' f2' ∉ tempSubForms f1` by metis_tac[]
                      >> metis_tac[])
                 >- (`∀f1' f2'. x ≠ U f1' f2' ∨ U f1' f2' ∉ tempSubForms f1` by metis_tac[]
                      >> `U f1' f2' ∉ tempSubForms f1` by metis_tac[]
                      >> `!i. b' i ∈ r.V i` by metis_tac[BRANCH_V_LEMM]
                      >> `(∀i. r.V i ⊆ (ALTER_A (tempSubForms f1) (POW (props f))
                                                (trans (POW (props f))) (initForms f1)
                                                {U f1' f2 | U f1' f2 ∈ tempSubForms f1}
                                       ).states)`
                          by metis_tac[validAARunFor_def]
                      >> fs[SUBSET_DEF, branchFixP_def] >> metis_tac[]
                    )
              )
           >- (fs[ltl2vwaa_free_alph_def, finalForms_def,acceptingAARun_def, tempSubForms_def]
                 >- (`∀f1' f2'. x ≠ U f1' f2' ∨ U f1' f2' ∉ tempSubForms f2` by metis_tac[]
                     >> `U f1' f2' ∉ tempSubForms f2` by metis_tac[]
                     >> `!i. b' i ∈ r'.V i` by metis_tac[BRANCH_V_LEMM]
                     >> `(∀i. r'.V i ⊆ (ALTER_A (tempSubForms f2) (POW (props f))
                                                (trans (POW (props f)))
                                                (initForms f2)
                                                {U f1 f2' | U f1 f2' ∈ tempSubForms f2}
                                                ).states)`
                         by metis_tac[validAARunFor_def]
                     >> fs[SUBSET_DEF, branchFixP_def] >> metis_tac[]
                    )
                 >- (`∀f1 f2'. x ≠ U f1 f2' ∨ U f1 f2' ∉ tempSubForms f2` by metis_tac[]
                      >> metis_tac[])
              )
        )
  );

val RUN_FOR_CONJ_LEMM2_UNION = store_thm
  ("RUN_FOR_CONJ_LEMM2_UNION",
   ``!f1 f2 f w run.
              runForAA (ltl2vwaa_free_alph (POW (props f)) (CONJ f1 f2)) run w
            ==> (?r1. runForAA (ltl2vwaa_free_alph (POW (props f)) f1) r1 w
             /\ (?r2. runForAA (ltl2vwaa_free_alph (POW (props f)) f2) r2 w
             /\ !i. run.V i = r1.V i ∪ r2.V i))``,
   fs[runForAA_def] >> rpt gen_tac >> rpt strip_tac
   >> `(!b x. infBranchOf run b ∧ branchFixP b x
           ⇒ x ∉ (ltl2vwaa_free_alph (POW (props f)) (CONJ f1 f2)).final)`
      by metis_tac[LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM, BRANCH_ACC_LEMM]
   >> `!init. init ⊆ run.V 0 ==> !i. run_restr_V init run i ⊆ run.V i`
      by metis_tac[RUN_RESTR_LEMM]
   >> `!init b. (init ⊆ run.V 0) /\ (infBranchOf (run_restr init run) b)
              ==> infBranchOf run b`
      by metis_tac[RUN_RESTR_FIXP_LEMM]
     >- (`?r1. validAARunFor (ltl2vwaa_free_alph (POW (props f)) f1) r1 w
             /\ (∀b x. infBranchOf r1 b ∧ branchFixP b x
                  ⇒ x ∉ (ltl2vwaa_free_alph (POW (props f)) f1).final) /\
          ∃r2.
             (validAARunFor (ltl2vwaa_free_alph (POW (props f)) f2) r2 w ∧
              (∀b x. infBranchOf r2 b ∧ branchFixP b x
                ⇒ x ∉ (ltl2vwaa_free_alph (POW (props f)) f2).final)) ∧
                ∀i. run.V i = r1.V i ∪ r2.V i`
            suffices_by metis_tac[LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM, BRANCH_ACC_LEMM]
         >> rpt strip_tac >> fs[validAARunFor_def, ltl2vwaa_free_alph_def, finalForms_def]
         >> rpt strip_tac >> fs[initForms_def, tempSubForms_def, tempDNF_def]
         >> qexists_tac `run_restr f' run`
         >> rpt strip_tac >> fs[run_restr_def, run_restr_V_def]
           >- (Induct_on `i`
               >- metis_tac[run_restr_V_def, TEMPDNF_TEMPSUBF]
               >- (`∀i. run_restr_V f' run i ⊆ run.V i` by metis_tac[SUBSET_UNION]
                   >> simp[run_restr_V_def, SUBSET_DEF] >> rpt strip_tac
                   >> `(s = run.E (i,q)) ∧ q ∈ run_restr_V f' run i` by metis_tac[]
                   >> `q ∈ run.V i` by metis_tac[SUBSET_DEF]
                   >> `∃a. (a,run.E (i,q)) ∈ trans (POW (props f)) q` by metis_tac[]
                   >> `∀q'. (q' ∈ run.E (i,q)) ⇒ (q',q) ∈ TSF`
                       by metis_tac[TRANS_REACHES_SUBFORMS]
                   >> `(x,q) ∈ TSF` by metis_tac[]
                   >> `(q,f1) ∈ TSF` by metis_tac[TSF_def,IN_DEF,SUBSET_DEF]
                   >> metis_tac[TSF_TRANS_LEMM, transitive_def, TSF_def, IN_DEF]
                  )
              )
           >- (`∀i. run_restr_V f' run i ⊆ run.V i` by metis_tac[SUBSET_UNION]
               >> `q ∈ run.V i` by metis_tac[SUBSET_DEF]
               >> fs[run_restr_E_def]
              )
           >- (fs[SUBSET_DEF, run_restr_V_def, run_restr_E_def] >> rpt strip_tac
               >> Cases_on `q ∈ run_restr_V f' run i` >> fs[]
               >> `x ∈ run_restr_V f' run (SUC i)` suffices_by simp[SUC_ONE_ADD]
               >> fs[run_restr_V_def]
               >> qexists_tac `run.E (i,q)` >> rpt strip_tac >> fs[]
               >> qexists_tac `q` >> fs[]
              )
           >- (`run_restr_V f' run i ⊆ run.V i` by metis_tac[SUBSET_UNION]
               >> `q ∈ run.V i` by metis_tac[SUBSET_DEF]
               >> Cases_on `i=0` >> fs[]
               >> `(i = 0) ∨ ∃q'. q ∈ run.E (i − 1,q') ∧ q' ∈ run.V (i − 1)`
                  by metis_tac[] >> fs[]
               >> `?j. i = SUC j` by (Cases_on `i` >> fs[])
               >> rw[] >> fs[run_restr_V_def]
               >> qexists_tac `q''` >> strip_tac >> fs[]
               >> simp[run_restr_E_def]
              )
           >- (`infBranchOf run b` by metis_tac[SUBSET_UNION]
               >> metis_tac[]
              )
           >- (qexists_tac `run_restr f'' run`
               >> rpt strip_tac >> fs[run_restr_def, run_restr_V_def]
             >- (Induct_on `i`
                 >- metis_tac[run_restr_V_def, TEMPDNF_TEMPSUBF]
                 >- (`∀i. run_restr_V f'' run i ⊆ run.V i` by metis_tac[SUBSET_UNION]
                     >> simp[run_restr_V_def, SUBSET_DEF] >> rpt strip_tac
                     >> `(s = run.E (i,q)) ∧ q ∈ run_restr_V f'' run i` by metis_tac[]
                     >> `q ∈ run.V i` by metis_tac[SUBSET_DEF]
                     >> `∃a. (a,run.E (i,q)) ∈ trans (POW (props f)) q` by metis_tac[]
                     >> `∀q'. (q' ∈ run.E (i,q)) ⇒ (q',q) ∈ TSF`
                          by metis_tac[TRANS_REACHES_SUBFORMS]
                     >> `(x,q) ∈ TSF` by metis_tac[]
                     >> `(q,f2) ∈ TSF` by metis_tac[TSF_def,IN_DEF,SUBSET_DEF]
                     >> metis_tac[TSF_TRANS_LEMM, transitive_def, TSF_def, IN_DEF]
                    )
                )
             >- (`∀i. run_restr_V f'' run i ⊆ run.V i` by metis_tac[SUBSET_UNION]
                   >> `q ∈ run.V i` by metis_tac[SUBSET_DEF]
                   >> fs[run_restr_E_def]
                )
             >- (fs[SUBSET_DEF, run_restr_V_def, run_restr_E_def] >> rpt strip_tac
                 >> Cases_on `q ∈ run_restr_V f'' run i` >> fs[]
                 >> `x ∈ run_restr_V f'' run (SUC i)` suffices_by simp[SUC_ONE_ADD]
                 >> fs[run_restr_V_def]
                 >> qexists_tac `run.E (i,q)` >> rpt strip_tac >> fs[]
                 >> qexists_tac `q` >> fs[]
                )
             >- (`run_restr_V f'' run i ⊆ run.V i` by metis_tac[SUBSET_UNION]
                 >> `q ∈ run.V i` by metis_tac[SUBSET_DEF]
                 >> Cases_on `i=0` >> fs[]
                 >> `(i = 0) ∨ ∃q'. q ∈ run.E (i − 1,q') ∧ q' ∈ run.V (i − 1)`
                     by metis_tac[] >> fs[]
                 >> `?j. i = SUC j` by (Cases_on `i` >> fs[])
                 >> rw[] >> fs[run_restr_V_def]
                 >> qexists_tac `q''` >> strip_tac >> fs[]
                 >> simp[run_restr_E_def]
                )
             >- (`infBranchOf run b` by metis_tac[SUBSET_UNION]
                 >> metis_tac[]
                )
             >- (Induct_on `i`
                 >> fs[run_restr_V_def]
                 >> fs[SET_EQ_SUBSET] >> rpt strip_tac
                   >- (simp[SUBSET_DEF] >> rpt strip_tac
                       >> `((SUC i) = 0) ∨ ∃q'. x ∈ run.E ((SUC i) − 1,q')
                           ∧ q' ∈ run.V ((SUC i) − 1)` by metis_tac[]
                       >> fs[]
                       >> `q' ∈ run_restr_V f' run i \/ q' ∈ run_restr_V f'' run i`
                          by fs[UNION_DEF, SUBSET_DEF]
                        >- (`(∃s.
                              x ∈ s ∧
                               ∃q.
                                ((∀x. x ∈ s ⇒ x ∈ run.E (i,q))
                                     ∧ ∀x. x ∈ run.E (i,q) ⇒ x ∈ s) ∧
                                 q ∈ run_restr_V f' run i)`
                            suffices_by metis_tac[]
                            >> qexists_tac `run.E (i,q')` >> fs[]
                            >> qexists_tac `q'` >> fs[])
                        >- (`∃s.
                              x ∈ s ∧
                              ∃q.
                              ((∀x. x ∈ s ⇒ x ∈ run.E (i,q))
                                   ∧ ∀x. x ∈ run.E (i,q) ⇒ x ∈ s) ∧
                              q ∈ run_restr_V f'' run i`
                            suffices_by metis_tac[]
                            >> qexists_tac `run.E (i,q')` >> fs[]
                            >> qexists_tac `q'` >> fs[]
                           )
                      )
                   >- (simp[BIGUNION, SUBSET_DEF] >> rpt strip_tac
                        >> (`x ∈ run.V (i + 1)` by metis_tac[SUBSET_DEF]
                            >> metis_tac[SUC_ONE_ADD,ADD_COMM]
                      ))
                   >- (simp[BIGUNION, SUBSET_DEF] >> rpt strip_tac
                       >> `x ∈ run.V (i + 1)` by metis_tac[SUBSET_DEF]
                       >> metis_tac[SUC_ONE_ADD,ADD_COMM])
                )
              )
           )
  );

val TRANS_LEMM1 = store_thm
  ("TRANS_LEMM1",
   ``!w f' f r. runForAA (ltl2vwaa_free_alph (POW (props f')) f) r w
              /\ r.V 0 ∈ tempDNF f
                    ==> (?a. (a, r.V 1) ∈ trans (POW (props f')) f
                      /\ at w 0 ∈ a)``,
   gen_tac >> gen_tac >> Induct_on `f`
     >- (fs[ltl2vwaa_free_alph_def, initForms_def, trans_def, tempDNF_def]
         >> fs[trans_def, runForAA_def, validAARunFor_def]
         >> rpt strip_tac
         >> `∃a'. (a',r.E (0,VAR a)) ∈ (trans (POW (props f')) (VAR a))
                     /\ at w 0 ∈ a'`
             by metis_tac[IN_SING] >> fs[trans_def]
         >- (CCONTR_TAC >> `CHOICE (r.V 1) ∈ r.V 1` by metis_tac[CHOICE_DEF]
            >> `(1 = 0) ∨ ∃q'. (CHOICE (r.V 1)) ∈ r.E (1 − 1,q') ∧ q' ∈ r.V (1 − 1)`
              by metis_tac[] >> fs[]
            >> `q' = VAR a` by metis_tac[IN_SING]
            >> fs[] >> metis_tac[NOT_IN_EMPTY])
         >- (metis_tac[])
        )
     >- (fs[ltl2vwaa_free_alph_def, initForms_def, trans_def, tempDNF_def]
          >> fs[trans_def, runForAA_def, validAARunFor_def]
          >> rpt strip_tac
          >> `∃a'. (a',r.E (0,N_VAR a)) ∈ (trans (POW (props f')) (N_VAR a))
                      /\ at w 0 ∈ a'`
             by metis_tac[IN_SING] >> fs[trans_def]
          >- (CCONTR_TAC >> `CHOICE (r.V 1) ∈ r.V 1` by metis_tac[CHOICE_DEF]
             >> `(1 = 0) ∨ ∃q'. (CHOICE (r.V 1)) ∈ r.E (1 − 1,q') ∧ q' ∈ r.V (1 − 1)`
               by metis_tac[] >> fs[]
             >> `q' = N_VAR a` by metis_tac[IN_SING] >> fs[] >> metis_tac[NOT_IN_EMPTY])
          >- (fs[IN_DIFF] >> metis_tac[IN_DIFF])
          >- (metis_tac[IN_DIFF])
        )
     >- (rpt strip_tac
         >> `runForAA (ltl2vwaa_free_alph (POW (props f')) f) r w ∨
             runForAA (ltl2vwaa_free_alph (POW (props f')) f'') r w`
             by metis_tac[RUN_FOR_DISJ_LEMM2]
           >- (`r.V 0 ∈ tempDNF f` by
                 (POP_ASSUM mp_tac
                  >> simp[runForAA_def, validAARunFor_def, ltl2vwaa_free_alph_def]
                  >> rpt strip_tac >> fs[initForms_def]
                 )
               >> `∃a. (a,r.V 1) ∈ trans (POW (props f')) f ∧ at w 0 ∈ a` by metis_tac[]
               >> qexists_tac `a` >> fs[trans_def]
              )
           >- (`r.V 0 ∈ tempDNF f''` by
                 (POP_ASSUM mp_tac
                  >> simp[runForAA_def, validAARunFor_def, ltl2vwaa_free_alph_def]
                  >> rpt strip_tac >> fs[initForms_def]
                 )
               >> `∃a. (a,r.V 1) ∈ trans (POW (props f')) f'' ∧ at w 0 ∈ a` by metis_tac[]
               >> qexists_tac `a` >> fs[trans_def]
              )
        )
     >- (rpt strip_tac
         >> `∃r1.
               runForAA (ltl2vwaa_free_alph (POW (props f')) f) r1 w ∧
               ∃r2.
                 runForAA (ltl2vwaa_free_alph (POW (props f')) f'') r2 w ∧
                 ∀i. r.V i = r1.V i ∪ r2.V i`
            by metis_tac[RUN_FOR_CONJ_LEMM2_UNION]
        >> simp[trans_def, d_conj_def]
        >> `r1.V 0 ∈ tempDNF f` by
             fs[ltl2vwaa_free_alph_def, runForAA_def, validAARunFor_def, initForms_def]
        >> `r2.V 0 ∈ tempDNF f''` by
             fs[ltl2vwaa_free_alph_def, runForAA_def, validAARunFor_def, initForms_def]
        >> `∃a. (a,r1.V 1) ∈ trans (POW (props f')) f ∧ at w 0 ∈ a` by metis_tac[]
        >> `∃a. (a,r2.V 1) ∈ trans (POW (props f')) f'' ∧ at w 0 ∈ a` by metis_tac[]
        >> qexists_tac `a ∩ a'` >> fs[]
        >> qexists_tac `a` >> qexists_tac `a'`
        >> qexists_tac `r1.V 1` >> qexists_tac `r2.V 1`
        >> fs[] >> strip_tac
        )
   >- (rpt strip_tac
       >> fs[trans_def, runForAA_def, validAARunFor_def]
       >> fs[ltl2vwaa_free_alph_def, initForms_def, tempDNF_def]
       >> `∃a. (a,r.E (0,X f)) ∈ trans (POW (props f')) (X f) ∧ at w 0 ∈ a`
           by metis_tac[IN_SING]
       >> fs[trans_def] >> CCONTR_TAC
       >> `r.V 1 ⊆ r.E (0, X f)` by
              (simp[SUBSET_DEF] >> rpt strip_tac
               >> CCONTR_TAC
               >> `(1 = 0) ∨ ∃q'. x ∈ r.E (1 − 1,q') ∧ q' ∈ r.V (1 − 1)`
                       by metis_tac[] >> fs[]
               >> `q' = X f` by metis_tac[IN_SING] >> fs[]
              )
       >> `r.E (0, X f) ⊆ r.V (0 + 1)` by metis_tac[] >> fs[]
       >> `r.E (0, X f) = r.V 1` by metis_tac[SET_EQ_SUBSET]
       >> fs[] >> metis_tac[]
      )
   >- (rpt strip_tac
       >> fs[trans_def, runForAA_def, validAARunFor_def]
       >> fs[ltl2vwaa_free_alph_def, initForms_def, tempDNF_def]
       >> `∃a. (a,r.E (0,U f f'')) ∈ trans (POW (props f')) (U f f'') ∧ at w 0 ∈ a`
           by metis_tac[IN_SING]
       >> qexists_tac `a`
       >> `r.V 1 ⊆ r.E (0, U f f'')` by
             (simp[SUBSET_DEF] >> rpt strip_tac >> fs[]
              >> CCONTR_TAC
              >> `(1 = 0) ∨ ∃q'. x ∈ r.E (1 − 1,q') ∧ q' ∈ r.V (1 − 1)`
                 by metis_tac[] >> fs[]
              >> `q' = U f f''` by metis_tac[IN_SING]
              >> fs[]
             )
       >> `r.E (0, U f f'') ⊆ r.V (0 + 1)` by metis_tac[] >> fs[]
       >> `r.V 1 = r.E (0, U f f'')` by metis_tac[SET_EQ_SUBSET]
       >> fs[trans_def] >> metis_tac[]
      )
   >- (rpt strip_tac
       >> fs[runForAA_def, validAARunFor_def]
       >> fs[ltl2vwaa_free_alph_def, initForms_def, tempDNF_def]
       >> `∃a. (a,r.E (0,R f f'')) ∈ trans (POW (props f')) (R f f'') ∧ at w 0 ∈ a`
             by metis_tac[IN_SING]
       >> qexists_tac `a`
       >> `r.V 1 ⊆ r.E (0, R f f'')` by
               (simp[SUBSET_DEF] >> rpt strip_tac >> fs[]
                >> CCONTR_TAC
                >> `(1 = 0) ∨ ∃q'. x ∈ r.E (1 − 1,q') ∧ q' ∈ r.V (1 − 1)`
                  by metis_tac[] >> fs[]
                >> `q' = R f f''` by metis_tac[IN_SING]
                >> fs[]
               )
       >> `r.E (0, R f f'') ⊆ r.V (0 + 1)` by metis_tac[] >> fs[]
       >> `r.V 1 = r.E (0, R f f'')` by metis_tac[SET_EQ_SUBSET]
       >> fs[trans_def] >> metis_tac[]
      )
  );

val CONJ_DISJ_DISTRIB = store_thm
  ("CONJ_DISJ_DISTRIB",
   ``!x f f1 f2 f3.
  (?r. runForAA (ltl2vwaa_free_alph (POW (props f)) (CONJ f1 (DISJ f2 f3))) r x)
       = ((?r. runForAA (ltl2vwaa_free_alph (POW (props f)) (CONJ f1 f2)) r x)
         \/ ?r. runForAA (ltl2vwaa_free_alph (POW (props f)) (CONJ f1 f3)) r x)``,
  rpt strip_tac >> fs[EQ_IMP_THM] >> rpt strip_tac
    >- (imp_res_tac RUN_FOR_CONJ_LEMM2_UNION
        >> imp_res_tac RUN_FOR_DISJ_LEMM2
          >- (`∃r. runForAA (ltl2vwaa_free_alph (POW (props f)) (CONJ f1 f2)) r x`
              by metis_tac[RUN_FOR_CONJ_LEMM] >> metis_tac[])
          >- (`∃r. runForAA (ltl2vwaa_free_alph (POW (props f)) (CONJ f1 f3)) r x`
               by metis_tac[RUN_FOR_CONJ_LEMM] >> metis_tac[])
       )
    >- (imp_res_tac RUN_FOR_CONJ_LEMM2_UNION
       >> `?r. runForAA (ltl2vwaa_free_alph (POW (props f)) (DISJ f2 f3)) r x`
          by metis_tac[RUN_FOR_DISJ_LEMM]
       >> metis_tac[RUN_FOR_CONJ_LEMM]
       )
    >- (imp_res_tac RUN_FOR_CONJ_LEMM2_UNION
        >> `?r. runForAA (ltl2vwaa_free_alph (POW (props f)) (DISJ f2 f3)) r x`
           by metis_tac[RUN_FOR_DISJ_LEMM]
        >> metis_tac[RUN_FOR_CONJ_LEMM]
       )
  );


val U_AUTO_CHARACTERISATION = store_thm
  ("U_AUTO_CHARACTERISATION",
  ``!f f1 f2.
    (alterA_lang (ltl2vwaa_free_alph (POW (props f)) (U f1 f2))
            = alterA_lang (ltl2vwaa_free_alph (POW (props f))
                                           (DISJ f2 (CONJ f1 (X (U f1 f2))))))``,
  rpt strip_tac >> rw[SET_EQ_SUBSET] >> fs[SUBSET_DEF, alterA_lang_def]
  >> rpt strip_tac
  >- (`(∃run.
       runForAA
       (ltl2vwaa_free_alph (POW (props f))
                          (DISJ f2 (CONJ f1 (X (U f1 f2))))) run x) ∧
       ∀x'.
       x' ∈ word_range x ⇒
       x' ∈
       (ltl2vwaa_free_alph (POW (props f))
                          (DISJ f2 (CONJ f1 (X (U f1 f2))))).alphabet`
      suffices_by metis_tac[]
     >> strip_tac
        >- (`suff x 0 = x` by (Cases_on `x` >> fs[suff_def] >> metis_tac[])
            >> `!a. (a,run.E (0,U f1 f2)) ∈ trans (POW (props f)) f2 ∧ at x 0 ∈ a ⇒
                ∃r'. runForAA (ltl2vwaa_free_alph (POW (props f)) f2) r' x`
              by metis_tac[REPL_F2_LEMM, SUBSET_REFL]
            >> `!a. (a,run.E (0,U f1 f2)) ∈
                d_conj (trans (POW (props f)) f1) {(POW (props f),{U f1 f2})}
                ∧ at x 0 ∈ a ⇒
                ∃r'. runForAA
                        (ltl2vwaa_free_alph (POW (props f)) (CONJ f1 (X (U f1 f2)))) r' x`
                by metis_tac[U_REPL_F1_LEMM]
            >> POP_ASSUM mp_tac
            >> POP_ASSUM mp_tac
            >> RULE_ASSUM_TAC(
               SIMP_RULE (srw_ss())[runForAA_def, validAARunFor_def, ltl2vwaa_free_alph_def])
            >> fs[initForms_def, tempSubForms_def, tempDNF_def]
            >> rpt strip_tac
            >> `(U f1 f2) ∈ run.V 0` by simp[]
            >> `∃a. ((a,run.E (0,U f1 f2)) ∈ trans (POW (props f)) (U f1 f2)) ∧ (at x 0 ∈ a)`
              by metis_tac[]
            >> fs[trans_def]
              >-  (`∃r'. runForAA (ltl2vwaa_free_alph (POW (props f)) f2) r' x`
                       by metis_tac[]
                  >> qexists_tac `r'`
                  >> metis_tac[RUN_FOR_DISJ_LEMM]
                  )
              >- (`∃r'. runForAA
                          (ltl2vwaa_free_alph (POW (props f)) (CONJ f1 (X (U f1 f2))))
                          r' x`
                   by metis_tac[]
                  >> qexists_tac `r'`
                  >> metis_tac[RUN_FOR_DISJ_LEMM]
                 )
              )
        >- (rpt strip_tac >> fs[ltl2vwaa_free_alph_def])
     )
  >- (`(∃run.
         runForAA (ltl2vwaa_free_alph (POW (props f)) (U f1 f2)) run x) ∧
        ∀x'.
        x' ∈ word_range x ⇒
        x' ∈ (ltl2vwaa_free_alph (POW (props f)) (U f1 f2)).alphabet` suffices_by metis_tac[]
     >> rpt strip_tac
     >> `runForAA (ltl2vwaa_free_alph (POW (props f)) f2) run x
        \/ runForAA (ltl2vwaa_free_alph (POW (props f))  (CONJ f1 (X (U f1 f2)))) run x`
         by metis_tac[RUN_FOR_DISJ_LEMM2]
     >> `{U f1 f2} ∈ tempDNF (U f1 f2)` by fs[tempDNF_def]
       >- (`?a. (a,run.V 1) ∈ trans (POW (props f)) (U f1 f2) ∧ at x 0 ∈ a`
               suffices_by metis_tac[REPL_IN_0]
           >> `run.V 0 ∈ tempDNF f2 ⇒
                 ∃a. (a,run.V 1) ∈ trans (POW (props f)) f2 ∧ at x 0 ∈ a`
              by metis_tac[TRANS_LEMM1]
           >> fs[runForAA_def, validAARunFor_def, ltl2vwaa_free_alph_def]
           >> fs[trans_def]
           >> `?a. (a,run.V 1) ∈ trans (POW (props f)) f2 /\ (at x 0 ∈ a)`
              suffices_by metis_tac[]
           >> `∃a. (a,run.V 1) ∈ trans (POW (props f)) f2 ∧ (at x 0 ∈ a)`
                by metis_tac[initForms_def]
           >> qexists_tac `a` >> fs[])
       >- (`?a. (a,run.V 1) ∈ trans (POW (props f)) (U f1 f2) ∧ at x 0 ∈ a`
              suffices_by metis_tac[REPL_IN_0]
           >> `run.V 0 ∈ tempDNF (CONJ f1 (X (U f1 f2))) ⇒
                ∃a. (a,run.V 1) ∈ trans (POW (props f)) (CONJ f1 (X (U f1 f2)))
                      ∧ at x 0 ∈ a`
               by metis_tac[TRANS_LEMM1]
           >> fs[runForAA_def, validAARunFor_def, ltl2vwaa_free_alph_def]
           >> fs[trans_def]
           >> `?a. (a,run.V 1) ∈
                d_conj (trans (POW (props f)) f1) {(POW (props f),{U f1 f2})}
                  ∧ at x 0 ∈ a` suffices_by metis_tac[]
           >> `∃a.
                  (a,run.V 1) ∈
                  d_conj (trans (POW (props f)) f1)
                  (λs. ∃e. (s = (POW (props f),e)) ∧ e ∈ tempDNF (U f1 f2)) ∧
                  at x 0 ∈ a` by metis_tac[initForms_def]
           >> qexists_tac `a` >> fs[tempDNF_def]
           >> `(λs. (s = (POW (props f),{U f1 f2})))
                = {(POW (props f), {U f1 f2})}` by
                  (CCONTR_TAC >> fs[NOT_EQUAL_SETS] >> metis_tac[])
           >> fs[]
          )
       >- (fs[ltl2vwaa_free_alph_def])
       >- (fs[ltl2vwaa_free_alph_def])
     )
  );

val R_AUTO_CHARACTERISATION = store_thm
  ("R_AUTO_CHARACTERISATION",
   ``!f f1 f2. alterA_lang (ltl2vwaa_free_alph (POW (props f)) (R f1 f2)) =
                              alterA_lang (ltl2vwaa_free_alph (POW (props f))
                                       (CONJ f2 (DISJ f1 (X (R f1 f2)))))``,
   rpt strip_tac >> rw[SET_EQ_SUBSET] >> fs[SUBSET_DEF, alterA_lang_def]
   >> rpt strip_tac
      >- (`(∃run.
             runForAA
             (ltl2vwaa_free_alph (POW (props f))
                                (CONJ f2 (DISJ f1 (X (R f1 f2))))) run x) ∧
            ∀x'.
            x' ∈ word_range x ⇒
            x' ∈
            (ltl2vwaa_free_alph (POW (props f))
                               (CONJ f2 (DISJ f1 (X (R f1 f2))))).alphabet`
            suffices_by metis_tac[]
          >> strip_tac
          >> `!a qs f1 f2.
            (a,qs) ∈ trans (POW (props f)) f1 ∧ at x 0 ∈ a ∧ qs ⊆ run.E (0,f2) ⇒
            ∃r'. runForAA (ltl2vwaa_free_alph (POW (props f)) f1) r' (suff x 0)`
             by metis_tac[REPL_F2_LEMM]
         >> `!a. (a,run.E (0,R f1 f2)) ∈
                   d_conj (trans (POW (props f)) f2) {(POW (props f),{R f1 f2})} ∧
                   at x 0 ∈ a ⇒
                   ∃r'.
                   runForAA
                   (ltl2vwaa_free_alph (POW (props f)) (CONJ f2 (X (R f1 f2)))) r'
                   (suff x 0)`
             by metis_tac[R_REPL_F1_LEMM]
          >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
          >> RULE_ASSUM_TAC(
                  SIMP_RULE
                      (srw_ss())[runForAA_def, validAARunFor_def, ltl2vwaa_free_alph_def])
          >> rpt strip_tac
          >> fs[trans_def]
            >- (`?r. runForAA (ltl2vwaa_free_alph (POW (props f)) (CONJ f2 f1)) r x
              \/ ?r. runForAA
                        (ltl2vwaa_free_alph (POW (props f)) (CONJ f2 (X (R f1 f2)))) r x`
               suffices_by metis_tac[CONJ_DISJ_DISTRIB]
                >> fs[initForms_def, tempDNF_def]
                >> `R f1 f2 ∈ run.V 0` by metis_tac[IN_SING]
                >> `∃a. (a,run.E (0,R f1 f2)) ∈ trans (POW (props f)) (R f1 f2)
                   ∧ at x 0 ∈ a`
                   by metis_tac[]
                >> fs[trans_def]
                >> `((a,run.E (0,R f1 f2)) ∈
                       d_conj (trans (POW (props f)) f2) (trans (POW (props f)) f1))
                    \/ (a,run.E (0,R f1 f2)) ∈
                    d_conj (trans (POW (props f)) f2) {(POW (props f),{R f1 f2})}`
                   by metis_tac[D_CONJ_UNION_DISTR, IN_UNION]
                 >- (POP_ASSUM mp_tac >> simp[d_conj_def]
                     >> rpt strip_tac
                     >> `∃r'. runForAA (ltl2vwaa_free_alph (POW (props f)) f1) r' (suff x 0)`
                        by metis_tac[IN_INTER,SUBSET_UNION]
                     >> `∃r'. runForAA (ltl2vwaa_free_alph (POW (props f)) f2) r' (suff x 0)`
                        by metis_tac[IN_INTER,SUBSET_UNION]
                     >> `suff x 0 = x`
                             by (Cases_on `x` >> fs[suff_def] >> metis_tac[])
                     >> `?r. runForAA (ltl2vwaa_free_alph (POW (props f)) (CONJ f2 f1)) r x`
                        by metis_tac[RUN_FOR_CONJ_LEMM]
                     >> dsimp[] >> metis_tac[]
                    )
                 >- (`suff x 0 = x`
                          by (Cases_on `x` >> fs[suff_def] >> metis_tac[])
                     >> dsimp[] >> metis_tac[])
               )
            >- fs[ltl2vwaa_free_alph_def]
         )
      >- (`(∃run.
             runForAA
             (ltl2vwaa_free_alph (POW (props f))
                                (R f1 f2)) run x) ∧
           ∀x'.
           x' ∈ word_range x ⇒
           x' ∈
           (ltl2vwaa_free_alph (POW (props f))
                              (R f1 f2)).alphabet`
            suffices_by metis_tac[] >> rpt strip_tac
          >- (`{R f1 f2} ∈ tempDNF (R f1 f2)` by fs[tempDNF_def]
              >> `run.V 0 ∈ tempDNF (CONJ f2 (DISJ f1 (X (R f1 f2)))) ⇒
                        ∃a. (a,run.V 1) ∈ trans (POW (props f))
                                                (CONJ f2 (DISJ f1 (X (R f1 f2))))
                        ∧ at x 0 ∈ a` by metis_tac[TRANS_LEMM1]
              >> `?a.(a,run.V 1) ∈ trans (POW (props f)) (R f1 f2) ∧ at x 0 ∈ a`
                 suffices_by metis_tac[REPL_IN_0]
              >> fs[runForAA_def, validAARunFor_def, ltl2vwaa_free_alph_def, initForms_def]
              >> `∃a.
                   (a,run.V 1) ∈
                     trans (POW (props f)) (CONJ f2 (DISJ f1 (X (R f1 f2))))
                     ∧ at x 0 ∈ a` by fs[]
              >> fs[trans_def, tempDNF_def]
              >> qexists_tac `a` >> fs[]
              >> `(λs. s = (POW (props f),{R f1 f2}))
                   = {(POW (props f),{R f1 f2})}` suffices_by (rpt strip_tac >> fs[])
              >> fs[SET_EQ_SUBSET, SUBSET_DEF]
             )
          >- fs[ltl2vwaa_free_alph_def]
         )
  );



val RUN_FOR_X_LEMM = store_thm
  ("RUN_FOR_X_LEMM",
   ``!r f g x. runForAA (ltl2vwaa_free_alph (POW (props f)) g) r (suff x 1)
           /\ word_range x ⊆ POW (props f)
      ==> ?r'. runForAA (ltl2vwaa_free_alph (POW (props f)) (X g)) r' x``,
   rpt strip_tac >> fs[runForAA_def]
   >> qabbrev_tac `r_new = ALTERA_RUN
                           (\i. if i = 0 then {X g} else r.V (i-1))
                           (λ(i,q). if i = 0 then r.V 0 else r.E (i-1,q))`
   >> qexists_tac `r_new`
   >> `validAARunFor (ltl2vwaa_free_alph (POW (props f)) (X g)) r_new x ∧
      (validAARunFor (ltl2vwaa_free_alph (POW (props f)) (X g)) r_new x
        ==> acceptingAARun (ltl2vwaa_free_alph (POW (props f)) (X g)) r_new)`
     suffices_by metis_tac[]
   >> conj_tac
     >- (fs[validAARunFor_def] >> rpt strip_tac >> fs[ltl2vwaa_free_alph_def]
         >> fs[tempDNF_def, initForms_def, tempSubForms_def]
           >- (qunabbrev_tac `r_new` >> fs[])
           >- (Cases_on `i` >> qunabbrev_tac `r_new` >> fs[SUBSET_DEF] >> rpt strip_tac
               >> metis_tac[])
           >- (Cases_on `i` >> qunabbrev_tac `r_new` >> fs[]
               >- (qexists_tac `POW (props f)` >> strip_tac
                    >- (fs[trans_def])
                    >- (metis_tac[AT_WORD_RANGE, SUBSET_DEF])
                  )
               >- (`?a. (a,r.E (n,q)) ∈ trans (POW (props f)) q ∧ at (suff x 1) n ∈ a`
                     by metis_tac[]
                   >> qexists_tac `a` >> strip_tac >> fs[]
                   >> `SUC n = n + 1` by simp[]
                   >> metis_tac[AT_SUFF_LEMM]
                  )
              )
           >- (Cases_on `i` >> qunabbrev_tac `r_new` >> fs[SUBSET_DEF]
               >> rpt strip_tac
               >> `x' ∈ r.V (n + 1)` by metis_tac[]
               >> `SUC n = n + 1` by simp[] >> rw[]
              )
           >- (Cases_on `i = 0` >> fs[] >> qunabbrev_tac `r_new`
               >> fs[]
               >> Cases_on `i = 1`
                 >- (qexists_tac `X g` >> fs[])
                 >- (`~(0 = 1)` by simp[]
                    >> `((i - 1) = 0) \/ ∃q'. q ∈ r.E (((i - 1) - 1),q')
                                            ∧ q' ∈ r.V ((i - 1) - 1)`
                       by metis_tac[]
                    >> fs[]
                    >> `((i - 1) = 0) ∨ ∃q'. q ∈ r.E ((i - 1) − 1,q')
                                           ∧ q' ∈ r.V ((i - 1) − 1)`
                       by metis_tac[] >> fs[]
                    >> `~(i <= 1)` by simp[]
                    >> qexists_tac `q''` >> fs[])
              )
        )
     >- (strip_tac
         >> `∀b x'. infBranchOf r_new b ∧ branchFixP b x'
                ⇒ x' ∉ (ltl2vwaa_free_alph (POW (props f)) (X g)).final`
            suffices_by metis_tac[LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM, BRANCH_ACC_LEMM]
         >> rpt strip_tac
         >> `∀b x'. infBranchOf r b ∧ branchFixP b x'
                ⇒ x' ∉ (ltl2vwaa_free_alph (POW (props f)) g).final`
            by metis_tac[LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM, BRANCH_ACC_LEMM]
         >> qabbrev_tac `b' = \i. b (i + 1)`
         >> `x' ∈ {U f1 f2 | U f1 f2 ∈ tempSubForms (X g)}`
            by fs[ltl2vwaa_free_alph_def, finalForms_def]
         >> `x' ∈ {U f1 f2 | U f1 f2 ∈ tempSubForms g}` by fs[tempSubForms_def]
         >> `x' ∈ (ltl2vwaa_free_alph (POW (props f)) g).final`
            by fs[ltl2vwaa_free_alph_def, finalForms_def]
         >> `infBranchOf r b' /\ branchFixP b' x'`
            suffices_by metis_tac[ltl2vwaa_free_alph_def, finalForms_def, tempSubForms_def]
         >> strip_tac
            >- (fs[infBranchOf_def] >> rpt strip_tac >> fs[]
                 >- (qunabbrev_tac `b'` >> qunabbrev_tac `r_new` >> fs[]
                     >> `0 + 1 = 1` by simp[] >> metis_tac[])
                 >- (qunabbrev_tac `b'` >> qunabbrev_tac `r_new` >> fs[]
                     >> `b ((i + 1) + 1) ∈
                           if (i + 1) = 0 then r.V 0 else r.E ((i + 1) − 1,b (i +1))`
                        by metis_tac[] >> fs[])
               )
            >- (fs[branchFixP_def] >> qexists_tac `i-1`
                >> fs[] >> qunabbrev_tac `b'` >> fs[]
               )
        )
  );

val RUN_FOR_X_LEMM2 = store_thm
  ("RUN_FOR_X_LEMM2",
   ``!r x f g. runForAA (ltl2vwaa_free_alph (POW (props f)) (X g)) r x
       ==> ∃run. runForAA (ltl2vwaa_free_alph (POW (props f)) g) run (suff x 1)``,
   rpt strip_tac >> fs[runForAA_def]
   >> qabbrev_tac `r_new = ALTERA_RUN (\i. r.V (i + 1)) (λ(i,q). r.E(i+1,q))`
   >> qexists_tac `r_new`
   >> `validAARunFor (ltl2vwaa_free_alph (POW (props f)) g) r_new (suff x 1) ∧
      (validAARunFor (ltl2vwaa_free_alph (POW (props f)) g) r_new (suff x 1)
          ==> acceptingAARun (ltl2vwaa_free_alph (POW (props f)) g) r_new)`
      suffices_by metis_tac[]
   >> conj_tac
       >- (fs[validAARunFor_def, ltl2vwaa_free_alph_def, initForms_def, tempDNF_def]
           >> `X g ∈ r.V 0` by simp[]
           >> `∃a. (a,r.E (0,X g)) ∈ trans (POW (props f)) (X g)` by metis_tac[]
           >> fs[trans_def]
           >> qunabbrev_tac `r_new` >> fs[]
           >> `!q. q ∈ r.V 1 ==> (1 = 0) \/
                              ∃q'. q ∈ r.E (1 − 1,q') ∧ q' ∈ r.V (1 − 1)`
               by metis_tac[] >> fs[]
           >> `!q. (q ∈ r.V 1) ==> (q ∈ r.E(0,X g))` by metis_tac[IN_SING]
           >> `r.V 1 ⊆ r.E (0, X g)` by metis_tac[SUBSET_DEF]
           >> `0 + 1 = 1` by simp[]
           >> `r.V 1 = r.E (0, X g)` by metis_tac[SUBSET_ANTISYM]
           >> rpt strip_tac >> fs[]
             >- (Induct_on `i` >> fs[tempSubForms_def, tempDNF_def]
                   >- metis_tac[TEMPDNF_TEMPSUBF]
                   >- (fs[SUBSET_DEF] >> rpt strip_tac
                       >> `(((SUC i) + 1) = 0) ∨ ∃q'. x' ∈ r.E (((SUC i) + 1) − 1,q')
                          ∧ q' ∈ r.V (((SUC i) + 1) − 1)`
                          by metis_tac[] >> fs[]
                       >> `∃a. (a,r.E ((SUC i),q')) ∈ trans (POW (props f)) q'`
                          by metis_tac[]
                       >> `(x',q') ∈ TSF` by metis_tac[TRANS_REACHES_SUBFORMS]
                       >> `SUC i = i + 1` by simp[]
                       >> `(q',g) ∈ TSF` by metis_tac[TSF_def, IN_DEF]
                       >> `(x',g) ∈ TSF` by metis_tac[TSF_TRANS_LEMM, IN_DEF, transitive_def]
                       >> metis_tac[TSF_def, IN_DEF]
                      )
                )
             >- (`∃a. (a,r.E ((i + 1),q)) ∈ trans (POW (props f)) q ∧ at x (i + 1) ∈ a`
                  by metis_tac[]
                 >> qexists_tac `a'` >> fs[] >> metis_tac[AT_SUFF_LEMM]
                )
             >- (`r.E (i + 1,q) ⊆ r.V ((i + 1) + 1)` by metis_tac[] >> fs[])
             >- (Cases_on `i = 0` >> fs[]
                 >> `(i + 1) - 1 = i` by simp[]
                 >> `~(i + 1 = 0)` by simp[] >> metis_tac[]
                )
          )
       >- (strip_tac
           >> `∀b x. infBranchOf r_new b ∧ branchFixP b x
                ⇒ x ∉ (ltl2vwaa_free_alph (POW (props f)) g).final`
              suffices_by metis_tac[LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM, BRANCH_ACC_LEMM]
           >> rpt strip_tac
           >> `∀b x. infBranchOf r b ∧ branchFixP b x
                 ⇒ x ∉ (ltl2vwaa_free_alph (POW (props f)) (X g)).final`
               by metis_tac[LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM, BRANCH_ACC_LEMM]
           >> `!i. b i ∈ r_new.V i` by metis_tac[BRANCH_V_LEMM]
           >> fs[ltl2vwaa_free_alph_def, finalForms_def, tempSubForms_def]
           >> qabbrev_tac `b' = \i. if i = 0 then X g else b (i - 1)`
           >> `infBranchOf r b' ∧ branchFixP b' x'` suffices_by metis_tac[]
           >> strip_tac
             >- (fs[infBranchOf_def] >> qunabbrev_tac `b'` >> qunabbrev_tac `r_new`
                 >> rpt strip_tac >> fs[validAARunFor_def, initForms_def, tempDNF_def]
                 >> Cases_on `i = 0` >> fs[]
                   >- (`b 0 ∈ r.V (0 + 1)` by metis_tac[] >> fs[]
                       >> `(1 = 0) ∨ ∃q'. b 0 ∈ r.E (1 − 1,q') ∧ q' ∈ r.V (1 − 1)`
                          by metis_tac[] >> fs[]
                       >> metis_tac[IN_SING]
                      )
                   >- (`?j. i = SUC j` by (Cases_on `i` >> fs[])
                       >> `i = j +1` by simp[]
                       >> `b i ∈ r.E (i,b j)` by metis_tac[]
                       >> fs[]
                      )
                )
             >- (fs[branchFixP_def] >> qexists_tac `i+1`
                 >> qunabbrev_tac `b'` >> fs[]
                )
          )
  );

val EVTL_F2_TRANS_LEMM = store_thm
  ("EVTL_F2_TRANS_LEMM",
  ``!f f1 f2 r w. runForAA (ltl2vwaa_free_alph (POW (props f)) (U f1 f2)) r w
      ==> (?n a. (a, r.E (n, U f1 f2)) ∈ trans (POW (props f)) f2
          ∧ at w n ∈ a)``,
  rpt strip_tac >> fs[runForAA_def]
  >> `∀b x. infBranchOf r b ∧ branchFixP b x
      ⇒ x ∉ (ltl2vwaa_free_alph (POW (props f)) (U f1 f2)).final`
     by metis_tac[LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM, BRANCH_ACC_LEMM]
  >> CCONTR_TAC
  >> fs[validAARunFor_def]
  >> `!i. U f1 f2 ∈ r.V i` by (
      Induct_on `i` >> fs[ltl2vwaa_free_alph_def, initForms_def, tempDNF_def]
      >> `∃a. (a,r.E (i,U f1 f2)) ∈ trans (POW (props f)) (U f1 f2)
            ∧ (at w i ∈ a)` by metis_tac[]
      >> fs[trans_def]
        >- (metis_tac[])
        >- (fs[d_conj_def]
            >> `U f1 f2 ∈ r.E (i, U f1 f2)` by metis_tac[IN_UNION, IN_SING]
            >> `U f1 f2 ∈ r.V (i + 1)` by metis_tac[SUBSET_DEF]
            >> metis_tac[SUC_ONE_ADD,ADD_COMM]
           )
  )
  >> `!i. U f1 f2 ∈ r.E (i, U f1 f2)` by (
      CCONTR_TAC >> fs[]
      >> fs[ltl2vwaa_free_alph_def, initForms_def, tempDNF_def]
      >> `(i = 0) ∨ ∃q'. (U f1 f2) ∈ r.E (i − 1,q') ∧ q' ∈ r.V (i − 1)`
         by metis_tac[]
       >- (rw[]
           >> `U f1 f2 ∈ r.V 0` by metis_tac[IN_SING]
           >> `(1 = 0) ∨ ∃q'. (U f1 f2) ∈ r.E (1 − 1,q') ∧ q' ∈ r.V (1 − 1)`
              by metis_tac[] >> fs[]
           >> `q' = U f1 f2` by metis_tac[IN_SING] >> fs[]
          )
       >- (`U f1 f2 ∈ r.V i` by fs[]
           >> `∃a. (a,r.E (i,(U f1 f2))) ∈ trans (POW (props f)) (U f1 f2)
                  ∧ at w i ∈ a` by metis_tac[]
           >> fs[trans_def]
           >- (metis_tac[])
           >- (fs[d_conj_def]
                 >> `U f1 f2 ∈ r.E (i, U f1 f2)` by metis_tac[IN_UNION, IN_SING]
                 >> `U f1 f2 ∈ r.V (i + 1)` by metis_tac[SUBSET_DEF]
                 >> metis_tac[SUC_ONE_ADD,ADD_COMM]
              )
          )
  )
  >> `infBranchOf r (\_. U f1 f2)` by fs[infBranchOf_def]
  >> `branchFixP (\_. U f1 f2) (U f1 f2)` by fs[branchFixP_def]
  >> fs[ltl2vwaa_free_alph_def, finalForms_def]
  >> `U f1 f2 ≠ U f1 f2 ∨ U f1 f2 ∉ tempSubForms (U f1 f2)`
      by metis_tac[]
  >> fs[tempSubForms_def]
  );

val ALL_F1_BEFORE_F2 = store_thm
  ("ALL_F1_BEFORE_F2",
  ``!f f1 f2 r w. runForAA (ltl2vwaa_free_alph (POW (props f)) (U f1 f2)) r w
      ==> ?n a. (a, r.E (n, U f1 f2)) ∈ trans (POW (props f)) f2
          ∧ at w n ∈ a
          ∧ (!i. i < n ==> ?a'. (a', r.E (i, U f1 f2)) ∈
                       d_conj (trans (POW (props f)) f1) {(POW (props f), {U f1 f2})}
                       ∧ at w i ∈ a')``,
  rpt strip_tac
  >> imp_res_tac (SIMP_RULE bool_ss [LEAST_EXISTS] EVTL_F2_TRANS_LEMM)
  >> qabbrev_tac `N = LEAST n. (∃a.
                                 (a,r.E (n,U f1 f2)) ∈ trans (POW (props f)) f2 ∧
                                 at w n ∈ a)`
  >> qexists_tac `N` >> qexists_tac `a`
  >> simp[]
  >> CCONTR_TAC >> fs[]
  >> `!j. j < N ==> U f1 f2 ∈ r.V j` by (
      Induct_on `j`
       >- (fs[runForAA_def, validAARunFor_def, ltl2vwaa_free_alph_def, initForms_def]
           >> metis_tac[tempDNF_def, IN_SING]
          )
       >- (strip_tac >> fs[runForAA_def, validAARunFor_def, ltl2vwaa_free_alph_def, trans_def]
           >> `∃a'. (a',r.E (j,U f1 f2)) ∈ trans (POW (props f)) (U f1 f2) ∧ at w j ∈ a'`
              by metis_tac[]
           >> fs[trans_def]
             >- metis_tac[DECIDE ``SUC j < N ==> j < N``]
             >- (fs[d_conj_def]
                 >> metis_tac[DECIDE ``SUC j = j + 1``, SUBSET_DEF,IN_UNION,IN_SING])
          )
  )
  >> `U f1 f2 ∈ r.V i` by fs[]
  >> fs[runForAA_def,validAARunFor_def,ltl2vwaa_free_alph_def,trans_def]
  >> `∃a'. (a',r.E (i,(U f1 f2))) ∈ trans (POW (props f)) (U f1 f2) ∧ at w i ∈ a'`
     by metis_tac[]
  >> fs[trans_def]
  >> metis_tac[]
  );

val EVTL_F2_RUN_LEMM = store_thm
  ("EVTL_F2_RUN_LEMM",
  ``!f f1 f2 r w. runForAA (ltl2vwaa_free_alph (POW (props f)) (U f1 f2)) r w
        ==> ?r' n. runForAA (ltl2vwaa_free_alph (POW (props f)) f2) r' (suff w n)
        ∧ !i. i < n ==> ?r'. runForAA (ltl2vwaa_free_alph (POW (props f)) f1) r' (suff w i)``,
  rpt strip_tac
  >> `∃n a. (a,r.E (n,U f1 f2)) ∈ trans (POW (props f)) f2 ∧ at w n ∈ a
           ∧ (!i. i < n ==> ?a'. (a', r.E (i, U f1 f2)) ∈
                        d_conj (trans (POW (props f)) f1) {(POW (props f), {U f1 f2})}
                        ∧ at w i ∈ a')`
      by metis_tac[ALL_F1_BEFORE_F2]
  >> `∃r'. runForAA (ltl2vwaa_free_alph (POW (props f)) f2) r' (suff w n)`
      by metis_tac[REPL_F2_LEMM, SUBSET_REFL]
  >> qexists_tac `r'` >> qexists_tac `n` >> simp[]
  >> rpt strip_tac
  >> `∃a'.
           (a',r.E (i,U f1 f2)) ∈
           d_conj (trans (POW (props f)) f1)
           {(POW (props f),{U f1 f2})} ∧ at w i ∈ a'`
     by fs[]
  >> imp_res_tac U_REPL_F1_LEMM
  >> metis_tac[RUN_FOR_CONJ_LEMM2_UNION]
  );

val always_run_cond_def = Define `
  always_run_cond f1 f2 rs s i q =
     if q ∈ s
     then (if q = R f1 f2
           then {R f1 f2} ∪ ((rs i).V 1)
           else let j = (LEAST j. q ∈ (rs j).V (i-j)) in
                    (rs j).E (i-j,q))
     else {}`

val always_run_V_def = Define `
   (always_run_V f1 f2 rs 0 = {R f1 f2})
 ∧ (always_run_V f1 f2 rs (SUC i) =
       {R f1 f2} ∪ {q | ?q'. q' ∈ always_run_V f1 f2 rs i
                         ∧ q ∈ always_run_cond f1 f2 rs (always_run_V f1 f2 rs i) i q'}
   )`

val always_run_E_def = Define `
  always_run_E f1 f2 rs (i,q) =
          always_run_cond f1 f2 rs (always_run_V f1 f2 rs i) i q`

val always_run_def = Define `
  always_run f1 f2 rs = ALTERA_RUN (always_run_V f1 f2 rs) (always_run_E f1 f2 rs)`

val ALWAYS_RUN_LEMM1 = store_thm
  ("ALWAYS_RUN_LEMM1",
  ``∀f' f1 f2 w rs.
   (!n. runForAA (ltl2vwaa_free_alph (POW (props f')) f2) (rs n) (suff w n))
     ==> (!i q. q ∈ always_run_V f1 f2 rs i /\ ~(q = R f1 f2)
         ==> (LEAST j. q ∈ (rs j).V (i − j)) < i)``,
  rpt gen_tac >> strip_tac >> Induct_on `i`
  >> rpt strip_tac >> fs[always_run_V_def] >> rpt strip_tac
  >> Cases_on `q' = R f1 f2`
    >- (`q ∈ {R f1 f2} ∪ (rs i).V 1` by metis_tac[always_run_cond_def]
        >> `q ∈ (rs i).V 1` by metis_tac[IN_UNION,IN_SING]
        >> fs[] >> numLib.LEAST_ELIM_TAC >> rpt strip_tac
          >- (qexists_tac `i` >> simp[])
          >- (CCONTR_TAC >> fs[SUC_ONE_ADD]
              >> `i < n` by simp[]
              >> `q ∉ (rs i).V (i + 1 - i)` by metis_tac[]
              >> fs[]
             )
       )
    >- (`q ∈ (rs (LEAST j. q' ∈ (rs j).V (i − j))).E
             (i − (LEAST j. q' ∈ (rs j).V (i − j)),q')`
          by metis_tac[always_run_cond_def]
        >> qabbrev_tac `N' = (LEAST j. q' ∈ (rs j).V (i − j))`
        >> `N' < i` by metis_tac[]
        >> numLib.LEAST_ELIM_TAC >> rpt strip_tac
         >- (fs[runForAA_def, validAARunFor_def, ltl2vwaa_free_alph_def]
             >> `(rs N').E (i-N',q') ⊆ (rs N').V ((i-N') + 1)`
                by metis_tac[]
             >> qexists_tac `N'` >> fs[SUB]
             >> `q ∈ (rs N').V (i − N' + 1)` by metis_tac[SUBSET_DEF]
             >> fs[SUC_ONE_ADD]
             >> `i - N' + 1 = i + 1 - N'` by simp[] >> metis_tac[]
            )
         >- (CCONTR_TAC >> `N' < n` by simp[]
             >> `q ∉ (rs N').V (SUC i − N')` by metis_tac[]
             >> fs[runForAA_def, validAARunFor_def, ltl2vwaa_free_alph_def]
             >> `(rs N').E (i - N',q') ⊆ (rs N').V (i - N' + 1)` by fs[]
             >> `q ∈ (rs N').V (i - N' + 1)` by metis_tac[SUBSET_DEF]
             >> `SUC i - N' = i - N' + 1` by simp[]
             >> metis_tac[]
            )
       )
  );

val ALWAYS_RUN_LEMM2 = store_thm
  ("ALWAYS_RUN_LEMM2",
  ``∀f' f1 f2 w rs.
    (!n .runForAA (ltl2vwaa_free_alph (POW (props f')) f2) (rs n) (suff w n))
     ==> (!i q. q ∈ always_run_V f1 f2 rs i /\ ~(q = R f1 f2)
            ==>
            let N = LEAST j. q ∈ (rs j).V (i - j)
            in q ∈ (rs N).V (i - N))``,
  rpt gen_tac >> strip_tac >> Induct_on `i`
   >- (rpt strip_tac >> fs[] >> fs[always_run_V_def])
   >- (rpt strip_tac >> fs[always_run_V_def] >> Cases_on `q' = R f1 f2`
         >- (`q ∈ {R f1 f2} ∪ (rs i).V 1`
                by metis_tac[always_run_cond_def]
             >> numLib.LEAST_ELIM_TAC >> rpt strip_tac
             >> qexists_tac `i` >> fs[] >> fs[]
            )
         >- (fs[always_run_V_def]
            >> qabbrev_tac `N = LEAST j. q' ∈ (rs j).V (i − j)`
            >> `q ∈ (rs N).E (i-N,q')` by metis_tac[always_run_cond_def]
            >> numLib.LEAST_ELIM_TAC >> rpt strip_tac
            >> qexists_tac `N`
            >> `N < i` by metis_tac[ALWAYS_RUN_LEMM1]
            >> fs[runForAA_def, validAARunFor_def]
            >> `(rs N).E (i - N,q') ⊆ (rs N).V ((i - N) + 1)` by metis_tac[]
            >> `i - N + 1 = SUC i - N` by simp[]
            >> metis_tac[SUBSET_DEF]
            )
      )
  );

val LEQ_CHAIN_FIXP = store_thm
  ("LEQ_CHAIN_FIXP",
  ``!f n. (!i. i >= n ==> f (i + 1) <= f i)
     ==> (?k. k ∈ minimal_elements { f l | n <= l }
           (rrestrict (rel_to_reln $<=) { f l | n <= l }))``,
  rpt strip_tac
  >> `linear_order (rrestrict (rel_to_reln $<=) {f l | n <= l}) {f l | n <= l}` by (
      fs[linear_order_def] >> rpt strip_tac
        >- (fs[SUBSET_DEF, domain_def, rrestrict_def] >> rpt strip_tac
            >> metis_tac[])
        >- (fs[SUBSET_DEF, range_def, rrestrict_def] >> rpt strip_tac
            >> metis_tac[])
        >- (fs[transitive_def, rrestrict_def, rel_to_reln_def] >> rpt strip_tac)
        >- (fs[antisym_def, rrestrict_def, rel_to_reln_def])
        >- (fs[rrestrict_def, rel_to_reln_def] >> Cases_on `f l <= f l'`
            >- (disj1_tac >> strip_tac >> fs[] >> metis_tac[])
            >- (fs[] >> metis_tac[])
           )
  )
  >> `!k l. k >= l ∧ l >= n ==> f k <= f l` by (
      Induct_on `k`
         >- (rpt strip_tac >> fs[] >> `l = 0` by simp[] >> fs[])
         >- (rpt strip_tac >> Cases_on `SUC k = l` >> fs[]
             >> `k >= l` by simp[] >> `f k <= f l` by simp[]
             >> `f (SUC k) <= f k` suffices_by simp[]
             >> `k >= n` by simp[]
             >> metis_tac[DECIDE ``SUC k = k + 1``]
            )
  )
  >> `FINITE { f l | n <= l }` by (
     `{ f l | n <= l } ⊆ count (f n + 1)` by (
         fs[SUBSET_DEF, count_def] >> rpt strip_tac
         >> `x <= f n` suffices_by (rpt strip_tac >> fs[LESS_OR_EQ])
         >> rw[]
     )
     >> metis_tac[SUBSET_FINITE,FINITE_COUNT]
  )
  >> `~({ f l | n <= l } = {})` by (
         `f n ∈ { f l | n <= l }` by (
             fs[] >> qexists_tac `n` >> fs[]
         ) >> metis_tac[NOT_IN_EMPTY]
  )
  >> metis_tac[finite_linear_order_has_minimal]
  );

val ALWAYS_RUN_ACC_LEMM = store_thm
  ("ALWAYS_RUN_ACC_LEMM",
  ``∀f' f1 f2 w rs.
  (!n .runForAA (ltl2vwaa_free_alph (POW (props f')) f2) (rs n) (suff w n))
  ∧ validAARunFor (ltl2vwaa_free_alph (POW (props f')) (R f1 f2)) (always_run f1 f2 rs) w
     ==> (!b x. infBranchOf (always_run f1 f2 rs) b ∧ branchFixP b x
             ∧ ~(x = R f1 f2)
             ==> ?b' i. infBranchOf (rs i) b' ∧ branchFixP b' x)``,
  rpt strip_tac
  >> imp_res_tac BRANCH_V_LEMM
  >> fs[branchFixP_def]
  >> `!m. m >= i ==> x ∈ (always_run f1 f2 rs).V m` by metis_tac[]
  >> fs[always_run_def]
  >> `!m. m >= i ==> (let N = LEAST j. x ∈ (rs j).V (m - j)
                      in x ∈ (rs N).V (m - N))`
     by metis_tac[ALWAYS_RUN_LEMM2]
  >> fs[]
  >> qabbrev_tac `N = \m. LEAST j. x ∈ (rs j).V (m - j)`
  >> `!k. k >= i ==> N (k + 1) <= N k` by (
      rpt strip_tac
      >> `x ∈ (rs (N k)).V (k - (N k))` by fs[]
      >> `x ∈ (always_run f1 f2 rs).E (k, x)` by (
          fs[infBranchOf_def, always_run_def]
          >> `b (k+1) = x` by simp[] >> metis_tac[]
      )
      >> `x ∈ (rs (N k)).E (k - N k, x)` by (
          fs[always_run_def, always_run_E_def, always_run_cond_def]
          >> metis_tac[]
      )
      >> `x ∈ (rs (N k)).V ((k - N k) + 1)`
           by metis_tac[runForAA_def,validAARunFor_def,SUBSET_DEF]
      >> `N k < k` by metis_tac[ALWAYS_RUN_LEMM1]
      >> `(k - N k) + 1 = (k + 1) - N k` by fs[SUB_LEFT_ADD, ADD_COMM]
      >> `x ∈ (rs (N k)).V ((k + 1) - N k)` by fs[]
      >> CCONTR_TAC >> `N k < N (k + 1)` by simp[]
      >> qunabbrev_tac `N` >> POP_ASSUM mp_tac
      >> simp[] >> strip_tac
      >> imp_res_tac LESS_LEAST
      >> POP_ASSUM mp_tac >> simp[] >> metis_tac[]
  )
  >> `∃k.
        k ∈
        minimal_elements {N l | i <= l}
        (rrestrict (rel_to_reln $<=) {N l | i <= l})` by metis_tac[LEQ_CHAIN_FIXP]
  >> `?j. (k = N j) /\ (i <= j)` by (
      fs[minimal_elements_def, rrestrict_def, rel_to_reln_def]
      >> metis_tac[]
  )
  >> `!h. h >= j ==> x ∈ (rs (N j)).V (h - N j) ∧ (N h = N j)` by (
      strip_tac >> strip_tac
      >> `h >= i` by simp[]
      >> `x ∈
          (rs (LEAST j. x ∈ (rs j).V (h − j))).V
          (h − LEAST j. x ∈ (rs j).V (h − j))` by metis_tac[]
      >> `x ∈ (rs (N h)).V (h - N h)` by fs[]
      >> `N j = N h` suffices_by metis_tac[]
      >> `!a b. a >= b ∧ b >= i ==> N a <= N b` by (
          Induct_on `a`
             >- (rpt strip_tac >> fs[] >> `b' = 0` by simp[] >> fs[])
             >- (rpt strip_tac >> Cases_on `SUC a = b'` >> fs[]
                 >> `a >= b'` by simp[] >> `N a <= N b'` by simp[]
                 >> `N (SUC a) <= N a` suffices_by simp[]
                 >> `a >= i` by simp[]
                 >> metis_tac[DECIDE ``SUC a = a + 1``]
                )
      )
      >> `N h <= N j` by fs[]
      >> `N j <= N h` by (
          fs[minimal_elements_def,rrestrict_def, rel_to_reln_def]
          >> fs[]
          >> `(∃l. (N h = N l) ∧ i ≤ l) ∧ N h ≤ N j ∧
              (∃l. (N h = N l) ∧ i ≤ l) ∧ (∃l. (N j = N l) ∧ i ≤ l)` by (
              rpt strip_tac >> fs[]
                  >- (qexists_tac `h` >> fs[])
                  >- (qexists_tac `h` >> fs[])
                  >- (qexists_tac `j` >> fs[])
          ) >> metis_tac[]
      )
      >> fs[]
  )
  >> `infBranchSuffOf (rs (N j)) (j - N j) (\_. x)` by (
      fs[infBranchSuffOf_def]
      >> `!a. x ∈ (rs (N j)).E (a + (j - N j),x)` suffices_by fs[]
      >> rpt strip_tac
      >> `x ∈ always_run_V f1 f2 rs j` by fs[]
      >> `x ∈ always_run_V f1 f2 rs (a + j)` by fs[]
      >> `N j < j` by metis_tac[ALWAYS_RUN_LEMM1]
      >> fs[infBranchOf_def]
      >> `b (a + j + 1) = x` by simp[]
      >> `b (a + j) = x` by simp[]
      >> `x ∈ always_run_E f1 f2 rs (a + j, x)` by metis_tac[]
      >> fs[always_run_E_def, always_run_cond_def]
      >> `x ∈
           (rs (LEAST j'. x ∈ (rs j').V (a + j − j'))).E
           (a + j − (LEAST j'. x ∈ (rs j').V (a + j − j')),x)` by metis_tac[]
      >> `x ∈ (rs (N (a + j))).E (a + j - N (a + j),x)` by metis_tac[]
      >> metis_tac[DECIDE ``a + j >= j``]
  )
  >> qabbrev_tac `b1 = (λ_ : num. x : α ltl_frml)`
  >> `infBranchSuffOf (rs (N j)) (j − (N j)) b1` by fs[]
  >> `validAARunFor (ltl2vwaa_free_alph (POW (props f')) f2) (rs (N j)) (suff w (N j))`
     by metis_tac[runForAA_def]
  >> imp_res_tac BRANCH_SUFF_LEMM
  >> qexists_tac `b''` >> qexists_tac `N j`
  >> fs[] >> qexists_tac `j - N j` >> fs[]
  >> strip_tac
    >- metis_tac[DECIDE ``0 + (j - N j) = j - N j``]
    >- (rpt strip_tac
        >> `?q. q + (j - N j) = m` by fs[LESS_EQ_ADD_EXISTS]
        >> `b'' m = b1 q` by metis_tac[]
        >> metis_tac[]
       )
  );

val ALWAYS_RUN = store_thm
  ("ALWAYS_RUN",
``!f' f1 f2 w. (word_range w ⊆ POW (props f')) ∧
  (!n. ?r. runForAA (ltl2vwaa_free_alph (POW (props f')) f2) r (suff w n))
     ==> (?r. runForAA (ltl2vwaa_free_alph (POW (props f')) (R f1 f2)) r w)``,
  rpt strip_tac
  >> `?rs. !n. runForAA (ltl2vwaa_free_alph (POW (props f')) f2) (rs n) (suff w n)`
     by metis_tac[SKOLEM_THM]
  >> qexists_tac `always_run f1 f2 rs`
  >> `!n. ((rs n).V 0) ∈ tempDNF f2
       ==> ∃a. (a,(rs n).V 1) ∈ trans (POW (props f')) f2 ∧ at (suff w n) 0 ∈ a`
     by metis_tac[TRANS_LEMM1]
  >> simp[runForAA_def]
  >> `(validAARunFor (ltl2vwaa_free_alph (POW (props f')) (R f1 f2))
       (always_run f1 f2 rs) w)
       ∧ ((validAARunFor (ltl2vwaa_free_alph (POW (props f')) (R f1 f2))
                      (always_run f1 f2 rs) w)
              ==> acceptingAARun (ltl2vwaa_free_alph (POW (props f')) (R f1 f2))
              (always_run f1 f2 rs))` suffices_by metis_tac[]
  >> strip_tac
    >- (imp_res_tac ALWAYS_RUN_LEMM2
        >> imp_res_tac ALWAYS_RUN_LEMM1
        >> fs[validAARunFor_def, ltl2vwaa_free_alph_def, initForms_def, tempDNF_def]
        >> rpt strip_tac
          >- fs[always_run_def, always_run_V_def]
          >- (fs[always_run_def, always_run_V_def]
              >> Induct_on `i` >> fs[always_run_V_def, tempSubForms_def]
              >> fs[SUBSET_DEF] >> rpt strip_tac
              >> `((q' = R f1 f2) ∨ q' ∈ tempSubForms f1) ∨ q' ∈ tempSubForms f2`
                 by metis_tac[]
                 >- (fs[always_run_cond_def]
                     >> `x ∈ {R f1 f2} ∪ (rs i).V 1` by metis_tac[]
                     >> `x ∈ {R f1 f2} \/ x ∈ (rs i).V 1`
                         by metis_tac[IN_UNION]
                       >- metis_tac[IN_SING]
                       >- (fs[runForAA_def, validAARunFor_def]
                           >> `(rs i).V 0 ∈ tempDNF f2`
                              by metis_tac[]
                           >> imp_res_tac TEMPDNF_TEMPSUBF
                           >> disj2_tac
                           >> metis_tac[SUBSET_DEF]
                          )
                    )
                 >- (`~(q' = R f1 f2)` by (
                             CCONTR_TAC >> fs[]
                             >> `R f1 f2 ∈ subForms f1` by metis_tac[TSF_IMPL_SF]
                             >> `f1 ∈ subForms (R f1 f2)`
                                   by fs[subForms_def, SUBFORMS_REFL]
                             >> `f1 = R f1 f2` by metis_tac[SF_ANTISYM_LEMM]
                             >> `(!f g. ~(f = R f g))` by (Induct_on `f` >> fs[])
                             >> metis_tac[]
                      )
                     >> `x ∈ (rs (LEAST j. q' ∈ (rs j).V (i − j))).E
                               (i − (LEAST j. q' ∈ (rs j).V (i − j)),q')`
                         by metis_tac[always_run_cond_def]
                     >> qabbrev_tac `N = (LEAST j. q' ∈ (rs j).V (i − j))`
                     >> fs[runForAA_def, validAARunFor_def]
                     >> `q' ∈ (rs N).V (i - N)` by (
                               qunabbrev_tac `N` >> numLib.LEAST_ELIM_TAC
                               >> simp[] >> metis_tac[])
                     >> `?a. (a,(rs N).E (i-N,q')) ∈ trans (POW (props f')) q'`
                             by metis_tac[]
                     >> `(x,q') ∈ TSF` by metis_tac[TRANS_REACHES_SUBFORMS]
                     >> disj1_tac >> disj2_tac
                     >> metis_tac[TSF_def, IN_DEF, TSF_TRANS_LEMM, transitive_def]
                    )
                 >- (`~(q' = R f1 f2)` by (
                            CCONTR_TAC >> fs[]
                            >> `R f1 f2 ∈ subForms f2` by metis_tac[TSF_IMPL_SF]
                            >> `f2 ∈ subForms (R f1 f2)`
                                    by fs[subForms_def, SUBFORMS_REFL]
                            >> `f2 = R f1 f2` by metis_tac[SF_ANTISYM_LEMM]
                            >> `(!f g. ~(g = R f g))` by (Induct_on `g` >> fs[])
                            >> metis_tac[]
                        )
                      >> `x ∈ (rs (LEAST j. q' ∈ (rs j).V (i − j))).E
                                  (i − (LEAST j. q' ∈ (rs j).V (i − j)),q')`
                         by metis_tac[always_run_cond_def]
                      >> qabbrev_tac `N = (LEAST j. q' ∈ (rs j).V (i − j))`
                      >> fs[runForAA_def, validAARunFor_def]
                      >> `q' ∈ (rs N).V (i - N)` by (
                           qunabbrev_tac `N` >> numLib.LEAST_ELIM_TAC
                           >> simp[] >> metis_tac[])
                      >> `?a. (a,(rs N).E (i-N,q')) ∈ trans (POW (props f')) q'`
                            by metis_tac[]
                      >> `(x,q') ∈ TSF` by metis_tac[TRANS_REACHES_SUBFORMS]
                      >> disj2_tac
                      >> metis_tac[TSF_def, IN_DEF, TSF_TRANS_LEMM, transitive_def]
                    )
             )
          >- (Cases_on `q = R f1 f2`
              >- (fs[always_run_def, always_run_V_def, always_run_E_def]
                  >> fs[always_run_V_def, always_run_cond_def]
                  >> fs[runForAA_def, validAARunFor_def]
                  >> fs[trans_def, d_conj_def]
                  >> `∃a.
                        (a,(rs i).V 1) ∈ trans (POW (props f')) f2 ∧
                        at (suff w i) 0 ∈ a` by metis_tac[]
                  >> qexists_tac `a` >> dsimp[] >> disj2_tac
                  >> qexists_tac `a` >> qexists_tac `(rs i).V 1`
                  >> fs[AT_SUFF_LEMM]
                  >> strip_tac
                    >- metis_tac[TRANS_ALPH_LEMM,INTER_SUBSET_EQN]
                    >- metis_tac[UNION_COMM]
                 )
              >- (fs[always_run_def, always_run_V_def, always_run_E_def]
                    >> fs[always_run_V_def, always_run_cond_def]
                    >> fs[runForAA_def, validAARunFor_def]
                    >> fs[trans_def, d_conj_def]
                    >> qabbrev_tac `N = LEAST j. q ∈ (rs j).V (i − j)`
                    >> `q ∈ (rs N).V (i − N)` by metis_tac[]
                    >> `∃a.
                         (a,(rs N).E (i - N,q)) ∈ trans (POW (props f')) q ∧
                          at (suff w N) (i - N) ∈ a` by fs[]
                    >> qexists_tac `a` >> fs[AT_SUFF_LEMM]
                    >> `N < i` by metis_tac[]
                    >> `i - N + N = i` by simp[]
                    >> metis_tac[]
                 )
             )
          >- (fs[SUBSET_DEF, always_run_def, always_run_V_def] >> rpt strip_tac
                >> `x ∈ always_run_V f1 f2 rs (SUC i)`
                     suffices_by metis_tac[SUC_ONE_ADD, ADD_COMM]
                >> fs[always_run_V_def, always_run_E_def]
                >> Cases_on `x = R f1 f2` >> fs[]
                >> Cases_on `q = R f1 f2`
                    >- (qexists_tac `q` >> fs[]
                        >> Cases_on `i` >> fs[always_run_V_def])
                    >- (qexists_tac `q` >> fs[]
                        >> fs[always_run_cond_def]
                        >> metis_tac[NOT_IN_EMPTY]
                       )
             )
          >- (Cases_on `i = 0` >> fs[]
              >> `?j. i = SUC j` by (Cases_on `i` >> fs[])
              >> rw[]
              >> fs[always_run_def, always_run_V_def]
              >> `!i. R f1 f2 ∈ (always_run f1 f2 rs).V i` by (
                     strip_tac >> fs[always_run_def,always_run_V_def]
                     >> Cases_on `i` >> fs[always_run_V_def]
                 )
                >- (qexists_tac `R f1 f2`
                    >> strip_tac >> fs[always_run_def, always_run_V_def, always_run_E_def]
                    >> fs[always_run_cond_def]
                   )
                >- (qexists_tac `q'` >> fs[] >> simp[always_run_E_def])
             )
       )
    >- (rpt strip_tac
        >> `∀b x. infBranchOf (always_run f1 f2 rs) b ∧ branchFixP b x
              ⇒ x ∉ (ltl2vwaa_free_alph (POW (props f')) (R f1 f2)).final`
           suffices_by metis_tac[BRANCH_ACC_LEMM, LTL2WAA_ISFINITE, LTL2WAA_ISWEAK_LEMM]
        >> rpt strip_tac
        >> Cases_on `x = R f1 f2`
        >> imp_res_tac ALWAYS_RUN_LEMM2
         >- fs[ltl2vwaa_free_alph_def, finalForms_def]
         >- (`∃b' i. infBranchOf (rs i) b' ∧ branchFixP b' x`
              by metis_tac[ALWAYS_RUN_ACC_LEMM]
             >> `x ∉ (ltl2vwaa_free_alph (POW (props f')) f2).final`
             by metis_tac[BRANCH_ACC_LEMM,LTL2WAA_ISFINITE,LTL2WAA_ISWEAK_LEMM,runForAA_def]
             >> fs[ltl2vwaa_free_alph_def, finalForms_def]
             >> `U f1' f2' ∈ tempSubForms f2` suffices_by metis_tac[]
             >> `?i. U f1' f2' ∈ (always_run f1 f2 rs).V i`
                 by metis_tac[branchFixP_def, BRANCH_V_LEMM]
             >> `~(U f1' f2' = R f1 f2)` by simp[]
             >> fs[always_run_def]
             >> `(U f1' f2') ∈
                   (rs (LEAST j. (U f1' f2') ∈ (rs j).V (i' − j))).V
                    (i' − LEAST j. (U f1' f2') ∈ (rs j).V (i' − j))`
                by metis_tac[]
             >> qabbrev_tac `N = LEAST j. U f1' f2' ∈ (rs j).V (i' − j)`
             >> `(rs N).V (i' - N ) ⊆ tempSubForms f2`
                  by fs[runForAA_def, validAARunFor_def]
             >> metis_tac[SUBSET_DEF]
            )
       )
  );

val ALWAYS_F2_OR_EVTL_F1_R = store_thm
  ("ALWAYS_F2_OR_EVTL_F1_R",
  ``!f f1 f2 r w. runForAA (ltl2vwaa_free_alph (POW (props f)) (R f1 f2)) r w
    ==> ((!n. ?a. (a, r.E (n, R f1 f2)) ∈
              d_conj (trans (POW (props f)) f2) {(POW (props f), {R f1 f2})}
         ∧ at w n ∈ a) \/
        (?n a. (a, r.E (n, R f1 f2)) ∈ trans (POW (props f)) (CONJ f1 f2)
         ∧ at w n ∈ a))``,
  rpt strip_tac >> Cases_on `!i. R f1 f2 ∈ r.V i`
    >- (disj1_tac >> rpt strip_tac
        >> fs[runForAA_def, validAARunFor_def, ltl2vwaa_free_alph_def]
        >> `R f1 f2 ∈ r.V n` by metis_tac[]
        >> `∃a. (a,r.E (n,R f1 f2)) ∈ trans (POW (props f)) (R f1 f2) ∧ at w n ∈ a`
           by metis_tac[]
        >> qexists_tac `a` >> fs[]
        >> fs[trans_def]
        >> `R f1 f2 ∈ r.V (n+1)` by metis_tac[]
        >> `((n + 1) = 0) ∨ ∃q'. (R f1 f2) ∈ r.E ((n + 1) − 1,q') ∧ q' ∈ r.V ((n + 1) − 1)`
           by metis_tac[] >> fs[]
        >> `q' = R f1 f2` by (
            `q' ∈ tempSubForms (R f1 f2)` by metis_tac[SUBSET_DEF]
           >> `∃a. (a,r.E (n,q')) ∈ trans (POW (props f)) q' ∧ at w n ∈ a`
              by metis_tac[]
           >> `(R f1 f2,q') ∈ TSF` by metis_tac[TRANS_REACHES_SUBFORMS]
           >> metis_tac[TSF_def,IN_DEF,TSF_ANTISYM_LEMM]
         )
        >> `(a,r.E (n,R f1 f2)) ∈
           d_conj (trans (POW (props f)) f2) (trans (POW (props f)) f1)
           ∪ d_conj (trans (POW (props f)) f2) {(POW (props f),{R f1 f2})}`
           by metis_tac[D_CONJ_UNION_DISTR]
        >> fs[IN_UNION] >> POP_ASSUM mp_tac >> simp[d_conj_def]
        >> rpt strip_tac
        >> (`!q. (q ∈ e1) ==> (q,f2) ∈ TSF` by metis_tac[TRANS_REACHES_SUBFORMS]
           >> `!q. (q ∈ e2) ==> (q,f1) ∈ TSF` by metis_tac[TRANS_REACHES_SUBFORMS]
           >> `R f1 f2 ∈ e1 \/ R f1 f2 ∈ e2` by metis_tac[IN_UNION]
             >- (`R f1 f2 ∈ tempSubForms f2` by metis_tac[TSF_def, IN_DEF]
                 >> `R f1 f2 ∈ subForms f2` by metis_tac[TSF_IMPL_SF]
                 >> `f2 ∈ subForms (R f1 f2)` by fs[subForms_def, SUBFORMS_REFL]
                 >> `R f1 f2 = f2` by metis_tac[SF_ANTISYM_LEMM]
                 >> `(!f g. ~(g = R f g))` by (Induct_on `g` >> fs[])
                 >> metis_tac[]
                )
             >- (`R f1 f2 ∈ tempSubForms f1` by metis_tac[TSF_def, IN_DEF]
                 >> `R f1 f2 ∈ subForms f1` by metis_tac[TSF_IMPL_SF]
                 >> `f1 ∈ subForms (R f1 f2)` by fs[subForms_def, SUBFORMS_REFL]
                 >> `R f1 f2 = f1` by metis_tac[SF_ANTISYM_LEMM]
                 >> `(!f g. ~(g = R g f))` by (Induct_on `g` >> fs[])
                 >> metis_tac[]
                )
             )
       )
    >- (disj2_tac
        >> fs[runForAA_def, validAARunFor_def]
        >> qabbrev_tac `N = LEAST j. ~(R f1 f2 ∈ r.V j)`
        >> qexists_tac `N - 1`
        >> `R f1 f2 ∈ r.V 0`
            by (fs[ltl2vwaa_free_alph_def, initForms_def, tempDNF_def] >> metis_tac[IN_SING])
        >> `R f1 f2 ∈ r.V (N - 1)` by (
             qunabbrev_tac `N` >> numLib.LEAST_ELIM_TAC
             >> rpt strip_tac
                >- metis_tac[]
                >- (`~(n = 0)` by metis_tac[]
                    >> `n - 1 < n` by simp[]
                    >> metis_tac[])
         )
        >> fs[ltl2vwaa_free_alph_def]
        >> `∃a. (a,r.E (N-1,(R f1 f2))) ∈ trans (POW (props f)) (R f1 f2) ∧ at w (N-1) ∈ a`
            by fs[]
        >> qexists_tac `a` >> fs[]
        >> fs[trans_def]
        >> `(a,r.E (N -1,R f1 f2)) ∈
            d_conj (trans (POW (props f)) f2) (trans (POW (props f)) f1)
          ∪ d_conj (trans (POW (props f)) f2) {(POW (props f),{R f1 f2})}`
          by metis_tac[D_CONJ_UNION_DISTR]
        >> fs[IN_UNION]
         >- (fs[d_conj_def]>> metis_tac[UNION_COMM, INTER_COMM])
         >- (fs[d_conj_def]
             >> `r.E (N - 1, R f1 f2) ⊆ r.V (N - 1 + 1)` by metis_tac[]
             >> fs[]
             >> `~(R f1 f2 ∈ r.V N)` by (
                  qunabbrev_tac `N`
                  >> numLib.LEAST_ELIM_TAC
                  >> rpt strip_tac >> fs[]
                  >> metis_tac[])
             >> `~(N = 0)` by metis_tac[]
             >> `N - 1 + 1 = N` by simp[]
             >> `R f1 f2 ∈ r.V N` by metis_tac[IN_UNION,SUBSET_DEF,IN_SING]
            )
       )
  );

val SUBFORM_LEMMA = store_thm
  ("SUBFORM_LEMMA",
   ``!f. (!g. g ∈ subForms f ==>
         ({w | MODELS w g /\ (word_range w ⊆ POW (props f))} =
          alterA_lang (ltl2vwaa_free_alph (POW (props f)) g))) ==>
                      (ltl_lang f = alterA_lang (ltl2vwaa f))``,
   rpt strip_tac >> `f ∈ (subForms f)` by metis_tac[SUBFORMS_REFL]
    >> `({w | MODELS w f /\ (word_range w ⊆ POW (props f)) }
         = alterA_lang (ltl2vwaa_free_alph (POW (props f)) f))`
        by metis_tac[]
    >> metis_tac[ltl_lang_def, ltl2vwaa_def]
  );

val LTL2WAA_ISCORRECT = store_thm
  ("LTL2WAA_ISCORRECT",
   ``!f. (ltl_lang f = alterA_lang (ltl2vwaa f))``,
   strip_tac >>
   `(!g. (g ∈ subForms f) ==>
        ({w | MODELS w g /\ (word_range w ⊆ POW (props f))} =
         alterA_lang (ltl2vwaa_free_alph (POW (props f)) g)))`
     suffices_by metis_tac[SUBFORM_LEMMA]
   >> `!g. (g ∈ subForms f) ==>
       (({w | MODELS w g ∧ word_range w ⊆ POW (props f)}
             ⊆ alterA_lang (ltl2vwaa_free_alph (POW (props f)) g))
        /\ (alterA_lang (ltl2vwaa_free_alph (POW (props f)) g)
            ⊆ {w | MODELS w g ∧ word_range w ⊆ POW (props f)}))`
     suffices_by rw[SET_EQ_SUBSET]
   >> Induct_on `g` >> rpt strip_tac >> simp[MODELS_def]
     >- (fs[alterA_lang_def, ltl2vwaa_free_alph_def, SUBSET_DEF]
         >> rpt strip_tac
         >> qexists_tac `ALTERA_RUN (\i. if i=0 then {VAR a} else {}) (\_. {})`
         >> simp[runForAA_def, validAARunFor_def, acceptingAARun_def]
         >> rpt strip_tac
         >> simp[initForms_def, tempDNF_def, trans_def]
         >> Cases_on `i=0`
         >> fs[SUBSET_DEF, tempSubForms_def, infBranchOf_def]
         >> qexists_tac `char (POW (props f)) a` >> rpt strip_tac
         >> fs[char_def, trans_def,POW_DEF, SUBSET_DEF] >> rpt strip_tac
         >> fs[word_range_def]
         >> `∀y. (y ∈ at x 0) ⇒ (y ∈ props f)` by metis_tac[]
         >> metis_tac[]
        )
     >- (fs[alterA_lang_def, ltl2vwaa_free_alph_def, SUBSET_DEF]
         >> rpt strip_tac
         >> fs[runForAA_def, validAARunFor_def, acceptingAARun_def, tempSubForms_def]
         >> fs[SUBSET_DEF,initForms_def]
         >> `VAR a ∈ run.V 0` by fs[tempDNF_def]
         >> `∃a'. ((a',run.E (0,VAR a)) ∈ trans (POW (props f)) (VAR a))
                         ∧ (at x 0 ∈ a')` by metis_tac[]
         >> fs[trans_def, char_def]
         >> `(at x 0) ∈ { a' | (a' ∈ POW (props f)) ∧ (a ∈ a')}` by rw[]
         >> fs[]
        )
     >- (fs[alterA_lang_def, ltl2vwaa_free_alph_def, SUBSET_DEF]
         >> rpt strip_tac
         >> qexists_tac `ALTERA_RUN (\i. if i=0 then {N_VAR a} else {}) (\_. {})`
         >> simp[runForAA_def, validAARunFor_def, acceptingAARun_def]
         >> rpt strip_tac
         >> simp[initForms_def, tempDNF_def, trans_def]
         >> Cases_on `i=0`
         >> fs[SUBSET_DEF, tempSubForms_def, infBranchOf_def]
         >> qexists_tac `(POW (props f)) DIFF (char (POW (props f)) a)`
         >> rpt strip_tac
         >> fs[char_def, trans_def,POW_DEF, SUBSET_DEF] >> rpt strip_tac
         >> fs[word_range_def]
         >> `∀y. (y ∈ at x 0) ⇒ (y ∈ props f)` by metis_tac[]
         >> metis_tac[]
        )
     >- (fs[alterA_lang_def, ltl2vwaa_free_alph_def, SUBSET_DEF]
         >> rpt strip_tac
         >> fs[runForAA_def, validAARunFor_def, acceptingAARun_def, tempSubForms_def]
         >> fs[SUBSET_DEF,initForms_def]
         >> `N_VAR a ∈ run.V 0` by fs[tempDNF_def]
         >> `∃a'. ((a',run.E (0,N_VAR a)) ∈ trans (POW (props f)) (N_VAR a))
                         ∧ (at x 0 ∈ a')` by metis_tac[]
         >> fs[trans_def, char_def, DIFF_DEF]
         >> `(at x 0) ∈ { x | (x ∈ POW (props f))
            ∧ (~(x ∈ POW (props f)) \/ ~(a ∈ x))}` by rw[]
         >> fs[] >> fs[]
        )
     >- (`subForms (DISJ g g') = {DISJ g g'} ∪ (subForms g) ∪ (subForms g')`
           by rw[subForms_def]
         >> fs[UNION_DEF]
         >> `g ∈ subForms (DISJ g g')` by simp[SUBFORMS_REFL]
         >> `g' ∈ subForms (DISJ g g')` by simp[SUBFORMS_REFL]
         >> `g ∈ subForms f` by metis_tac[SUBFORMS_TRANS, subForms_def]
         >> `g' ∈ subForms f` by metis_tac[SUBFORMS_TRANS, subForms_def]
         >> dsimp[]
         >> `{w | MODELS w g ∧ word_range w ⊆ POW (props f)}
                ⊆ alterA_lang (ltl2vwaa_free_alph (POW (props f)) g)` by metis_tac[]
         >> `{w | MODELS w g' ∧ word_range w ⊆ POW (props f)}
                ⊆ alterA_lang (ltl2vwaa_free_alph (POW (props f)) g')` by metis_tac[]
         >> fs[alterA_lang_def, SUBSET_DEF] >> rpt strip_tac
           >- (`∃run.
                 runForAA (ltl2vwaa_free_alph (POW (props f)) g) run x ∧
                   ∀x'. x' ∈ word_range x
                   ==> x' ∈ (ltl2vwaa_free_alph (POW (props f)) g).alphabet`
                by metis_tac[]
               >> qexists_tac `run` >> rpt strip_tac >> fs[]
                  >- metis_tac[RUN_FOR_DISJ_LEMM]
                  >- fs[ltl2vwaa_free_alph_def]
              )
           >- (`∃run.
                  runForAA (ltl2vwaa_free_alph (POW (props f)) g') run x ∧
                    ∀x'. x' ∈ word_range x
                      ==> x' ∈ (ltl2vwaa_free_alph (POW (props f)) g').alphabet`
               by metis_tac[]
              >> qexists_tac `run` >> rpt strip_tac >> fs[]
                >- metis_tac[RUN_FOR_DISJ_LEMM]
                >- fs[ltl2vwaa_free_alph_def]
              )
        )
     >- (`subForms (DISJ g g') = {DISJ g g'} ∪ (subForms g) ∪ (subForms g')`
             by rw[subForms_def]
          >> fs[UNION_DEF]
          >> `g ∈ subForms (DISJ g g')` by simp[SUBFORMS_REFL]
          >> `g' ∈ subForms (DISJ g g')` by simp[SUBFORMS_REFL]
          >> `g ∈ subForms f` by metis_tac[SUBFORMS_TRANS, subForms_def]
          >> `g' ∈ subForms f` by metis_tac[SUBFORMS_TRANS, subForms_def]
          >> dsimp[]
          >> `{w | MODELS w g ∧ word_range w ⊆ POW (props f)}
                ⊆ alterA_lang (ltl2vwaa_free_alph (POW (props f)) g)` by metis_tac[]
          >> `{w | MODELS w g' ∧ word_range w ⊆ POW (props f)}
                ⊆ alterA_lang (ltl2vwaa_free_alph (POW (props f)) g')` by metis_tac[]
          >> fs[alterA_lang_def, SUBSET_DEF] >> rpt strip_tac
          >> `runForAA (ltl2vwaa_free_alph (POW (props f)) g) run x ∨
                runForAA (ltl2vwaa_free_alph (POW (props f)) g') run x`
              by metis_tac[RUN_FOR_DISJ_LEMM2]
          >- (`(∃run. runForAA (ltl2vwaa_free_alph (POW (props f)) g) run x
                ∧ ∀x'.
                ((x' ∈ word_range x) ⇒
                 (x' ∈ (ltl2vwaa_free_alph (POW (props f)) g).alphabet))) ⇒
                     MODELS x g ∧ ∀x'. (x' ∈ word_range x) ⇒ (x' ∈ POW (props f))`
                by metis_tac[]
              >> `(∃run.
                     runForAA (ltl2vwaa_free_alph (POW (props f)) g) run x ∧
                     ∀x'.
                       x' ∈ word_range x ⇒
                       x' ∈ (ltl2vwaa_free_alph (POW (props f)) g).alphabet)`
                   suffices_by metis_tac[]
              >> qexists_tac `run` >> fs[ltl2vwaa_free_alph_def])
          >- (`(∃run. runForAA (ltl2vwaa_free_alph (POW (props f)) g') run x
                 ∧ ∀x'.
                   ((x' ∈ word_range x) ⇒
                   (x' ∈ (ltl2vwaa_free_alph (POW (props f)) g').alphabet))) ⇒
                      MODELS x g' ∧ ∀x'. (x' ∈ word_range x) ⇒ (x' ∈ POW (props f))`
                 by metis_tac[]
              >> `(∃run.
                     runForAA (ltl2vwaa_free_alph (POW (props f)) g') run x ∧
                     ∀x'.
                       x' ∈ word_range x ⇒
                       x' ∈ (ltl2vwaa_free_alph (POW (props f)) g').alphabet)`
                 suffices_by metis_tac[]
              >> qexists_tac `run` >> fs[ltl2vwaa_free_alph_def])
        )
     >- (`subForms (CONJ g g') = {CONJ g g'} ∪ (subForms g) ∪ (subForms g')`
           by rw[subForms_def]
         >> fs[UNION_DEF]
         >> `g ∈ subForms (CONJ g g')` by simp[SUBFORMS_REFL]
         >> `g' ∈ subForms (CONJ g g')` by simp[SUBFORMS_REFL]
         >> `g ∈ subForms f` by metis_tac[SUBFORMS_TRANS, subForms_def]
         >> `g' ∈ subForms f` by metis_tac[SUBFORMS_TRANS, subForms_def]
         >> fs[SUBSET_DEF] >> rpt strip_tac >> fs[alterA_lang_def]
         >> `∃run.
               runForAA (ltl2vwaa_free_alph (POW (props f)) g) run x
             ∧ word_range x ⊆ (ltl2vwaa_free_alph (POW (props f)) g).alphabet`
            by metis_tac[]
         >> `∃run.
               runForAA (ltl2vwaa_free_alph (POW (props f)) g') run x
             ∧ word_range x ⊆ (ltl2vwaa_free_alph (POW (props f)) g').alphabet`
            by metis_tac[]
         >> `∃r. runForAA (ltl2vwaa_free_alph (POW (props f)) (CONJ g g')) r x`
             by metis_tac[RUN_FOR_CONJ_LEMM]
         >> qexists_tac `r` >> rpt strip_tac >> fs[]
         >> fs[ltl2vwaa_free_alph_def]
        )
     >- (`subForms (CONJ g g') = {CONJ g g'} ∪ (subForms g) ∪ (subForms g')`
           by rw[subForms_def]
         >> fs[UNION_DEF]
         >> `g ∈ subForms (CONJ g g')` by simp[SUBFORMS_REFL]
         >> `g' ∈ subForms (CONJ g g')` by simp[SUBFORMS_REFL]
         >> `g ∈ subForms f` by metis_tac[SUBFORMS_TRANS, subForms_def]
         >> `g' ∈ subForms f` by metis_tac[SUBFORMS_TRANS, subForms_def]
         >> fs[SUBSET_DEF] >> rpt strip_tac >> fs[alterA_lang_def]
           >- (`∃r1. runForAA (ltl2vwaa_free_alph (POW (props f)) g) r1 x`
                 by metis_tac[RUN_FOR_CONJ_LEMM2_UNION]
               >> `word_range x ⊆
                    (ltl2vwaa_free_alph (POW (props f)) g).alphabet`
                   suffices_by metis_tac[]
               >> fs[SUBSET_DEF, ltl2vwaa_free_alph_def])
           >- (`∃r1. runForAA (ltl2vwaa_free_alph (POW (props f)) g') r1 x`
                by metis_tac[RUN_FOR_CONJ_LEMM2_UNION]
               >> `word_range x ⊆
                      (ltl2vwaa_free_alph (POW (props f)) g').alphabet`
                   suffices_by metis_tac[]
               >> fs[SUBSET_DEF, ltl2vwaa_free_alph_def])
           >- (fs[ltl2vwaa_free_alph_def, word_range_def, SUBSET_DEF]
               >> metis_tac[]
              )
        )
     >- (`subForms (X g) = {X g} ∪ (subForms g)`
           by rw[subForms_def]
         >> fs[UNION_DEF]
         >> `g ∈ subForms (X g)` by simp[SUBFORMS_REFL]
         >> `g ∈ subForms f` by metis_tac[SUBFORMS_TRANS, subForms_def]
         >> fs[SUBSET_DEF] >> rpt strip_tac >> fs[alterA_lang_def]
         >> `word_range (suff x 1) ⊆ word_range x` by metis_tac[WORD_RANGE_SUFF_LEMM]
         >> `word_range (suff x 1) ⊆ POW (props f)` by metis_tac[SUBSET_TRANS, SUBSET_DEF]
         >> `?run. runForAA (ltl2vwaa_free_alph (POW (props f)) g) run (suff x 1)`
            by metis_tac[WORD_RANGE_SUFF_LEMM, SUBSET_DEF]
         >> `∃r'. runForAA (ltl2vwaa_free_alph (POW (props f)) (X g)) r' x`
            by metis_tac[RUN_FOR_X_LEMM, SUBSET_DEF]
         >> qexists_tac `r'` >> fs[ltl2vwaa_free_alph_def] >> metis_tac[SUBSET_DEF]
        )
     >- (`subForms (X g) = {X g} ∪ (subForms g)`
          by rw[subForms_def]
         >> fs[UNION_DEF]
         >> `g ∈ subForms (X g)` by simp[SUBFORMS_REFL]
         >> `g ∈ subForms f` by metis_tac[SUBFORMS_TRANS, subForms_def]
         >> fs[SUBSET_DEF] >> rpt strip_tac >> fs[alterA_lang_def]
           >- (`∃run. runForAA (ltl2vwaa_free_alph (POW (props f)) g) run (suff x 1)`
               by metis_tac[RUN_FOR_X_LEMM2]
               >> `word_range (suff x 1) ⊆ word_range x` by metis_tac[WORD_RANGE_SUFF_LEMM]
               >> `?run. runForAA (ltl2vwaa_free_alph (POW (props f)) g) run (suff x 1) ∧
                   word_range (suff x 1) ⊆ (ltl2vwaa_free_alph (POW (props f)) g).alphabet`
                   suffices_by metis_tac[]
               >> qexists_tac `run'` >> fs[ltl2vwaa_free_alph_def]
               >> metis_tac[SUBSET_TRANS])
           >- (fs[ltl2vwaa_free_alph_def, SUBSET_DEF])
        )
     >- (`{w |
           (∃n. MODELS (suff w n) g' ∧ ∀i. i < n ⇒ MODELS (suff w i) g)
           ∧ word_range w ⊆ POW (props f) }
           ⊆ alterA_lang
          (ltl2vwaa_free_alph (POW (props f))
                             (DISJ g' (CONJ g (X (U g g')))))`
           suffices_by metis_tac[U_AUTO_CHARACTERISATION]
         >> simp[SUBSET_DEF] >> rpt strip_tac
         >> `subForms (U g g') = {U g g'} ∪ (subForms g) ∪ (subForms g')`
             by rw[subForms_def]
         >> fs[UNION_DEF]
         >> `g ∈ subForms (U g g')` by simp[SUBFORMS_REFL]
         >> `g' ∈ subForms (U g g')` by simp[SUBFORMS_REFL]
         >> `g ∈ subForms f` by metis_tac[SUBFORMS_TRANS, subForms_def]
         >> `g' ∈ subForms f` by metis_tac[SUBFORMS_TRANS, subForms_def]
         >> `suff x 0 = x` by
                   (Cases_on `x` >> fs[suff_def] >> metis_tac[])
         >> Cases_on `n = 0`
          >- (`MODELS x g'` by metis_tac[]
              >> fs[SUBSET_DEF, alterA_lang_def]
              >> `?run.
                    runForAA (ltl2vwaa_free_alph (POW (props f)) g')
                           run x`
                   by metis_tac[word_range_def]
              >> qexists_tac `run`
              >> strip_tac
                >- metis_tac[RUN_FOR_DISJ_LEMM]
                >- fs[ltl2vwaa_free_alph_def]
             )
          >- (`!j. suff x (n - j) ∈
                   alterA_lang (ltl2vwaa_free_alph (POW (props f))
                              (DISJ g' (CONJ g (X (U g g')))))`
                 suffices_by (`n - n = 0` by simp[]
                               >> metis_tac[])
              >> Induct_on `j`
               >- (fs[alterA_lang_def]
                   >> `word_range (suff x n) ⊆ word_range x`
                       by metis_tac[WORD_RANGE_SUFF_LEMM]
                   >> fs[SUBSET_DEF]
                   >> `∃run.
                        runForAA (ltl2vwaa_free_alph (POW (props f)) g')
                               run
                               (suff x n)
                     ∧ word_range (suff x n)
                       ⊆ (ltl2vwaa_free_alph (POW (props f)) g').alphabet`
                      by metis_tac[SUBSET_DEF]
                   >> qexists_tac `run` >> rpt strip_tac
                    >- metis_tac[RUN_FOR_DISJ_LEMM]
                    >- fs[ltl2vwaa_free_alph_def]
                  )
               >- (Cases_on `n <= j`
                >- (`n - j = 0` by simp[]
                    >> `n - SUC j = 0` by simp[]
                    >> rw[] >> metis_tac[]
                   )
                >- (`suff x (n − j) ∈
                       alterA_lang
                       (ltl2vwaa_free_alph (POW (props f)) (U g g'))`
                     by metis_tac[U_AUTO_CHARACTERISATION]
                   >> POP_ASSUM mp_tac >> simp[alterA_lang_def]
                   >> rpt strip_tac
                   >> `suff (suff x (n - SUC j)) 1 = suff x (n - j)`
                        by (Cases_on `x` >> fs[suff_def]
                           >> simp[] >> rw[SUC_ONE_ADD])
                   >> `word_range (suff x (n − SUC j))
                         ⊆ word_range x`
                       by metis_tac[WORD_RANGE_SUFF_LEMM]
                   >> `∃r'.
                       runForAA
                       (ltl2vwaa_free_alph (POW (props f)) (X (U g g')))
                       r' (suff x (n - SUC j))`
                         by metis_tac[RUN_FOR_X_LEMM, SUBSET_DEF]
                   >> `n - SUC j < n` by simp[]
                   >> `MODELS (suff x (n - SUC j)) g` by fs[]
                   >> `∃r'.
                        runForAA
                        (ltl2vwaa_free_alph (POW (props f)) g)
                        r' (suff x (n - SUC j))` by
                           (fs[alterA_lang_def, SUBSET_DEF]
                            >> metis_tac[])
                   >> `∃r.
                        runForAA
                        (ltl2vwaa_free_alph (POW (props f))
                            (CONJ g (X (U g g'))))
                        r (suff x (n - SUC j))` by metis_tac[RUN_FOR_CONJ_LEMM]
                   >> qexists_tac `r`
                   >> rpt strip_tac
                     >- metis_tac[RUN_FOR_DISJ_LEMM]
                     >- (fs[ltl2vwaa_free_alph_def] >> metis_tac[SUBSET_DEF])
                   )
                  )
             )
        )
     >- (`subForms (U g g') = {U g g'} ∪ (subForms g) ∪ (subForms g')`
            by rw[subForms_def]
         >> fs[UNION_DEF]
         >> `g ∈ subForms (U g g')` by simp[SUBFORMS_REFL]
         >> `g' ∈ subForms (U g g')` by simp[SUBFORMS_REFL]
         >> `g ∈ subForms f` by metis_tac[SUBFORMS_TRANS, subForms_def]
         >> `g' ∈ subForms f` by metis_tac[SUBFORMS_TRANS, subForms_def]
         >> simp[SUBSET_DEF, alterA_lang_def] >> rpt strip_tac
          >- (imp_res_tac EVTL_F2_RUN_LEMM
               >> qexists_tac `n` >> strip_tac
                >- (`word_range (suff x n) ⊆ POW (props f)` by (
                       fs[ltl2vwaa_free_alph_def]
                     >> `word_range x ⊆ POW (props f)`
                       suffices_by metis_tac[WORD_RANGE_SUFF_LEMM,SUBSET_TRANS]
                     >> metis_tac[SUBSET_DEF]
                   )
                  >> fs[SUBSET_DEF, alterA_lang_def, ltl2vwaa_free_alph_def] >> metis_tac[]
                   )
                >- (rpt strip_tac
                   >> `∃r'. runForAA (ltl2vwaa_free_alph (POW (props f)) g) r' (suff x i)`
                      by fs[]
                   >> `word_range (suff x i) ⊆ POW (props f)` by (
                         fs[ltl2vwaa_free_alph_def]
                         >> `word_range x ⊆ POW (props f)`
                             suffices_by metis_tac[WORD_RANGE_SUFF_LEMM,SUBSET_TRANS]
                         >> metis_tac[SUBSET_DEF]
                     )
                   >> fs[SUBSET_DEF, alterA_lang_def, ltl2vwaa_free_alph_def] >> metis_tac[]
                   )
             )
          >- fs[ltl2vwaa_free_alph_def]
        )
     >- (`subForms (R g g') = {R g g'} ∪ (subForms g) ∪ (subForms g')`
           by rw[subForms_def]
          >> fs[UNION_DEF]
          >> `g ∈ subForms (R g g')` by simp[SUBFORMS_REFL]
          >> `g' ∈ subForms (R g g')` by simp[SUBFORMS_REFL]
          >> `g ∈ subForms f` by metis_tac[SUBFORMS_TRANS, subForms_def]
          >> `g' ∈ subForms f` by metis_tac[SUBFORMS_TRANS, subForms_def]
          >> simp[SUBSET_DEF] >> rpt strip_tac
          >> `(∀n. MODELS (suff x n) g') ∨
              ∃n. MODELS (suff x n) g ∧ ∀i. i <= n ⇒ MODELS (suff x i) g'`
             by metis_tac[R_COND_LEMM]
            >- (fs[alterA_lang_def]
                >> `!n. ?r. runForAA (ltl2vwaa_free_alph (POW (props f)) g') r (suff x n)`
                by (rpt strip_tac >> `MODELS (suff x n) g'` by metis_tac[]
                    >> fs[alterA_lang_def, SUBSET_DEF]
                    >> metis_tac[WORD_RANGE_SUFF_LEMM, SUBSET_DEF]
                   )
                >> imp_res_tac ALWAYS_RUN
                >> `word_range x ⊆ POW (props f)` by metis_tac[SUBSET_DEF]
                >> fs[]
                >> `∃r. runForAA (ltl2vwaa_free_alph (POW (props f)) (R g g')) r x`
                    by fs[]
                >> qexists_tac `r`
                >> strip_tac >> fs[]
                >> fs[ltl2vwaa_free_alph_def]
               )
            >- (`x ∈ alterA_lang (ltl2vwaa_free_alph (POW (props f))
                                                  (CONJ g' (DISJ g (X (R g g')))))`
                 suffices_by metis_tac[R_AUTO_CHARACTERISATION]
                >> fs[alterA_lang_def]
                >> rw[LEFT_EXISTS_AND_THM]
                 >- (`suff x 0 = x` by
                      (Cases_on `x` >> fs[suff_def] >> metis_tac[])
                    >> `!j.
                       ∃run. runForAA
                       (ltl2vwaa_free_alph (POW (props f)) (CONJ g' (DISJ g (X (R g g')))))
                       run (suff x (n - j))`
                       suffices_by metis_tac[DECIDE ``n - n = 0``]
                    >> Induct_on `j`
                      >- (fs[SUBSET_DEF]
                          >> `word_range (suff x n) ⊆ POW (props f)`
                              by metis_tac[WORD_RANGE_SUFF_LEMM, SUBSET_DEF]
                          >> `∃run.
                             runForAA (ltl2vwaa_free_alph (POW (props f)) g) run (suff x n)`
                             by metis_tac[SUBSET_DEF]
                          >> `∃run.
                             runForAA (ltl2vwaa_free_alph (POW (props f)) g') run (suff x n)`
                             by metis_tac[SUBSET_DEF, DECIDE ``n <= n``]
                          >> `∃r.
                         runForAA (ltl2vwaa_free_alph (POW (props f)) (CONJ g' g)) r
                                      (suff x n)`
                             by metis_tac[RUN_FOR_CONJ_LEMM]
                          >> metis_tac[CONJ_DISJ_DISTRIB]
                         )
                      >- (`∃run.
                            runForAA
                            (ltl2vwaa_free_alph (POW (props f))
                                  (R g g')) run (suff x (n − j))` by (
                          `alterA_lang (ltl2vwaa_free_alph (POW (props f)) (R g g')) =
                          alterA_lang
                              (ltl2vwaa_free_alph (POW (props f))
                                                 (CONJ g' (DISJ g (X (R g g')))))`
                              by metis_tac[R_AUTO_CHARACTERISATION]
                           >> fs[alterA_lang_def, SUBSET_DEF, SET_EQ_SUBSET]
                           >> first_x_assum (qspec_then `suff x (n - j)` mp_tac)
                           >> first_x_assum (qspec_then `suff x (n - j)` mp_tac)
                           >> `word_range (suff x (n - j)) ⊆ POW (props f)`
                              by metis_tac[WORD_RANGE_SUFF_LEMM, SUBSET_DEF]
                           >> rpt strip_tac
                           >> fs[ltl2vwaa_free_alph_def] >> metis_tac[SUBSET_DEF]
                            )
                         >> Cases_on `n <= j`
                           >- (`n - j = 0` by simp[]
                                >> `n - SUC j = 0` by simp[]
                                >> rw[] >> metis_tac[]
                              )
                           >- (`suff (suff x (n - SUC j)) 1 = suff x (n - j)`
                                by (Cases_on `x` >> fs[suff_def]
                               >> simp[] >> rw[SUC_ONE_ADD])
                               >> `word_range (suff x (n − SUC j))
                                             ⊆ word_range x`
                                   by metis_tac[WORD_RANGE_SUFF_LEMM]
                               >> `∃r'.
                                    runForAA
                                    (ltl2vwaa_free_alph (POW (props f)) (X (R g g')))
                                    r' (suff x (n - SUC j))`
                                   by metis_tac[RUN_FOR_X_LEMM, SUBSET_DEF]
                               >> `n - SUC j < n` by simp[]
                               >> `MODELS (suff x (n - SUC j)) g'` by fs[]
                               >> `∃r'.
                                     runForAA
                                     (ltl2vwaa_free_alph (POW (props f)) g')
                                     r' (suff x (n - SUC j))` by
                                  (fs[alterA_lang_def, SUBSET_DEF]
                                      >> metis_tac[])
                               >> `∃r.
                                     runForAA
                                     (ltl2vwaa_free_alph (POW (props f))
                                                    (CONJ g' (X (R g g'))))
                                     r (suff x (n - SUC j))` by metis_tac[RUN_FOR_CONJ_LEMM]
                               >> metis_tac[CONJ_DISJ_DISTRIB]
                              )
                           )
                    )
                 >- (fs[word_range_def, SUBSET_DEF, ltl2vwaa_free_alph_def])
               )
        )
     >- (`subForms (R g g') = {R g g'} ∪ (subForms g) ∪ (subForms g')`
            by rw[subForms_def]
         >> fs[UNION_DEF]
         >> `g ∈ subForms (R g g')` by simp[SUBFORMS_REFL]
         >> `g' ∈ subForms (R g g')` by simp[SUBFORMS_REFL]
         >> `g ∈ subForms f` by metis_tac[SUBFORMS_TRANS, subForms_def]
         >> `g' ∈ subForms f` by metis_tac[SUBFORMS_TRANS, subForms_def]
         >> simp[SUBSET_DEF, alterA_lang_def] >> rpt gen_tac
         >> strip_tac >> strip_tac
          >- (`(∀n. MODELS (suff x n) g') ∨
               ∃n. MODELS (suff x n) g ∧ ∀i. i ≤ n ⇒ MODELS (suff x i) g'`
               suffices_by metis_tac[R_COND_LEMM]
              >> imp_res_tac ALWAYS_F2_OR_EVTL_F1_R
               >- (disj1_tac >> strip_tac
                   >> first_x_assum (qspec_then `n` mp_tac)
                   >> strip_tac
                   >> `∃r'.
                        runForAA
                        (ltl2vwaa_free_alph (POW (props f)) (CONJ g' (X (R g g')))) r'
                        (suff x n)` by metis_tac[R_REPL_F1_LEMM]
                   >> `word_range (suff x n) ⊆ word_range x`
                         by metis_tac[WORD_RANGE_SUFF_LEMM]
                   >> `∃r1.
                        runForAA (ltl2vwaa_free_alph (POW (props f)) g') r1 (suff x n)`
                      by metis_tac[RUN_FOR_CONJ_LEMM2_UNION]
                   >> fs[alterA_lang_def, SUBSET_DEF]
                   >> fs[SUBSET_DEF, ltl2vwaa_free_alph_def]
                   >> metis_tac[]
                  )
               >- (disj2_tac
                  >> qabbrev_tac
                    `N = LEAST j. (?a.
                         (a,run.E (j,R g g')) ∈ trans (POW (props f)) (CONJ g g')
                         ∧ at x j ∈ a)`
                  >> `!i. i < N ==> (R g g' ∈ run.V i)` by (
                     Induct_on `i`
                      >- (strip_tac >> fs[runForAA_def,validAARunFor_def]
                          >> fs[ltl2vwaa_free_alph_def, initForms_def, tempDNF_def]
                         )
                      >- (strip_tac >> `R g g' ∈ run.V i` by fs[]
                         >> `~(?a.(a,run.E (i,R g g')) ∈ trans (POW (props f)) (CONJ g g')
                                                               ∧ at x i ∈ a)` by (
                            CCONTR_TAC >> fs[] >> `N <= i` suffices_by simp[]
                            >> qunabbrev_tac `N`
                            >> numLib.LEAST_ELIM_TAC >> rpt strip_tac
                              >- metis_tac[]
                              >- (CCONTR_TAC >> `i < n'` by simp[]
                                             >> metis_tac[])
                           )
                         >> fs[runForAA_def, validAARunFor_def, ltl2vwaa_free_alph_def]
                         >> `?a'. (a', run.E (i, R g g')) ∈ trans (POW (props f)) (R g g')
                                   ∧ at x i ∈ a'` by metis_tac[]
                         >> fs[trans_def]
                         >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
                         >> simp[D_CONJ_UNION_DISTR] >> rpt strip_tac
                                >- (fs[d_conj_def]
                                    >> first_x_assum (qspec_then `a'` mp_tac)
                                    >> metis_tac[UNION_COMM, INTER_COMM]
                                   )
                                >- (fs[d_conj_def]
                                    >> `e1' ∪ {R g g'} ⊆ run.V (i + 1)` by metis_tac[]
                                    >> `SUC i = i + 1` by simp[]
                                    >> metis_tac[IN_UNION,IN_SING,SUBSET_DEF]
                                   )
                             )
                         )
                  >> qexists_tac `N`
                  >> rpt strip_tac
                    >- (`?a.(a,run.E (N,R g g')) ∈ trans (POW (props f)) (CONJ g g')
                        ∧ at x N ∈ a` by (
                             qunabbrev_tac `N` >> numLib.LEAST_ELIM_TAC
                             >> rpt strip_tac
                               >- (metis_tac[])
                               >- metis_tac[]
                                )
                        >> `∃r'.
                           runForAA (ltl2vwaa_free_alph (POW (props f)) (CONJ g g'))
                           r' (suff x N)` by metis_tac[REPL_F2_LEMM,SUBSET_REFL]
                        >> ` ∃r1.
                           runForAA (ltl2vwaa_free_alph (POW (props f)) g) r1 (suff x N)`
                           by metis_tac[RUN_FOR_CONJ_LEMM2_UNION]
                        >> `word_range (suff x N) ⊆ word_range x`
                                   by metis_tac[WORD_RANGE_SUFF_LEMM]
                        >> fs[alterA_lang_def, SUBSET_DEF]
                        >> fs[SUBSET_DEF, ltl2vwaa_free_alph_def]
                        >> metis_tac[]
                       )
                    >- (Cases_on `i = N`
                        >- (`?a.(a,run.E (N,R g g')) ∈ trans (POW (props f)) (CONJ g g')
                             ∧ at x N ∈ a` by (
                                 qunabbrev_tac `N` >> numLib.LEAST_ELIM_TAC
                                 >> rpt strip_tac >> metis_tac[]
                                  )
                            >> `∃r'.
                                 runForAA (ltl2vwaa_free_alph (POW (props f)) (CONJ g g'))
                                 r' (suff x N)` by metis_tac[REPL_F2_LEMM,SUBSET_REFL]
                            >> ` ∃r1.
                                 runForAA (ltl2vwaa_free_alph (POW (props f)) g')
                                 r1 (suff x N)`
                                 by metis_tac[RUN_FOR_CONJ_LEMM2_UNION]
                            >> `word_range (suff x N) ⊆ word_range x`
                                 by metis_tac[WORD_RANGE_SUFF_LEMM]
                            >> fs[alterA_lang_def, SUBSET_DEF]
                            >> fs[SUBSET_DEF, ltl2vwaa_free_alph_def]
                            >> metis_tac[])
                        >- (`i < N` by simp[]
                            >> `~(?a.(a,run.E (i,R g g')) ∈ trans (POW (props f)) (CONJ g g')
                            ∧ at x i ∈ a)` by (
                               CCONTR_TAC >> fs[] >> `N <= i` suffices_by simp[]
                               >> qunabbrev_tac `N`
                               >> numLib.LEAST_ELIM_TAC >> rpt strip_tac
                                 >- (metis_tac[])
                                 >- (CCONTR_TAC >> `i < n'` by simp[]
                                    >> metis_tac[])
                                 )
                            >> `R g g' ∈ run.V i` by fs[]
                            >> imp_res_tac R_REPL_F1_LEMM
                            >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
                            >> RULE_ASSUM_TAC(
                                 SIMP_RULE
                           (srw_ss())[runForAA_def, validAARunFor_def, ltl2vwaa_free_alph_def]
                            )
                            >> rpt strip_tac
                            >> `?a. (a,run.E (i,R g g')) ∈ trans (POW (props f)) (R g g')
                                  ∧ at x i ∈ a` by metis_tac[]
                            >> fs[trans_def] >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
                            >> simp[D_CONJ_UNION_DISTR]
                            >> rpt strip_tac
                              >- (fs[d_conj_def]
                                  >> first_x_assum (qspec_then `a'` mp_tac)
                                  >> metis_tac[UNION_COMM, INTER_COMM])
                              >- (`∃r'.
                                    runForAA
                                    (ltl2vwaa_free_alph (POW (props f))
                                                       (CONJ g' (X (R g g')))) r'
                                    (suff x i)` by metis_tac[]
                                  >> `∃r1.
                                    runForAA (ltl2vwaa_free_alph (POW (props f)) g') r1
                                    (suff x i)` by metis_tac[RUN_FOR_CONJ_LEMM2_UNION]
                                  >> `word_range (suff x i) ⊆ word_range x`
                                      by metis_tac[WORD_RANGE_SUFF_LEMM]
                                  >> fs[alterA_lang_def, SUBSET_DEF]
                                  >> fs[SUBSET_DEF, ltl2vwaa_free_alph_def]
                                  >> metis_tac[]
                                 )
                           )
                       )
                  )
             )
          >- fs[ltl2vwaa_free_alph_def]
        )
  );

val _ = export_theory();
