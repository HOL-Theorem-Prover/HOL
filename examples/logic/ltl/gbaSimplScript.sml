open HolKernel Parse bossLib boolLib pairTheory pred_setTheory relationTheory set_relationTheory arithmeticTheory

open buechiATheory

val _ = new_theory "gbaSimpl"

(*
  Reducing the amount of transitions
*)

val trans_implies_def = Define`
  trans_implies accTrans q (a1,q1) (a2,q2)
      = (q1 = q2) ∧ a2 ⊆ a1
      ∧ !t. t ∈ accTrans ==> ((q,a2,q2) ∈ t ==> (q,a1,q1) ∈ t)`;

val TRANS_IMPLIES_PO = store_thm
  ("TRANS_IMPLIES_PO",
   ``!aT q d.
       partial_order (rrestrict (rel_to_reln (trans_implies aT q)) d) d``,
   fs[partial_order_def, rrestrict_def, rel_to_reln_def] >> rpt strip_tac
    >- (fs[domain_def,SUBSET_DEF] >> rpt strip_tac)
    >- (fs[range_def, SUBSET_DEF] >> rpt strip_tac)
    >- (fs[transitive_def,SUBSET_DEF] >> rpt strip_tac
        >> Cases_on `x` >> Cases_on `y` >> Cases_on `z` >> fs[trans_implies_def]
        >> metis_tac[SUBSET_TRANS])
    >- (fs[reflexive_def,SUBSET_DEF] >> rpt strip_tac >> Cases_on `x`
        >> fs[trans_implies_def])
    >- (fs[antisym_def,SUBSET_DEF] >> rpt strip_tac >> Cases_on `x`
        >> Cases_on `y` >> fs[trans_implies_def]
        >> metis_tac[SUBSET_ANTISYM]
       )
  );

val TRANS_IMPLIES_FINITE = store_thm
  ("TRANS_IMPLIES_FINITE",
  ``!aT q d. FINITE d ==>
     finite_prefixes (rrestrict (rel_to_reln (trans_implies aT q)) d) d``,
  fs[finite_prefixes_def, rrestrict_def, rel_to_reln_def] >> rpt strip_tac
  >> `FINITE {e' | e' ∈ (\x. trans_implies aT q x e) ∧ e' ∈ d }`
      suffices_by fs[IN_DEF]
  >> metis_tac[INTER_DEF,INTER_FINITE,INTER_COMM]
  );

val TRANS_IMPLIES_MIN = store_thm
  ("TRANS_IMPLIES_MIN",
  ``!aut q1 q2 w i a. FINITE aut.states ∧ FINITE aut.alphabet ∧ isValidGBA aut
          ∧ q1 ∈ aut.states ∧ (a,q2) ∈ aut.trans q1
          ==> let rel = rrestrict
                            (rel_to_reln (trans_implies aut.accTrans q1))
                            (aut.trans q1)
              in ?t. t ∈ minimal_elements (aut.trans q1) rel
                  ∧ (t,(a, q2)) ∈ rel``,
  rpt strip_tac >> simp[]
  >> qabbrev_tac `rel = rrestrict
                            (rel_to_reln (trans_implies aut.accTrans q1))
                            (aut.trans q1)`
  >> Cases_on `(a, q2) ∈ minimal_elements (aut.trans q1) rel`
   >- (qexists_tac `(a, q2)` >> fs[] >> qunabbrev_tac `rel`
       >> fs[rrestrict_def,rel_to_reln_def,trans_implies_def])
   >- (HO_MATCH_MP_TAC finite_prefix_po_has_minimal_path
       >> qexists_tac `aut.trans q1`
       >> `FINITE (aut.trans q1)` by (imp_res_tac GBA_FINITE_LEMM >> fs[])
       >> rpt strip_tac >> fs[] >> qunabbrev_tac `rel`
         >- metis_tac[TRANS_IMPLIES_PO]
         >- metis_tac[TRANS_IMPLIES_FINITE]
      )
  );

val removeImplied_def = Define`
  removeImplied accTrans trans q =
    (trans q) DIFF {t | ?t'. ~(t = t') ∧ t' ∈ (trans q)
                             ∧ trans_implies accTrans q t' t}`;

val reduceTransSimpl_def = Define`
  reduceTransSimpl (GBA s i t aT a) =
   GBA s i (removeImplied aT t)
    (IMAGE
         (\s. {(e,a,e') | (e,a,e') ∈ s ∧ (a,e') ∈ (removeImplied aT t) e })
         aT)
    a`;

val REDUCE_IS_VALID = store_thm
 ("REDUCE_IS_VALID",
  ``!aut. isValidGBA aut ==> isValidGBA (reduceTransSimpl aut)``,
  fs[isValidGBA_def] >> rpt strip_tac >> Cases_on `aut`
  >> fs[reduceTransSimpl_def] >> fs[removeImplied_def] >> metis_tac[]
 );

val REDUCE_IS_CORRECT = store_thm
  ("REDUCE_IS_CORRECT",
   ``!aut. FINITE aut.states ∧ FINITE aut.alphabet ∧ isValidGBA aut
             ==> (GBA_lang aut = GBA_lang (reduceTransSimpl aut))``,
   fs[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
   >> fs[GBA_lang_def, reduceTransSimpl_def]
    >- (rename [‘isGBARunFor aut r x’] >> qexists_tac `r`
        >> `word_range x ⊆ (reduceTransSimpl aut).alphabet`
             by (Cases_on `aut` >> fs[reduceTransSimpl_def])
        >> fs[isGBARunFor_def] >> Cases_on `r`
        >> rename [`GBA_RUN f`]
        >> `!i. f i ∈ aut.states` by metis_tac[GBA_RUN_LEMM]
        >> rpt strip_tac
         >- (fs[isValidGBARunFor_def] >> rpt strip_tac
             >> Cases_on `aut` >> fs[reduceTransSimpl_def]
             >> rename [`GBA states init trans aT alph`]
             >> imp_res_tac TRANS_IMPLIES_MIN >> fs[]
             >> `∃a. (a,f (i + 1)) ∈ trans (f i) ∧ at x i ∈ a` by fs[]
             >> first_x_assum (qspec_then `f (i+1)` mp_tac) >> rpt strip_tac
             >> first_x_assum (qspec_then `f i` mp_tac) >> rpt strip_tac
             >> first_x_assum (qspec_then `a` mp_tac) >> rpt strip_tac
             >> POP_ASSUM mp_tac >> simp[] >> rpt strip_tac >> Cases_on `t`
             >> rename[`(a_new,_) ∈ minimal_elements (trans (f i)) _`]
             >> qexists_tac `a_new` >> simp[removeImplied_def]
             >> fs[minimal_elements_def,rrestrict_def,rel_to_reln_def]
             >> fs[trans_implies_def] >> rw[] >> metis_tac[SUBSET_DEF]
             )
         >- (`!TT. TT ∈ (reduceTransSimpl aut).accTrans
              ==> (!i. ?a j. i <= j ∧ (f j, a, f (j+1)) ∈ TT
                ∧ (a, f (j+1)) ∈ (reduceTransSimpl aut).trans (f j)
                ∧ at x j ∈ a)` suffices_by metis_tac[GBA_ACC_LEMM]
             >> `!TT. TT ∈ aut.accTrans
                 ==> (!i. ?a j. i <= j ∧ (f j, a, f (j+1)) ∈ TT
                    ∧ (a, f (j+1)) ∈ aut.trans (f j)
                    ∧ at x j ∈ a)` by metis_tac[GBA_ACC_LEMM]
             >> rpt strip_tac
             >> rpt strip_tac >> Cases_on `aut` >> fs[reduceTransSimpl_def]
             >> rename [`GBA states init trans aT alph`, ‘s ∈ aT’]
             >> first_x_assum (qspec_then `s` mp_tac)
             >> simp[] >> rpt strip_tac
             >> first_x_assum (qspec_then `i` mp_tac) >> rpt strip_tac
             >> imp_res_tac TRANS_IMPLIES_MIN >> fs[]
             >> first_x_assum (qspec_then `f (j+1)` mp_tac) >> rpt strip_tac
             >> first_x_assum (qspec_then `f j` mp_tac) >> rpt strip_tac
             >> first_x_assum (qspec_then `a` mp_tac) >> rpt strip_tac
             >> POP_ASSUM mp_tac >> simp[] >> rpt strip_tac
             >> rename [‘(t, _, _) ∈ rrestrict (rel_to_reln _) _’]
             >> Cases_on `t` >> rename[`(a_new,r) ∈ minimal_elements _ _`]
             >> qexists_tac `a_new` >> qexists_tac `j` >> fs[removeImplied_def]
             >> rpt strip_tac >> fs[minimal_elements_def,rrestrict_def]
             >> fs[rel_to_reln_def,trans_implies_def]
              >- (first_x_assum (qspec_then `(a,f(j+1))` mp_tac) >> fs[]
                  >> rpt strip_tac >> metis_tac[])
              >- metis_tac[]
              >- metis_tac[]
              >- metis_tac[SUBSET_DEF]
              >- metis_tac[]
              >- metis_tac[SUBSET_DEF]
            )
       )
    >- (rename [‘isGBARunFor (reduceTransSimpl aut) r x’] >> qexists_tac `r`
        >> `word_range x ⊆ aut.alphabet`
           by (Cases_on `aut` >> fs[reduceTransSimpl_def])
        >> fs[isGBARunFor_def] >> rpt strip_tac
         >- (Cases_on `r` >> simp[isValidGBARunFor_def] >> rpt strip_tac
             >> Cases_on `aut` >> fs[reduceTransSimpl_def,isValidGBARunFor_def]
             >> first_x_assum (qspec_then `i` mp_tac) >> rpt strip_tac
             >> fs[removeImplied_def] >> metis_tac[]
            )
         >- (Cases_on `r`
             >> `!TT. TT ∈ (reduceTransSimpl aut).accTrans
              ==> (!i. ?a j. i <= j ∧ (f j, a, f (j+1)) ∈ TT
                     ∧ (a, f (j+1)) ∈ (reduceTransSimpl aut).trans (f j)
                     ∧ at x j ∈ a)` by metis_tac[GBA_ACC_LEMM]
             >> `!TT. TT ∈ aut.accTrans
                  ==> (!i. ?a j. i <= j ∧ (f j, a, f (j+1)) ∈ TT
                        ∧ (a, f (j+1)) ∈ aut.trans (f j)
                        ∧ at x j ∈ a)` suffices_by metis_tac[GBA_ACC_LEMM]
             >> rpt strip_tac
             >> qabbrev_tac
                 `realTrans = {(e,a,e') | (a,e') ∈
                                          (reduceTransSimpl aut).trans e }`
             >> first_x_assum (qspec_then `TT ∩ realTrans` mp_tac)
             >> Cases_on `aut` >> fs[reduceTransSimpl_def]
             >> qunabbrev_tac `realTrans`
             >> simp[] >> rpt strip_tac >> fs[]
             >> rename [‘GBA states init trans aT alph’,
                        ‘removeImplied aT trans’]
             >> `∀i.
                  ∃a j. i ≤ j ∧
                  ((f j,a,f (j + 1)) ∈ TT
                 ∧ (a,f (j + 1)) ∈ removeImplied aT trans (f j))
                 ∧ (a,f (j + 1)) ∈ removeImplied aT trans (f j) ∧ at x j ∈ a`
                by (
                  `∃s.
                    (TT ∩ {(e,a,e') | (a,e') ∈ removeImplied aT trans e} =
                     {(e,a,e') |
                        (e,a,e') ∈ s ∧ (a,e') ∈ removeImplied aT trans e}) ∧
                    s ∈ aT` suffices_by fs[]
                >> qexists_tac `TT` >> simp[SET_EQ_SUBSET,SUBSET_DEF]
                >> rpt strip_tac >> metis_tac[]
              )
             >> first_x_assum (qspec_then `i` mp_tac) >> rpt strip_tac
             >> fs[removeImplied_def] >> metis_tac[]
            )
       )
  );

(*
  Remove unreachable states
*)

val removeStatesSimpl_def = Define`
  removeStatesSimpl (GBA s i t aT alph) =
  GBA
      (s ∩ reachableFromSetGBA (GBA s i t aT alph) i)
      i
      (λq. if q ∈ (s ∩ reachableFromSetGBA (GBA s i t aT alph) i)
           then t q
           else {}
      )
      (IMAGE
           (\T. {(e,a,e') | (e,a,e') ∈ T
                          ∧  e ∈ (reachableFromSetGBA (GBA s i t aT alph) i)})
           aT)
      alph`;

val REDUCE_STATE_VALID = store_thm
  ("REDUCE_STATE_VALID",
   ``!aut. isValidGBA aut ==> isValidGBA (removeStatesSimpl aut)``,
   fs[isValidGBA_def] >> rpt strip_tac >> Cases_on `aut`
   >> fs[removeStatesSimpl_def,reachableFromSetGBA_def]
   >> fs[SUBSET_DEF] >> rpt strip_tac
    >- (simp[reachableFromGBA_def] >> metis_tac[RTC_REFL])
    >- metis_tac[]
    >- (rename [‘reachableFromGBA (GBA f f0 f1 f2 f3) x s’, ‘x ∈ f0’]
        >> qexists_tac `x` >> fs[reachableFromGBA_def]
        >> `stepGBA (GBA f f0 f1 f2 f3) s d` suffices_by metis_tac[RTC_CASES2]
        >> simp[stepGBA_def] >> metis_tac[])
    >- metis_tac[]
    >- metis_tac[]
    >- metis_tac[]
    >- metis_tac[]
  );

(* val REACHABLE_LEMM = store_thm *)
(*   ("REACHABLE_LEMM", *)
(*    ``!gba. isValidGBA gba ==> *)
(*       (!q. q ∈ gba.states ==>) *)
(* ) *)

val REDUCE_STATE_CORRECT = store_thm
  ("REDUCE_STATE_CORRECT",
   ``!aut. isValidGBA aut ==>
              (GBA_lang aut = GBA_lang (removeStatesSimpl aut))``,
   fs[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
   >> fs[GBA_lang_def, removeStatesSimpl_def]
   >- (qexists_tac `r` >> Cases_on `r` >> fs[isGBARunFor_def]
       >> `!i. f i ∈ reachableFromSetGBA aut aut.initial
            ∧  f i ∈ aut.states` by (
        Induct_on `i` >> fs[reachableFromSetGBA_def] >> rpt strip_tac
        >- (fs[isValidGBARunFor_def,reachableFromGBA_def]
              >> qexists_tac `f 0` >> metis_tac[RTC_REFL])
        >- (fs[isValidGBA_def,isValidGBARunFor_def]
              >> metis_tac[SUBSET_DEF])
        >- (fs[reachableFromGBA_def, isValidGBARunFor_def]
              >> rename[`init ∈ aut.initial`]
              >> qexists_tac `init` >> fs[]
              >> `(stepGBA aut) (f i) (f (SUC i))` suffices_by (
                 rpt strip_tac >> metis_tac[RTC_CASES2]
             )
             >> simp[stepGBA_def] >> metis_tac[SUC_ONE_ADD,ADD_COMM]
           )
        >- (fs[isValidGBARunFor_def,isValidGBA_def]
              >> metis_tac[SUBSET_DEF,SUC_ONE_ADD,ADD_COMM]
           )
        )
       >> `word_range x ⊆ (removeStatesSimpl aut).alphabet`
           by (Cases_on `aut` >> fs[removeStatesSimpl_def])
       >> rpt strip_tac >> fs[]
       >- (fs[isValidGBARunFor_def]
           >> Cases_on `aut` >> fs[removeStatesSimpl_def]
          )
       >- (`!T. T ∈ (removeStatesSimpl aut).accTrans
             ==> (!i. ?a j. i <= j ∧ (f j, a, f (j+1)) ∈ T
                  ∧ (a, f (j+1)) ∈ (removeStatesSimpl aut).trans (f j)
                  ∧ at x j ∈ a)` suffices_by metis_tac[GBA_ACC_LEMM]
           >> `!T. T ∈ aut.accTrans
             ==> (!i. ?a j. i <= j ∧ (f j, a, f (j+1)) ∈ T
                    ∧ (a, f (j+1)) ∈ aut.trans (f j)
                    ∧ at x j ∈ a)` by metis_tac[GBA_ACC_LEMM]
           >> rpt strip_tac >> Cases_on `aut`
           >> fs[removeStatesSimpl_def])
          )
    >- (`word_range x ⊆ aut.alphabet`
           by (Cases_on `aut` >> fs[removeStatesSimpl_def])
        >> qexists_tac `r` >> fs[isGBARunFor_def] >> rpt strip_tac
         >- (Cases_on `r` >> fs[isValidGBARunFor_def] >> rpt strip_tac
             >> Cases_on `aut` >> fs[removeStatesSimpl_def]
             >> metis_tac[MEMBER_NOT_EMPTY]
            )
         >- (Cases_on `r`
             >> `!i. f i ∈ reachableFromSetGBA aut aut.initial
                   ∧ f i ∈ aut.states` by (
                  Induct_on `i` >> fs[reachableFromSetGBA_def] >> rpt strip_tac
                   >- (fs[isValidGBARunFor_def,reachableFromGBA_def]
                       >> qexists_tac `f 0` >> Cases_on `aut`
                       >> fs[removeStatesSimpl_def]
                      )
                   >- (Cases_on `aut` >> fs[removeStatesSimpl_def]
                       >> fs[isValidGBARunFor_def,isValidGBA_def]
                       >> fs[SUBSET_DEF]
                      )
                   >- (fs[isValidGBARunFor_def,reachableFromGBA_def]
                       >> rename[`init ∈ aut.initial`]
                       >> qexists_tac `init` >> fs[]
                       >> `(stepGBA aut) (f i) (f (SUC i))` suffices_by (
                            rpt strip_tac >> metis_tac[RTC_CASES2]
                        )
                       >> Cases_on `aut` >> fs[removeStatesSimpl_def]
                       >> simp[stepGBA_def]
                       >> metis_tac[SUC_ONE_ADD,ADD_COMM,MEMBER_NOT_EMPTY]
                      )
                   >- (fs[isValidGBARunFor_def,isValidGBA_def]
                       >> Cases_on `aut` >> fs[removeStatesSimpl_def]
                       >> metis_tac[SUBSET_DEF,SUC_ONE_ADD,ADD_COMM,
                                   MEMBER_NOT_EMPTY]
                      )
              )
             >> `!T. T ∈ (removeStatesSimpl aut).accTrans
                  ==> (!i. ?a j. i <= j ∧ (f j, a, f (j+1)) ∈ T
                        ∧ (a, f (j+1)) ∈ (removeStatesSimpl aut).trans (f j)
                        ∧ at x j ∈ a)` by metis_tac[GBA_ACC_LEMM]
             >> `!T. T ∈ aut.accTrans
                  ==> (!i. ?a j. i <= j ∧ (f j, a, f (j+1)) ∈ T
                         ∧ (a, f (j+1)) ∈ aut.trans (f j)
                         ∧ at x j ∈ a)` suffices_by metis_tac[GBA_ACC_LEMM]
             >> rpt strip_tac >> fs[]
             >> qabbrev_tac `realTrans =
                  {(e,a,e') | e ∈ (reachableFromSetGBA aut aut.initial)
                                ∧ (e,a,e') ∈ T'}`
             >> first_x_assum (qspec_then `realTrans` mp_tac)
             >> Cases_on `aut` >> fs[removeStatesSimpl_def]
             >> rpt strip_tac
             >> `∀i.
                  ∃a j. i ≤ j ∧
                 (f j,a,f (j + 1)) ∈ realTrans ∧
                 (a,f (j + 1)) ∈ f1 (f j) ∧ at x j ∈ a` by (
                  `(realTrans =
                    {(e,a,e') |
                     (e,a,e') ∈ T' ∧
                           e ∈ reachableFromSetGBA (GBA f' f0 f1 f2 f3) f0})
                   ∧ T' ∈ f2` suffices_by metis_tac[]
                 >> qunabbrev_tac `realTrans` >> simp[SET_EQ_SUBSET,SUBSET_DEF]
                 >> rpt strip_tac >> fs[]
              )
             >> first_x_assum (qspec_then `i` mp_tac) >> rpt strip_tac
             >> qexists_tac `a` >> qexists_tac `j` >> simp[]
             >> qunabbrev_tac `realTrans` >> fs[]
            )
       )
  );

(*
  Merge equivalent states
*)

val replaceState_def = Define`
  replaceState x_old x_new s =
    if s = x_old then x_new else s`;

val replaceStateSet_def = Define`
  replaceStateSet x_old x_new set =
    if x_old ∈ set
    then (set DIFF {x_old}) ∪ {x_new}
    else set`;

val replaceAccTrans_def = Define`
  replaceAccTrans x_old x_new aT =
    IMAGE (\s. {(replaceState x_old x_new q1, a, replaceState x_old x_new q2) |
                (q1,a,q2) ∈ s}) aT`;

val REPL_AT_LEMM = store_thm
  ("REPL_AT_LEMM",
   ``!aT t x y.
       t ∈ replaceAccTrans x y aT ==>
       ?t2. t2 ∈ aT ∧
            !q1 a q2. (q1,a,q2) ∈ t2
                      ==> (replaceState x y q1, a, replaceState x y q2) ∈ t``,
   rpt strip_tac >> fs[replaceAccTrans_def] >> metis_tac[]
  );

val REPL_AT_LEMM2 = store_thm
  ("REPL_AT_LEMM2",
  ``!aT t x y. t ∈ aT
  ==> ?t2. t2 ∈ (replaceAccTrans x y aT)
  ∧ !q1 a q2. (q1,a,q2) ∈ t2
       ==> ?q3 q4. (q1 = replaceState x y q3) ∧ (q2 = replaceState x y q4)
                 ∧ (q3,a,q4) ∈ t``,
  rpt strip_tac >> fs[replaceAccTrans_def]
  >> qexists_tac
     `{(replaceState x y q1, a, replaceState x y q2) | (q1,a,q2) ∈ t}`
  >> rpt strip_tac >> fs[] >> metis_tac[]
  );

val equivalentStates_def = Define`
  equivalentStates aT trans q1 q2 =
     (trans q1 = trans q2)
   ∧ !a q3 T. ((a,q3) ∈ trans q1) ∧ T ∈ aT
                   ==> ((q1,a,q3) ∈ T = (q2,a,q3) ∈ T)`;

val mergeState_def = Define`
  mergeState x y (GBA s i t aT alph) =
      if equivalentStates aT t x y
      then GBA
              (s DIFF {x})
              (replaceStateSet x y i)
              (\m. {(a,replaceState x y n) | (a,n) ∈ t m})
              (replaceAccTrans x y aT)
              alph
      else (GBA s i t aT alph)`;

val _ = export_theory();

(* (* val un_merged_run_def = Define` *) *)
(* (*   (un_merged_run word aT x_old x_new init trans f switch 0 = *) *)
(* (*            ((switch,if f 0 ∈ init then f 0 else x_old))) *) *)
(* (*   ∧ (un_merged_run word aT x_old x_new init trans f s (SUC i) = *) *)
(* (*      if ?a. (a, f (SUC i)) ∈ trans (f i) ∧ at word i ∈ a *) *)
(* (*          ∧ (!a2. (f i = x_new) ∧ (a2,x_old) ∈ trans (f i) *) *)
(* (*                  ∧ (at word i ∈ a2) ==> switch ((f i), a2)) *) *)
(* (*      then (switch, f (SUC i)) *) *)
(* (*      else let a2 = @a. (a,x_old) ∈ trans (f i) ∧ (at word i ∈ a) *) *)
(* (*           in ((λ(q,a). if (q,a) = (f i, a2) *) *)
(* (*                        then false else switch (q,a,q2)),x_old))`; *) *)

(* (* val un_merged_run_def = Define` *) *)
(* (*   un_merged_run word aT x_old x_new init trans f i = *) *)
(* (*            if i = 0 *) *)
(* (*            then (if f 0 ∈ init then f 0 else x_old) *) *)
(* (*            else (if ?a. (a,f i) ∈ trans (f (i - 1)) ∧ at word (i-1) ∈ a *) *)
(* (*                   ∧ (!a2. (f i = x_new) ∧ (a2,x_old) ∈ trans (f (i-1)) *) *)
(* (*                   ∧ (at word (i-1) ∈ a2) ==> *) *)
(* (*                   !T. T ∈ aT ==> *) *)
(* (*                       ((f (i-1),a2,x_old) ∈ T ==> (f (i-1),a,f i) ∈ T)) *) *)
(* (*                  then f i else x_old)`; *) *)

(* val un_merged_run_def = Define` *)
(*   (un_merged_run_def w x y init trans f toggle 0 = *)
(*                 if f 0 ∈ init then f 0 else y *)
(*   ) *)
(*   ∧ (un_merged_run_def w α x y init trans f toogle i = *)
(*                 if (α i, f i) ∉ trans (f (i-1)) *)
(*                 then y *)

(*                 then  *)

(* ) *)

(* val MERGE_IS_CORRECT = store_thm *)
(*   ("MERGE_IS_CORRECT", *)
(*    ``!aut x y. isValidGBA aut ∧ x ∈ aut.states ∧ y ∈ aut.states *)
(*             ∧ ~(x = y) ∧ equivalentStates aut.accTrans aut.trans x y *)
(*            ==> (GBA_lang aut = GBA_lang (mergeState x y aut))``, *)
(*    fs[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac *)
(*    >> fs[GBA_lang_def,mergeState_def] *)
(*      >- (rename[`word_range w ⊆ _`] *)
(*          >> `word_range w ⊆ (mergeState x y aut).alphabet` *)
(*            by (Cases_on `aut` >> fs[mergeState_def] *)
(*                >> Cases_on `equivalentStates f2 f1 x y` *)
(*                >> simp[]) *)
(*          (* >> Cases_on `equivalentStates aut.accTrans aut.trans x y` *) *)
(*          (* >- ( *) *)
(*          Cases_on `aut` >> rename[`GBA states init t aT alph`] *)
(*          >> fs[] *)
(*              (* >> qabbrev_tac `s_new = *) *)
(*              (*       @p. p ∈ states ∧ ~(p = q) ∧ equivalentStates aT t p q` *) *)
(*          (* >> `s_new ∈ states ∧ ~(s_new = q) ∧ equivalentStates aT t s_new q` *) *)
(*          (*     by (qunabbrev_tac `s_new` >> metis_tac[]) *) *)
(*           >> Cases_on `r` *)
(*           >> qexists_tac `GBA_RUN (\i. replaceState x y (f i))` *)
(*           >> fs[isGBARunFor_def,mergeState_def] >> rpt strip_tac *)
(*           >> qabbrev_tac `newGBA = *)
(*               GBA (states DIFF {x}) (replaceStateSet x y init) *)
(*                   (λm. {(a,replaceState x y n) | (a,n) ∈ t m}) *)
(*                   (replaceAccTrans x y aT) alph` *)
(*           >- ((* `isValidGBARunFor newGBA *) *)
(*               (*    (GBA_RUN (λi. replaceState q s_new (f i))) x` *) *)
(*               (*       suffices_by metis_tac[] *) *)
(*               simp[isValidGBARunFor_def] >> rpt strip_tac *)
(*               >- (qunabbrev_tac `newGBA` *)
(*                   >> simp[replaceState_def,replaceStateSet_def] *)
(*                   >> Cases_on `f 0 = x` >> simp[] *)
(*                    >- fs[isValidGBARunFor_def] *)
(*                    >- (Cases_on `x ∈ init` >> fs[isValidGBARunFor_def]) *)
(*                  ) *)
(*               >- (fs[isValidGBARunFor_def] *)
(*                   >> `∃a. (a,f (i + 1)) ∈ t (f i) ∧ at w i ∈ a` *)
(*                        by metis_tac[] *)
(*                   >> qexists_tac `a` >> simp[replaceState_def] *)
(*                   >> qunabbrev_tac `newGBA` >> simp[replaceState_def] *)
(*                   >> qexists_tac `f (i + 1)` >> simp[] *)
(*                   >> Cases_on `f i = x` >> fs[equivalentStates_def] *)
(*                   >> metis_tac[] *)
(*                  ) *)
(*           ) *)
(*           >- (qabbrev_tac `newRun = λi. replaceState x y (f i)` *)
(*               (* >> `isAcceptingGBARunFor newGBA (GBA_RUN newRun) x` *) *)
(*               (*       suffices_by metis_tac[] *) *)
(*                >> `!T. T ∈ newGBA.accTrans *)
(*                    ==> (!i. ?a j. i <= j ∧ (newRun j, a, newRun (j+1)) ∈ T *)
(*                         ∧ (a, newRun (j+1)) ∈ newGBA.trans (newRun j) *)
(*                         ∧ at w j ∈ a)` suffices_by metis_tac[GBA_ACC_LEMM] *)
(*                >> qabbrev_tac `aut = GBA states init t aT alph` *)
(*                >> `!T. T ∈ aut.accTrans *)
(*                      ==> (!i. ?a j. i <= j ∧ (f j, a, f (j+1)) ∈ T *)
(*                         ∧ (a, f (j+1)) ∈ aut.trans (f j) *)
(*                         ∧ at w j ∈ a)` by metis_tac[GBA_ACC_LEMM] *)
(*                >> rpt strip_tac *)
(*                >> `?t2. t2 ∈ aut.accTrans *)
(*                      ∧ !q1 a q2. (q1,a,q2) ∈ t2 ==> *)
(*                      (replaceState x y q1, a, replaceState x y q2) ∈ T'` *)
(*                      by (qunabbrev_tac `newGBA` >> fs[] *)
(*                          >> imp_res_tac REPL_AT_LEMM >> qunabbrev_tac `aut` *)
(*                          >> simp[] >> metis_tac[]) *)
(*                   >> first_x_assum (qspec_then `t2` mp_tac) *)
(*                   >> simp[] >> rpt strip_tac *)
(*                   >> first_x_assum (qspec_then `i` mp_tac) >> rpt strip_tac *)
(*                   >> qexists_tac `a` >> qexists_tac `j` >> fs[] *)
(*                   >> qunabbrev_tac `newRun` >> simp[replaceState_def] *)
(*                   >> Cases_on `f j = x` >> Cases_on `f (j + 1) = x` *)
(*                   >> qunabbrev_tac `aut` >> fs[equivalentStates_def] *)
(*                   >> rpt strip_tac >> qunabbrev_tac `newGBA` >> simp[] *)
(*                   >> metis_tac[replaceState_def] *)
(*              ) *)
(*         ) *)
(*      >- (qexists_tac `r` >> simp[isGBARunFor_def] >> strip_tac *)
(*              >> Cases_on `aut` >> simp[mergeState_def] *)
(*               >- (qabbrev_tac `aut = GBA f f0 f1 f2 f3` *)
(*                   >> `isValidGBARunFor aut r x` suffices_by ( *)
(*                        qunabbrev_tac `aut` >> fs[] >> metis_tac[] *)
(*                    ) *)
(*                   >> fs[isGBARunFor_def] *)
(*                  ) *)
(*               >- (qabbrev_tac `aut = GBA f f0 f1 f2 f3` *)
(*                   >> `isAcceptingGBARunFor aut r x` suffices_by ( *)
(*                        qunabbrev_tac `aut` >> fs[] >> metis_tac[] *)
(*                    ) *)
(*                   >> fs[isGBARunFor_def] *)
(*                  ) *)
(*             ) *)
(*         ) *)
(*      >- (`word_range x ⊆ aut.alphabet` by ( *)
(*               Cases_on `aut` >> fs[mergeState_def] >> POP_ASSUM mp_tac *)
(*               >> Cases_on `∃q'. q' ∈ f ∧ q' ≠ q ∧ equivalentStates f2 f1 q' q` *)
(*               >> simp[]) *)
(*          >> Cases_on `∃q'. q' ∈ aut.states ∧ q' ≠ q *)
(*                  ∧ equivalentStates aut.accTrans aut.trans q' q` *)
(*          >> rpt strip_tac *)
(*           >- (fs[isGBARunFor_def,isValidGBARunFor_def] >> Cases_on `aut` *)
(*               >> rename[`GBA states i t aT alph`] *)
(*               >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac *)
(*               >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac *)
(*               >> RULE_ASSUM_TAC(SIMP_RULE (srw_ss())[mergeState_def]) *)
(*               >> rpt strip_tac *)
(*               >> qabbrev_tac *)
(*                   `s_new = @p. p ∈ states ∧ p ≠ q ∧ equivalentStates aT t p q` *)
(*               >> `s_new ∈ states ∧ ~(s_new = q) ∧ equivalentStates aT t s_new q` *)
(*                   by (qunabbrev_tac `s_new` >> fs[] >> metis_tac[]) *)
(*               >> fs[] *)
(*               >> qabbrev_tac *)
(*                   `newGBA = GBA (states DIFF {q}) (replaceStateSet q s_new i) *)
(*                      (λm. {(a,replaceState q s_new n) | (a,n) ∈ t m}) *)
(*                        (replaceAccTrans q s_new aT) alph` *)
(*               >> `isValidGBARunFor newGBA r x` by metis_tac[] *)
(*               >> POP_ASSUM mp_tac >> Cases_on `r` >> simp[isValidGBARunFor_def] *)
(*               >> rpt strip_tac *)
(*               >> qexists_tac `GBA_RUN (un_merged_run x aT q s_new i t f)` *)
(*               >> rpt strip_tac *)
(*                >- (simp[isValidGBARunFor_def,un_merged_run_def] >> rpt strip_tac *)
(*                   >- (Cases_on `f 0 ∈ i` >> fs[] >> qunabbrev_tac `newGBA` *)
(*                       >> fs[replaceStateSet_def] >> metis_tac[] *)
(*                      ) *)
(*                   >- (rename[`n = 0`] *)
(*                       >> `∃a. (a,f (n + 1)) ∈ newGBA.trans (f n) ∧ at x n ∈ a` *)
(*                           by metis_tac[] *)
(*                       >> rpt strip_tac *)
(*                       >> Cases_on ` *)
(*                           ∃a. (a,f (n + 1)) ∈ t (f n) ∧ at x n ∈ a ∧ *)
(*                            ∀a2. *)
(*                             (f (n + 1) = s_new) ∧ (a2,q) ∈ t (f n) *)
(*                             ∧ at x n ∈ a2 ⇒ *)
(*                             ∀T. T ∈ aT ⇒ (f n,a2,q) ∈ T ⇒ (f n,a,s_new) ∈ T` *)
(*                       >> Cases_on `n = 0` >> simp[] *)
(*                        >- (Cases_on `f 0 ∈ i` >> fs[] *)
(*                            >- metis_tac[] *)
(*                            >- (qunabbrev_tac `newGBA` >> fs[replaceStateSet_def] *)
(*                                >> `f 0 = s_new` by (Cases_on `q ∈ i` >> fs[]) *)
(*                                >> fs[equivalentStates_def] >> metis_tac[]) *)
(*                           ) *)
(*                        >- (Cases_on *)
(*                             `∃a. (a,f n) ∈ t (f (n − 1)) ∧ at x (n − 1) ∈ a ∧ *)
(*                               ∀a2. *)
(*                               (f n = s_new) ∧ (a2,q) ∈ t (f (n − 1)) *)
(*                               ∧ at x (n − 1) ∈ a2 ⇒ ∀T. T ∈ aT ⇒ *)
(*                                 (f (n − 1),a2,q) ∈ T ⇒ (f (n − 1),a,s_new) ∈ T` *)
(*                            >- metis_tac[] *)
(*                            >- (simp[] >> qunabbrev_tac `newGBA` *)
(*                               >> fs[replaceStateSet_def,replaceState_def] *)
(*                               >> `f n = s_new` by ( *)
(*                                first_x_assum (qspec_then `n-1` mp_tac) >> simp[] *)
(*                                >> rpt strip_tac >> metis_tac[]) *)
(*                               >> fs[equivalentStates_def] >> rw[] *)
(*                               >> metis_tac[]) *)
(*                           ) *)
(*                        >- (Cases_on `f 0 ∈ i` >> fs[] *)
(*                            >- (qunabbrev_tac `newGBA` >> fs[replaceStateSet_def] *)
(*                                >> fs[replaceState_def] >> Cases_on `n' = q` *)
(*                                >> metis_tac[]) *)
(*                            >- (qunabbrev_tac `newGBA` >> fs[replaceStateSet_def] *)
(*                                >> fs[replaceState_def,equivalentStates_def] *)
(*                                >> `f 0 = s_new` by (Cases_on `q ∈ i` >> fs[]) *)
(*                                >> Cases_on `n' = q` *)
(*                                >> metis_tac[]) *)
(*                           ) *)
(*                        >- (Cases_on *)
(*                             `∃a. (a,f n) ∈ t (f (n − 1)) ∧ at x (n − 1) ∈ a ∧ *)
(*                               ∀a2. *)
(*                               (f n = s_new) ∧ (a2,q) ∈ t (f (n − 1)) *)
(*                               ∧ at x (n − 1) ∈ a2 ⇒ ∀T. T ∈ aT ⇒ *)
(*                                 (f (n − 1),a2,q) ∈ T ⇒ (f (n − 1),a,s_new) ∈ T` *)
(*                             >- (simp[] >> qunabbrev_tac `newGBA` *)
(*                                 >> fs[replaceStateSet_def,replaceState_def] *)
(*                                 >> Cases_on `n' = q` >> fs[] >> metis_tac[] *)
(*                                ) *)
(*                             >- (simp[] >> fs[] >> qunabbrev_tac `newGBA` *)
(*                                 >> fs[replaceStateSet_def,replaceState_def] *)
(*                                 >> `f n = s_new` by ( *)
(*                                      first_x_assum (qspec_then `n-1` mp_tac) *)
(*                                      >> simp[] >> rpt strip_tac >> metis_tac[]) *)
(*                                 >> fs[equivalentStates_def] >> rw[] *)
(*                                 >> metis_tac[]) *)
(*                           ) *)
(*                      ) *)
(*                   ) *)
(*                >- (qabbrev_tac `newRun = un_merged_run x aT q s_new i t f` *)
(*                    >> qabbrev_tac `aut = GBA states i t aT alph` *)
(*                     >> `!T. T ∈ aut.accTrans *)
(*                          ==> (!i. ?a j. i <= j ∧ (newRun j, a, newRun (j+1)) ∈ T *)
(*                                ∧ (a, newRun (j+1)) ∈ aut.trans (newRun j) *)
(*                                ∧ at x j ∈ a)` suffices_by metis_tac[GBA_ACC_LEMM] *)
(*                     >> `isAcceptingGBARunFor newGBA (GBA_RUN f) x` by ( *)
(*                         qunabbrev_tac `aut` >> fs[mergeState_def] *)
(*                         >> metis_tac[]) *)
(*                     >> `!T. T ∈ newGBA.accTrans *)
(*                          ==> (!i. ?a j. i <= j ∧ (f j, a, f (j+1)) ∈ T *)
(*                                ∧ (a, f (j+1)) ∈ newGBA.trans (f j) *)
(*                                ∧ at x j ∈ a)` by metis_tac[GBA_ACC_LEMM] *)
(*                     >> rpt strip_tac *)
(*                     >> `∃t2. t2 ∈ replaceAccTrans q s_new aT ∧ *)
(*                          ∀q1 a q2. *)
(*                           (q1,a,q2) ∈ t2 ⇒ *)
(*                             ?q3 q4. (q1 = replaceState q s_new q3) *)
(*                                   ∧ (q2 = replaceState q s_new q4) *)
(*                                   ∧ ((q3,a,q4) ∈ T')` by ( *)
(*                         imp_res_tac REPL_AT_LEMM2 >> qunabbrev_tac `aut` *)
(*                         >> fs[] >> metis_tac[]) *)
(*                     >> first_x_assum (qspec_then `t2` mp_tac) *)
(*                     >> `t2 ∈ newGBA.accTrans` *)
(*                            by (qunabbrev_tac `newGBA` >> fs[]) *)
(*                     >> simp[] >> rpt strip_tac *)
(*                     >> first_x_assum (qspec_then `i'` mp_tac) >> rpt strip_tac *)
(*                     >> rename[`n <= j`] >> qexists_tac `a` >> qexists_tac `j` *)
(*                     >> fs[] >> strip_tac *)
(*                      >- (`!p. (f p, a, f (p+1)) ∈ t2 *)
(*                                 ==> (newRun p,a,newRun (p+1)) ∈ T'` by ( *)
(*                            Induct_on `p` >> fs[] >> rpt strip_tac *)
(*                            >> qunabbrev_tac `newRun` >> fs[un_merged_run_def] *)
(*                             >- (Cases_on `f 0 ∈ i` >> simp[] *)
(*                              >- (Cases_on `∃a'. (a',f 1) ∈ t (f 0) ∧ at x 0 ∈ a' *)
(*                                   ∧ ∀a2. (f 1 = s_new) ∧ (a2,q) ∈ t (f 0) *)
(*                                   ∧ at x 0 ∈ a2 ⇒ ∀T. T ∈ aT ⇒ *)
(*                                   (f 0,a2,q) ∈ T ⇒ (f 0,a',s_new) ∈ T` *)
(*                               >- (simp[] >> fs[] >> ) *)

(* (* ) *) *)


(* (* ) *) *)


(* (* qunabbrev_tac `newRun` >> simp[un_merged_run_def] *) *)
(* (*                          >>  *) *)



(* (* ) *) *)





(* (*                     >> `!j. (newRun j = f j) \/ (newRun j = q)` by ( *) *)
(* (*                         strip_tac >> qunabbrev_tac `newRun` *) *)
(* (*                         >> fs[un_merged_run_def] >> metis_tac[] *) *)
(* (*                     ) *) *)
(* (*                     >> strip_tac *) *)
(* (*                      >- (first_x_assum (qspec_then `f j` mp_tac) *) *)
(* (*                          >> strip_tac >> first_x_assum (qspec_then `a` mp_tac) *) *)
(* (*                          >> strip_tac *) *)
(* (*                          >> first_x_assum (qspec_then `f (j+1)` mp_tac) *) *)
(* (*                          >> simp[] >> strip_tac *) *)
(* (*                          >> `q3 = newRun j` by ( *) *)
(* (*                               qunabbrev_tac `newRun` >> fs[un_merged_run_def] *) *)
(* (*                               >> fs[replaceState_def] >> Cases_on `q3=q` >> fs[] *) *)
(* (*                               >> Cases_on `j=0` >> simp[] *) *)

(* (* ) *) *)

(* (*  >> Cases_on `q3 = q` *) *)
(* (*                          >> Cases_on `q4 = q` >> fs[replaceState_def] *) *)
(* (*                        >- (`(s_new,a,s_new) ∈ T'` suffices_by ( *) *)
(* (*                             qunabbrev_tac `newRun` >> fs[un_merged_run_def] *) *)
(* (*                             >> simp[] >> strip_tac >>  *) *)

(* (* )) *) *)


(* (*                      >- (qunabbrev_tac `newRun` >> qunabbrev_tac `aut` *) *)
(* (*                       >> simp[un_merged_run_def] >> fs[replaceState_def] *) *)
(* (*                       >> fs[equivalentStates_def] *) *)
(* (*                       >> Cases_on `~(f j = s_new)` >> simp[] *) *)
(* (*                        >- (qunabbrev_tac `newGBA` >> fs[] *) *)
(* (*                            >> first_x_assum (qspec_then `f j` mp_tac) *) *)
(* (*                            >> strip_tac >> first_x_assum (qspec_then `a` mp_tac) *) *)
(* (*                            >> strip_tac >> first_x_assum (qspec_then `f (j+1)` mp_tac) *) *)
(* (*                            >> simp[] >> rpt strip_tac >> Cases_on `q3 = q` *) *)
(* (*                            >> fs[] >> rw[] *) *)
(* (*                             >- (Cases_on `n' = q` >> fs[] *) *)
(* (*                               >- (fs[replaceAccTrans_def,replaceState_def] *) *)
(* (*                                   >>  *) *)

(* (* ) *) *)
(* (* ) *) *)

(* (*                            >> Cases_on `j = 0` >> simp[] *) *)
(* (*                             >- (Cases_on `f 0 ∈ i` >> fs[] *) *)
(* (*                              >- (Cases_on `q3 = q` >> Cases_on `q4 = q` *) *)
(* (*                                  >> simp[] >> rw[] *) *)
(* (*                                   >- (Cases_on `n' = q` >> rw[] *) *)
(* (*                                    >- (`(f 0,a,n') ∈ T'` by metis_tac[] *) *)
(* (*                                        >> metis_tac[] *) *)
(* (* ) *) *)
(* (* ) *) *)
(* (* ) *) *)
(* (* ) *) *)
(* (*                             >- (simp[] >> Cases_on `f 0 ∈ i` >> simp[] *) *)
(* (*                               >- ( *) *)

(* (* ) *) *)
(* (* ) *) *)
(* (* ) *) *)

(* (*                       >> simp[] >> first_x_assum (qspec_then `f j` mp_tac) *) *)
(* (*                       >> strip_tac >> first_x_assum (qspec_then `a` mp_tac) *) *)
(* (*                       >> strip_tac >> first_x_assum (qspec_then `f (j+1)` mp_tac) *) *)
(* (*                       >> simp[] >> strip_tac >> fs[replaceState_def] *) *)
(* (*                       >> fs[equivalentStates_def] *) *)
(* (*                       >> Cases_on `~(f j = q)` >> simp[] *) *)
(* (*                        >- (Cases_on `j = 0` >> simp[] >>  *) *)


(* (*                           ) *) *)


(* (*                       >> Cases_on `q3 = q` >> Cases_on `q4 = q` >> simp[] *) *)
(* (*                        >- (`(a,q) ∈ t s_new` by ( *) *)
(* (*                             fs[isValidGBA_def] *) *)

(* (* ) *) *)




(* (* fs[equivalentStates_def] *) *)
(* (*                            >> Cases_on ) *) *)


(* (*                       >> Cases_on `j = 0` *) *)
(* (*                       >> Cases_on `∃a. (a,f j) ∈ t (f (j − 1)) ∧ at x (j − 1) ∈ a` *) *)
(* (*                       >> Cases_on `∃a'. (a',f (j+1)) ∈ t (f j) ∧ at x j ∈ a'` *) *)
(* (*                       >> rw[] >> fs[replaceState_def] >>  *) *)
(* (*                          >- () *) *)
(* (* ) *) *)
(* (* ) *) *)
(* (* ) *) *)
