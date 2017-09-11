open HolKernel Parse bossLib boolLib pairTheory pred_setTheory arithmeticTheory relationTheory set_relationTheory

open wordTheory generalHelpersTheory

val _ = new_theory "buechiA"

val _ = Datatype
  `GBA = <| states      : 's set;
            initial     : 's set;
            trans       : 's -> (('a set # 's) set);
            accTrans    : (('s # ('a set) # 's) set) set;
            alphabet    : 'a set
            |>`;

val isValidGBA_def = Define`
  isValidGBA (A: ('s,'a) GBA) =
    (A.initial ⊆ A.states)
        ∧ (!s a d. (s ∈ A.states) /\ ((a, d) ∈ (A.trans s))
                                  ==> (d ∈ A.states) ∧ (a ⊆ A.alphabet))
        ∧ (!q1 a q2 T. (q1,a,q2) ∈ T ∧ T ∈ A.accTrans
               ==> (q1 ∈ A.states ∧ (a,q2) ∈ A.trans q1))`;

val _ = Datatype` gba_run = GBA_RUN (num -> 's)`;

val isValidGBARunFor_def = Define`
  isValidGBARunFor aut (GBA_RUN r) word =
    (r 0 ∈ aut.initial)
    ∧ (!i. ?a. (a, r (i + 1)) ∈ aut.trans (r i) ∧ (at word i ∈ a))`;

val isAcceptingGBARunFor_def = Define`
  isAcceptingGBARunFor aut (GBA_RUN r) x =
    !T. T ∈ aut.accTrans
        ==> INFINITE { i | ?a. (r i,a,r (i+1)) ∈ T
                            ∧ (a, r (i+1)) ∈ aut.trans (r i)
                            ∧ at x i ∈ a}`;

val isGBARunFor_def = Define`
  isGBARunFor aut run word =
    isValidGBARunFor aut run word ∧ isAcceptingGBARunFor aut run word`;

val GBA_lang_def = Define`
  GBA_lang aut = { w | ?r. isGBARunFor aut r w ∧ word_range w ⊆ aut.alphabet }`;

val GBA_ACC_LEMM = store_thm
  ("GBA_ACC_LEMM",
  ``!aut r x. isAcceptingGBARunFor aut (GBA_RUN r) x
        = !T. T ∈ aut.accTrans
              ==> (!i. ?a j. i <= j ∧ (r j, a, r (j+1)) ∈ T
                                    ∧ (a, r (j+1)) ∈ aut.trans (r j)
                                    ∧ at x j ∈ a)``,
  rw[EQ_IMP_THM] >> fs[isAcceptingGBARunFor_def]
    >- (`INFINITE {j | ∃a. (r j,a,r (j + 1)) ∈ T'
                        ∧ (a, r (j+1)) ∈ aut.trans (r j) ∧ at x j ∈ a}` by fs[]
        >> `!k. i <= k ==> INFINITE {j | ?a. (r j, a, r (j + 1)) ∈ T'
                                          ∧ (a, r (j+1)) ∈ aut.trans (r j)
                                          ∧ at x j ∈ a
                                          ∧ k <= j }` by (
            rpt strip_tac
            >> `{j | ∃a. (r j,a,r (j + 1)) ∈ T' ∧ (a, r (j+1)) ∈ aut.trans (r j)
                      ∧ at x j ∈ a ∧ k ≤ j} =
        {j | ∃a. (r j,a,r (j + 1)) ∈ T'
              ∧ (a, r (j+1)) ∈ aut.trans (r j) ∧ at x j ∈ a} DIFF (count k)` by (
                fs[DIFF_DEF, count_def] >> fs[SET_EQ_SUBSET, SUBSET_DEF]
                >> rpt strip_tac >> fs[] >> metis_tac[]
            )
            >> `FINITE (count k)` by metis_tac[FINITE_COUNT]
            >> metis_tac[INFINITE_DIFF_FINITE]
         )
        >> `INFINITE {j | ∃a. (r j,a,r (j + 1)) ∈ T'
                           ∧ (a, r (j+1)) ∈ aut.trans (r j)
                           ∧ at x j ∈ a
                           ∧ i ≤ j}` by fs[]
        >> `?y. y ∈ {j | ∃a. (r j,a,r (j + 1)) ∈ T'
                          ∧ (a, r (j+1)) ∈ aut.trans (r j)
                          ∧ at x j ∈ a
                          ∧ i ≤ j}` by metis_tac[INFINITE_INHAB]
        >> fs[IN_ABS] >> metis_tac[]
       )
    >- (rpt strip_tac
        >> `∀i. ∃j a. i ≤ j ∧ (r j,a,r (j + 1)) ∈ T'
                            ∧ (a, r (j+1)) ∈ aut.trans (r j)
                            ∧ at x j ∈ a`
            by metis_tac[DECIDE ``i <= i``]
        >> `?f. !i. ?a. i ≤ (f i) ∧ (r (f i),a,r (f i + 1)) ∈ T'
                 ∧ (a, r ((f i)+1)) ∈ aut.trans (r (f i))
                 ∧ at x (f i) ∈ a` by metis_tac[SKOLEM_THM]
        >> `INFINITE { f i | i ∈ 𝕌(:num)}` by metis_tac[NO_BOUNDS_INFINITE]
        >> `{f i | i ∈ 𝕌(:num)} ⊆ {i | ∃a. (r i,a,r (i + 1)) ∈ T'
                                        ∧ (a, r (i+1)) ∈ aut.trans (r i)
                                        ∧ at x i ∈ a}` by (
             fs[SET_EQ_SUBSET, SUBSET_DEF] >> rpt strip_tac
             >> metis_tac[])
        >> metis_tac[PSUBSET_DEF, PSUBSET_FINITE]
       )
  );

val ACC_TRANS_LEMM = store_thm
  ("ACC_TRANS_LEMM",
   ``!aut r word. isAcceptingGBARunFor aut (GBA_RUN r) word
     ∧ isValidGBA aut
     ∧ FINITE aut.alphabet ∧ FINITE aut.states
        ==> !T. T ∈ aut.accTrans
              ==> (?q1 a q2. !i. ?j. i <= j ∧ (q1 = r j) ∧ (q2 = r (j+1))
                                   ∧ (a,q2) ∈ aut.trans q1
                                   ∧ at word j ∈ a)``,
   rpt strip_tac
   >> `FINITE T'` by (
       fs[isValidGBA_def]
       >> `T' ⊆ (aut.states × ((POW aut.alphabet) × aut.states))` by (
           simp[SUBSET_DEF] >> rpt strip_tac
           >> Cases_on `x` >> Cases_on `r'` >> simp[] >> metis_tac[IN_POW]
       )
   >> metis_tac[FINITE_POW,FINITE_CROSS,PSUBSET_DEF,PSUBSET_FINITE]
   )
   >> rename[`FINITE T1`]
   >> `!i. ∃a j.
        i ≤ j ∧ (r j,a,r (j + 1)) ∈ T1 ∧
        (a,r (j + 1)) ∈ aut.trans (r j)
        ∧ at word j ∈ a` by metis_tac[GBA_ACC_LEMM]
   >> CCONTR_TAC >> fs[]
   >> `?f. !q1 a q2 j.
        ¬(f q1 a q2 ≤ j) ∨ q1 ≠ r j ∨ q2 ≠ r (j + 1) ∨
        (a,q2) ∉ aut.trans q1 ∨ at word j ∉ a` by metis_tac[SKOLEM_THM]
   >> qabbrev_tac `maxOcc = { f q1 a q2 | (q1,a,q2) ∈ T1 }`
   >> `?x. x ∈
        maximal_elements maxOcc
        (rrestrict (rel_to_reln $<=) maxOcc)`
       by (
       `linear_order (rrestrict (rel_to_reln $<=) maxOcc) maxOcc` by (
           fs[linear_order_def,rel_to_reln_def,rrestrict_def] >> rpt strip_tac
            >- (fs[domain_def,SUBSET_DEF] >> rpt strip_tac >> metis_tac[])
            >- (fs[range_def,SUBSET_DEF] >> rpt strip_tac >> metis_tac[])
            >- fs[transitive_def]
            >- fs[antisym_def]
       )
       >> HO_MATCH_MP_TAC finite_linear_order_has_maximal
       >> rpt strip_tac
        >- (qunabbrev_tac `maxOcc` >> fs[]
            >> qabbrev_tac `f2 = λ(m,n,b). f m n b`
            >> `FINITE {f2 x | x ∈ T1 }`
               suffices_by (qunabbrev_tac `f2` >> rpt strip_tac
                            >> `{(λ(m,n,b). f m n b) x | x ∈ T1}
                              = {f q1 a q2 | (q1,a,q2) ∈ T1}` by (
                                 simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                                 >- (Cases_on `x'` >> Cases_on `r'`
                                     >> fs[] >> metis_tac[])
                                 >- (qexists_tac `(q1,a,q2)` >> fs[])
                             )
                            >> metis_tac[])
            >> metis_tac[IMAGE_FINITE, IMAGE_DEF])
        >- fs[]
        >- (qunabbrev_tac `maxOcc`
            >> `~(T1 = {})` suffices_by (
                 rpt strip_tac
                 >> `?x. x ∈ T1` by fs[MEMBER_NOT_EMPTY]
                 >> Cases_on `x` >> Cases_on `r'`
                 >> `f q q' r'' ∈ {f q1 a q2 | (q1,a,q2) ∈ T1}` by (
                     fs[IN_DEF] >> metis_tac[])
                 >> metis_tac[MEMBER_NOT_EMPTY]
             )
            >> metis_tac[MEMBER_NOT_EMPTY]
           )
   )
   >> first_x_assum (qspec_then `x + 1` mp_tac) >> rpt strip_tac
   >> fs[maximal_elements_def,rrestrict_def,rel_to_reln_def]
   >> qunabbrev_tac `maxOcc`
   >> `¬(f (r j) a (r (j + 1)) ≤ j) ∨
       (a,r (j + 1)) ∉ aut.trans (r j) ∨ at word j ∉ a` by fs[]
   >> first_x_assum (qspec_then `f (r j) a (r (j + 1))` mp_tac)
   >> POP_ASSUM mp_tac >> simp[] >> rpt strip_tac
   >> metis_tac[]
  );


val GBA_FINITE_LEMM = store_thm
  ("GBA_FINITE_LEMM",
   ``!aut. FINITE aut.states ∧ FINITE aut.alphabet ∧ isValidGBA aut ==>
       !q. q ∈ aut.states ==> FINITE (aut.trans q)``,
   rpt strip_tac
   >> `aut.trans q ⊆ ((POW aut.alphabet) × aut.states)` by (
       fs[isValidGBA_def] >> simp[SUBSET_DEF] >> rpt strip_tac
         >- (Cases_on `x` >> metis_tac[IN_POW,FST])
         >- (Cases_on `x` >> metis_tac[IN_POW,SND])
   )
   >> metis_tac[FINITE_CROSS,FINITE_POW,PSUBSET_DEF,PSUBSET_FINITE]
  );

val GBA_RUN_LEMM = store_thm
  ("GBA_RUN_LEMM",
   ``!aut f w. isValidGBA aut ∧ isValidGBARunFor aut (GBA_RUN f) w
      ==> !i. f i ∈ aut.states``,
   rpt gen_tac >> strip_tac >> Induct_on `i`
   >> fs[isValidGBARunFor_def,isValidGBA_def]
    >- metis_tac[SUBSET_DEF]
    >- (rw[SUC_ONE_ADD] >> metis_tac[])
  );



(*
  reachable states
*)

val stepGBA_def = Define`
  stepGBA aut = \x y. ?a. (a,y) ∈ aut.trans x ∧ x ∈ aut.states`;

val reachableFromGBA_def = Define`
  reachableFromGBA aut = (stepGBA aut)^*`;

val reachableFromSetGBA_def = Define`
  reachableFromSetGBA aut s = { y | ?x. reachableFromGBA aut x y ∧ x ∈ s }`;

val REACHABLE_GBA_LEMM = store_thm
  ("REACHABLE_GBA_LEMM",
  ``!aut q1 q2. isValidGBA aut ∧ reachableFromGBA aut q1 q2 ∧ q1 ∈ aut.states
    ==> q2 ∈ aut.states``,
  gen_tac
  >> `isValidGBA aut ==> !q1 q2. reachableFromGBA aut q1 q2
        ==> q1 ∈ aut.states ==> q2 ∈ aut.states`
     suffices_by metis_tac[]
  >> strip_tac >> simp[reachableFromGBA_def]
  >> HO_MATCH_MP_TAC RTC_INDUCT >> rpt strip_tac >> fs[]
  >> fs[stepGBA_def,isValidGBA_def] >> metis_tac[]
  );

val _ = export_theory();
