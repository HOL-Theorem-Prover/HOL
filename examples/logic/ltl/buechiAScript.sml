open HolKernel Parse bossLib boolLib pairTheory pred_setTheory arithmeticTheory relationTheory

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
        ∧ (!q1 a q2 T. (q1,a,q2) ∈ T ∧ T ∈ A.accTrans ==> (a,q2) ∈ A.trans q1)`;

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
