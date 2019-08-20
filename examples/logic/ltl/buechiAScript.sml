open HolKernel Parse bossLib boolLib pairTheory pred_setTheory arithmeticTheory relationTheory set_relationTheory whileTheory

open wordTheory generalHelpersTheory

val _ = new_theory "buechiA"
val _ = ParseExtras.temp_loose_equality()

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
                                   ∧ at word j ∈ a
                                   ∧ (q1,a,q2) ∈ T)``,
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
        (a,q2) ∉ aut.trans q1 ∨ at word j ∉ a ∨ (q1,a,q2) ∉ T1`
      by metis_tac[SKOLEM_THM]
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
       (a,r (j + 1)) ∉ aut.trans (r j) ∨ at word j ∉ a
       ∨ (r j,a,r (j+1)) ∉ T1` by fs[]
   >> first_x_assum (qspec_then `f (r j) a (r (j + 1))` mp_tac)
   >> POP_ASSUM mp_tac >> simp[] >> rpt strip_tac
   >> metis_tac[]
  );

val alph_counter_def = Define`
  (alph_counter N num_to_T acc_T 0 = (0,0))
  ∧ (alph_counter N num_to_T acc_T (SUC i) =
       let last_switched = FST (alph_counter N num_to_T acc_T i)
       in let currentT_no = SND (alph_counter N num_to_T acc_T i)
       in if acc_T (num_to_T currentT_no) last_switched = i
          then (SUC i,(currentT_no + 1) MOD N)
          else (last_switched, currentT_no)
    )`;

val ALPH_COUNTER_FST_LEMM = store_thm
  ("ALPH_COUNTER_FST_LEMM",
   ``!N f g i. (FST (alph_counter N f g i)
                <= FST (alph_counter N f g (SUC i)))
             ∧ (FST (alph_counter N f g i) <= i)``,
   strip_tac >> strip_tac >> strip_tac >> Induct_on `i`
   >- simp[alph_counter_def]
   >- (qabbrev_tac `M = SUC i` >> simp[alph_counter_def]
       >> Cases_on `g (f (SND (alph_counter N f g M)))
                            (FST (alph_counter N f g M)) = M`
       >> qunabbrev_tac `M` >> fs[] >> simp[alph_counter_def]
       >> Cases_on `g (f (SND (alph_counter N f g i)))
                      (FST (alph_counter N f g i)) = i`
       >> fs[]
      )
  );

val ALPH_COUNTER_FST_LEMM2 = store_thm
  ("ALPH_COUNTER_FST_LEMM2",
   ``!N f g i. (alph_counter N f g i = alph_counter N f g (SUC i))
            \/ (FST (alph_counter N f g (SUC i)) = (SUC i))``,
   strip_tac >> strip_tac >> strip_tac >> Induct_on `i`
   >- (simp[alph_counter_def]
       >> Cases_on `g (f 0) 0 = 0` >> fs[]
      )
   >- (qabbrev_tac `M = SUC i` >> simp[alph_counter_def]
       >> Cases_on `g (f (SND (alph_counter N f g M)))
                            (FST (alph_counter N f g M)) = M`
       >> fs[]
      )
  );

(* val GBA_RUN_ALPH_FUN = store_thm *)
(*   ("GBA_RUN_ALPH_FUN", *)
(*    ``!aut r x. isAcceptingGBARunFor aut (GBA_RUN r) x *)
(*              ∧ isValidGBARunFor aut (GBA_RUN r) x *)
(*              ∧ FINITE aut.accTrans *)
(*                ==> ?f. !i. at x i ∈ f i ∧ (f i, r (i+1)) ∈ aut.trans (r i) *)
(*                      ∧ (!T. T ∈ aut.accTrans *)
(*                          ==> (!i. ?j. i <= j ∧ (r j, f j, r (j+1)) ∈ T *)
(*                                     ∧ (f j, r (j+1)) ∈ aut.trans (r j) *)
(*                                     ∧ at x j ∈ (f j)))``, *)
(*    rpt strip_tac >> IMP_RES_TAC GBA_ACC_LEMM *)
(*    >> fs[isValidGBARunFor_def] *)
(*    >> `!T. T ∈ aut.accTrans *)
(*             ==> ?h. !i. (h i, r (i + 1)) ∈ aut.trans (r i) *)
(*                       ∧ at x i ∈ h i *)
(*                       ∧ ?j. i <= j ∧ (r j, h j, r (j+1)) ∈ T` by ( *)
(*        rpt strip_tac *)
(*        >> `?h_0. !i. (h_0 i, r (i+1)) ∈ aut.trans (r i) ∧ at x i ∈ h_0 i` *)
(*            by metis_tac[SKOLEM_THM] *)
(*        >> first_x_assum (qspec_then `T'` mp_tac) >> rpt strip_tac *)
(*        >> `?h_s. !i. ?j. *)
(*               i ≤ j ∧ (r j,h_s i,r (j + 1)) ∈ T' ∧ *)
(*               (h_s i,r (j + 1)) ∈ aut.trans (r j) ∧ at x j ∈ h_s i` *)
(*           by metis_tac[SKOLEM_THM] *)
(*        >> `?h_s_j. !i. *)
(*               i ≤ h_s_j i ∧ (r (h_s_j i),h_s i,r ((h_s_j i) + 1)) ∈ T' ∧ *)
(*               (h_s i,r ((h_s_j i) + 1)) ∈ aut.trans (r (h_s_j i)) *)
(*               ∧ at x (h_s_j i) ∈ h_s i` *)
(*           by metis_tac[SKOLEM_THM] *)
(*        >> qexists_tac `λi. *)
(*               if ?k. i = h_s_j k then h_s (@k. h_s_j k = i) else h_0 i` *)
(*        >> rpt strip_tac >> Cases_on `?k. i = h_s_j k` >> fs[] *)
(*        >> rw[] >> metis_tac[] *)
(*    ) *)
(*    >> `?h_T. !T. T ∈ aut.accTrans *)
(*          ==>  ∀i. *)
(*          ((h_T T) i,r (i + 1)) ∈ aut.trans (r i) ∧ at x i ∈ (h_T T) i ∧ *)
(*          ∃j. i ≤ j ∧ (r j,(h_T T) j,r (j + 1)) ∈ T` by metis_tac[SKOLEM_THM] *)
(*    >> Cases_on `CARD aut.accTrans < 2` *)
(*    >- (`(CARD aut.accTrans = 1) \/ (CARD aut.accTrans = 0)` by ( *)
(*          Cases_on `CARD aut.accTrans = 0` >> fs[] >> metis_tac[CARD_EQ_0] *)
(*         ) *)
(*        >- (`SING aut.accTrans` by metis_tac[SING_IFF_CARD1] *)
(*            >> fs[SING_DEF] >> rename[`aut.accTrans = {t}`] *)
(*            >> qexists_tac `h_T t` >> rpt strip_tac >> fs[] *)
(*           ) *)
(*        >- (`aut.accTrans = {}` by metis_tac[CARD_EQ_0] *)
(*            >> `?f. !i. ((f i),r (i + 1)) ∈ aut.trans (r i) ∧ at x i ∈ (f i)` *)
(*               by metis_tac[SKOLEM_THM] *)
(*            >> qexists_tac `f` >> rpt strip_tac >> fs[] *)
(*            >> metis_tac[NOT_IN_EMPTY] *)
(*           ) *)
(*       ) *)
(*    >- ( *)
(*     `~(0 = CARD aut.accTrans)` by simp[] *)
(*     >> `~(aut.accTrans = {})` by metis_tac[CARD_EQ_0] *)
(*     >> `!T. T ∈ aut.accTrans ==> !i. ?j. i ≤ j ∧ (r j,h_T T j,r (j + 1)) ∈ T` *)
(*        by metis_tac[] *)
(*     >> `?g. !T. T ∈ aut.accTrans *)
(*                ==> !i. (i <= g T i) *)
(*                      ∧ (r (g T i),h_T T (g T i),r ((g T i) + 1)) ∈ T` *)
(*         by metis_tac[SKOLEM_THM] *)
(*     >> qabbrev_tac `N = CARD aut.accTrans` *)
(*     >> `∃f. *)
(*        (∀n m. n < N ∧ m < N ⇒ (f n = f m) ⇒ (n = m)) *)
(*        ∧ (aut.accTrans = {f n | n < N})` *)
(*        by (qunabbrev_tac `N` >> metis_tac[FINITE_ISO_NUM]) *)
(*     >> qabbrev_tac `α = λi. h_T (f (SND (alph_counter N f g i))) i` *)
(*     >> `0 < N` by metis_tac[CARD_EQ_0, DECIDE ``~(N = 0) ==> (0 < N)``] *)
(*     >> `!i. f (i MOD N) ∈ aut.accTrans` by ( *)
(*         rpt strip_tac *)
(*             >> `i MOD N < N` by metis_tac[MOD_LESS] *)
(*             >> `f (i MOD N) ∈ {f n | n < N}` *)
(*         suffices_by metis_tac[] *)
(*     >> rw[] >> metis_tac[] *)
(*     ) *)
(*     >> `!i. i < N ==> f i ∈ aut.accTrans` by *)
(*          (fs[] >> rpt strip_tac >> metis_tac[]) *)
(*     >> `!n. SND (alph_counter N f g n) < N` by ( *)
(*         Induct_on `n` >> simp[alph_counter_def] *)
(*          >> Cases_on `g (f (SND (alph_counter N f g n))) *)
(*                          (FST (alph_counter N f g n)) = n` *)
(*          >> simp[] *)
(*     ) *)
(*     >> `!i n. n < N ==> ?j. i <= j ∧ (SND (alph_counter N f g j) = n)` by ( *)
(*       qabbrev_tac `alph_T = λi. SND (alph_counter N f g i)` *)
(*       >> rw[] *)
(*       >> `(∀j. (alph_T (SUC j) = alph_T j) *)
(*              ∨ (alph_T (SUC j) = (alph_T j + 1) MOD N)) *)
(*         ∧ (∀i. ∃k. i ≤ k ∧ alph_T (SUC k) ≠ alph_T k) *)
(*         ∧ (alph_T 0 = 0) ∧ 0 < N` by ( *)
(*           rpt conj_tac *)
(*           >- (qunabbrev_tac `alph_T` >> simp[alph_counter_def] *)
(*               >> rpt strip_tac *)
(*               >> Cases_on *)
(*                    `g (f (SND (alph_counter N f g j))) *)
(*                         (FST (alph_counter N f g j)) = j` >> fs[] *)
(*              ) *)
(*           >- (strip_tac >> qunabbrev_tac `alph_T` >> simp[] *)
(*               >> CCONTR_TAC >> fs[] *)
(*               >> `!k. i <= k ==> (~(k = g (f (SND (alph_counter N f g i))) *)
(*                                           (FST (alph_counter N f g k))) *)
(*                                   ∧ (SND (alph_counter N f g i) *)
(*                                      = SND (alph_counter N f g k)) *)
(*                                   ∧ (FST (alph_counter N f g i) *)
(*                                           = FST (alph_counter N f g k)))` *)
(*                  by ( *)
(*                  Induct_on `k` >> fs[] >> rpt strip_tac *)
(*                  >- (rw[] >> first_assum (qspec_then `0` mp_tac) >> simp[] *)
(*                      >> PURE_REWRITE_TAC[DECIDE ``1 = SUC 0``] *)
(*                      >> fs[alph_counter_def] *)
(*                      ) *)
(*                  >- (Cases_on `SUC k = i` >> fs[] >> rw[] *)
(*                       >- (first_x_assum (qspec_then `SUC k` mp_tac) >> simp[] *)
(*                          >> qabbrev_tac `M = SUC k` >> simp[alph_counter_def] *)
(*                          >> `2 <= N` by simp[] *)
(*                          >> metis_tac[MOD_GEQ_2_INCREASES,LESS_MOD] *)
(*                          ) *)
(*                       >- (first_x_assum (qspec_then `SUC k` mp_tac) *)
(*                           >> qabbrev_tac `M = SUC k` >> simp[alph_counter_def] *)
(*                           >> `SND (alph_counter N f g M) *)
(*                                = SND (alph_counter N f g i)` by ( *)
(*                                qunabbrev_tac `M` >> simp[alph_counter_def] *)
(*                                >> metis_tac[] *)
(*                            ) *)
(*                           >> rw[] *)
(*                           >- (`2 <= N` by simp[] *)
(*                                >> metis_tac[MOD_GEQ_2_INCREASES,LESS_MOD]) *)
(*                           >- (fs[] >> metis_tac[]) *)
(*                          ) *)
(*                     ) *)
(*                  >- (Cases_on `SUC k = i` >> fs[] >> rw[] *)
(*                      >> simp[alph_counter_def] >> metis_tac[] *)
(*                     ) *)
(*                  >- (Cases_on `SUC k = i` >> fs[] >> rw[] *)
(*                               >> simp[alph_counter_def] >> metis_tac[] *)
(*                     ) *)
(*                ) *)
(*               >> first_assum *)
(*                    (qspec_then `f (SND (alph_counter N f g i))` mp_tac) *)
(*               >> simp[] >> rpt strip_tac *)
(*               >- metis_tac[] *)
(*               >- (fs[] *)
(*                   >> `g (f (SND (alph_counter N f g i))) *)
(*                            (FST (alph_counter N f g i)) *)
(*                            < (FST (alph_counter N f g i))` suffices_by ( *)
(*                        strip_tac >> qexists_tac `(FST (alph_counter N f g i))` *)
(*                        >> disj1_tac >> simp[] *)
(*                    ) *)
(*                   >> Q.HO_MATCH_ABBREV_TAC `g (f A) B < B` *)
(*                   >> Cases_on `i <= B` *)
(*                   >- (`B <= g (f A) B` by metis_tac[] >> fs[] *)
(*                       >> first_x_assum (qspec_then `g (f A) B` mp_tac) >> simp[] *)
(*                       >> rpt strip_tac >> metis_tac[]) *)
(*                   >- (`!j. B <= (i-j) ==> (alph_counter N f g (i-j) = (B,A)) *)
(*                                         ∧ ~((i - j) = g (f A) B)` *)
(*                         by ( *)
(*                         Induct_on `j` >> fs[] >> rpt strip_tac *)
(*                         >- (qunabbrev_tac `A` >> qunabbrev_tac `B` >> fs[]) *)
(*                         >- metis_tac[DECIDE ``i <= i``] *)
(*                         >-(`(alph_counter N f g (i − j)) = (B,A)` by simp[] *)
(*                            >> Cases_on `j <= i` >> fs[] >> Cases_on `j = i` *)
(*                            >> fs[] *)
(*                            >- (`B = 0` by simp[] >> rw[] *)
(*                                >> rw[DECIDE ``i - SUC i = 0``] *)
(*                                >> simp[alph_counter_def] *)
(*                                >> fs[alph_counter_def] *)
(*                               ) *)
(*                            >- ( *)
(*                             Cases_on `i-j = B` >> fs[] *)
(*                             >> `SUC (i - SUC j) = i - j` by simp[] *)
(*                             >> `alph_counter N f g (i − SUC j) *)
(*                                  = alph_counter N f g (SUC (i − SUC j))` *)
(*                                  suffices_by fs[] *)
(*                             >> `((alph_counter N f g (i - SUC j)) *)
(*                                  = alph_counter N f g (SUC (i - SUC j))) *)
(*                                   \/ (FST (alph_counter N f g (SUC (i - SUC j))) *)
(*                                       = SUC (i - SUC j))` *)
(*                                by metis_tac[ALPH_COUNTER_FST_LEMM2] *)
(*                             >> `B = SUC (i - SUC j)` by metis_tac[FST] *)
(*                             >> fs[] *)
(*                                ) *)
(*                            >- (`B = 0` by simp[] >> rw[] *)
(*                                >> rw[DECIDE ``i - SUC i = 0``] *)
(*                                >> simp[alph_counter_def] *)
(*                                >> fs[alph_counter_def] *)
(*                                >> `i - (SUC j) = 0` by simp[] *)
(*                                >> `i - j = 0` by simp[] *)
(*                                >> `alph_counter N f g 0 = (0,A)` by metis_tac[] *)
(*                                >> `A = 0` by fs[alph_counter_def] *)
(*                                >> metis_tac[alph_counter_def] *)
(*                               ) *)
(*                           ) *)
(*                         >- (`(alph_counter N f g (i − j)) = (B,A)` by simp[] *)
(*                             >> Cases_on `j <= i` >> fs[] >> Cases_on `j = i` *)
(*                             >> fs[] >> `SUC (i - SUC j) = i - j` by simp[] *)
(*                             >> `alph_counter N f g (SUC (i - (SUC j))) = (B,A)` *)
(*                                 by rw[] *)
(*                             >> POP_ASSUM mp_tac >> simp[alph_counter_def] *)
(*                             >> fs[] *)
(*                             >> `((alph_counter N f g (i - SUC j)) *)
(*                                  = alph_counter N f g (SUC (i - SUC j))) *)
(*                                   \/ (FST (alph_counter N f g (SUC (i - SUC j))) *)
(*                                         = SUC (i - SUC j))` *)
(*                                by metis_tac[ALPH_COUNTER_FST_LEMM2] *)
(*                             >> rw[] >> CCONTR_TAC >> fs[] *)
(*                            ) *)
(*                         ) *)
(*                       >> CCONTR_TAC >> `B <= g (f A) B` by simp[] *)
(*                       >> `?p. p + B = g (f A) B` by metis_tac[LESS_EQ_ADD_EXISTS] *)
(*                       >> Cases_on `i <= p + B` >> fs[] *)
(*                       >- metis_tac[] *)
(*                       >- (`B + p <= i` by simp[] *)
(*                           >> `?k. B + p = i - k` by metis_tac[LESS_EQUAL_DIFF] *)
(*                           >> `B <= i - k` by simp[] *)
(*                           >> metis_tac[] *)
(*                          ) *)
(*                      ) *)
(*                  ) *)
(*              ) *)
(*           >- (qunabbrev_tac `alph_T` >> simp[alph_counter_def]) *)
(*           >- simp[] *)
(*       ) *)
(*       >> IMP_RES_TAC INCREASING_MOD_CYCLES >> metis_tac[] *)
(*     ) *)
(*     >> qexists_tac `α` >> rpt strip_tac *)
(*     >- (qunabbrev_tac `α` >> fs[] >> metis_tac[]) *)
(*     >- (qunabbrev_tac `α` >> fs[] >> metis_tac[]) *)
(*     >- (`?a. (f a = T') ∧ (a < N)` by ( *)
(*           `!x. x ∈ aut.accTrans ==> x ∈ {f n | n < N}` by fs[] *)
(*           >> fs[] >> metis_tac[] *)
(*         ) *)
(*         >> `∃j. i ≤ j ∧ (SND (alph_counter N f g j) = a)` by fs[] *)
(*         >> qexists_tac `g T' j` >> rpt strip_tac >> fs[] *)
(*         >- (`j <= g T' j` by metis_tac[] >> fs[]) *)
(*         >- (qunabbrev_tac `α` >> simp[]) *)


(*  >> qexists_tac `i` *)
(*                   >> Cases_on `(i ≤ g (f (SND (alph_counter N f g i))) i)` *)
(*                   >> fs[] >> first_assum (qspec_then `i` mp_tac) *)
(*                   >> rpt strip_tac >> `FST (alph_counter N f g i) = i` suffices_by metis_tac[DECIDE ``i<=i``] *)
(* ) *)


(* ) *)
(* ) *)


(*               >> `!a. (i <= a) ==> *)
(*                     (SND (alph_counter N f g (SUC a)) = *)
(*                       (if g (f (FST (alph_counter N f g i))) *)
(*                             (SND (alph_counter N f g a)) = a *)
(*                       then ((SND (alph_counter N f g a)) + 1) MOD N *)
(*                       else SND (alph_counter N f g a)))` by ( *)
(*                    Induct_on `a` >> rpt strip_tac >> fs[] *)
(*                    >- (PURE_REWRITE_TAC[DECIDE ``1 = SUC 0``] *)
(*                        >> simp[alph_counter_def] *)
(*                       ) *)
(*                    >- (Cases_on *)
(*                         `g (f (FST (alph_counter N f g i))) *)
(*                            (SND (alph_counter N f g (SUC a))) = SUC a` >> fs[] *)
(*                        >- (Cases_on `i = SUC a` >> fs[] >> rw[] *)
(*                            >- (PURE_REWRITE_TAC[alph_counter_def] >> metis_tac[] ) *)
(* ) *)


(* ) *)


(* ) *)


(* `?k. i <= k *)
(*                    ∧ (g (f (SND (alph_counter N f g k))) *)
(*                          (FST (alph_counter N f g k)) = k)` by ( *)
(*                 first_assum (qspec_then `f (SND (alph_counter N f g i))` mp_tac) *)
(*                 >> rpt strip_tac >>  *)

(* ) *)
(* ) *)

(* ) *)




(*        `!j. ~(SND (alph_counter N f g j) *)
(*               = SND (alph_counter N f g (j-1))) *)
(*             ==> (SND (alph_counter N f g j) *)
(*                  = (SND (alph_counter N f g (j-1)) + 1) MOD N)` by ( *)
(*            rpt strip_tac >> Cases_on `j = 0` >> rw[] >> fs[alph_counter_def] *)
(*            >> `?k. j = SUC k` by (Cases_on `j` >> fs[]) *)
(*            >> rw[] >> fs[alph_counter_def] *)
(*            >> Cases_on *)
(*                `g (f (SND (alph_counter N f g k))) *)
(*                            (FST (alph_counter N f g k)) = k` >> fs[] *)
(*        ) *)
(*     >> strip_tac >> CCONTR_TAC *)
(*     >> qabbrev_tac `P = λn. n < N ∧ !j. i <= j *)
(*                                       ==> ~(SND (alph_counter N f g j) = n)` *)
(*     >> qabbrev_tac `P_m = λn. P (N - n)` *)
(*     >> qabbrev_tac `n_max = $LEAST P_m` *)
(*     >> `P_m n_max ∧ !n. n < n_max ==> ~ P_m n` by ( *)
(*         `?l. P_m l` suffices_by metis_tac[LEAST_EXISTS] *)
(*         >> qunabbrev_tac `P_m` >> qunabbrev_tac `P` >> fs[] *)
(*         >> CCONTR_TAC >> fs[] *)
(*         >> `?p. N = n + p` by metis_tac[LESS_EQ_EXISTS,DECIDE ``n < N ==> n <= N``] *)
(*         >> `?p. n = N - p` by metis_tac[ADD_SUB,DECIDE``n + p - p = n``] *)
(*         >> `~(p' = 0)` by fs[] >> metis_tac[] *)
(*        ) *)
(*     >> Cases_on `n_max = 1` >> qunabbrev_tac `P` >> qunabbrev_tac `P_m` >> fs[] *)
(*     >> first_x_assum (qspec_then `n_max - 1` mp_tac) >> simp[] >> rpt strip_tac *)
(*     >- () *)


(*     >- (rw[] >> qunabbrev_tac `P` >> fs[] >> Induct_on `i` >> rpt strip_tac *)
(*         >> fs[] *)
(*         >- (first_x_assum (qspec_then `0` mp_tac) >> simp[alph_counter_def]) *)
(*         >- (Cases_on `SND (alph_counter N f g i) = 0` >> fs[] *)
(*             >- () *)
(* ) *)
(* ) *)


(*         `!i. ?j. i <= j *)
(*                ∧ (~(SND (alph_counter N f g j) *)
(*                      = SND (alph_counter N f g (j-1))))` suffices_by ( *)
(*             rpt strip_tac >> simp[alph_counter_def] *)
(* ) *)
(*         >> rpt strip_tac >> simp[] >> Cases_on `alph_counter N f g i` *)
(*         >> Cases_on `n < G` >> fs[] *)
(*         >- (first_x_assum qspec_then) *)

(* ) *)
(*     >> qexists_tac `α` >> simp[FORALL_AND_THM] >> rpt conj_tac *)

(*     >- (rpt strip_tac >> qunabbrev_tac `α` >> simp[] >> metis_tac[]) *)
(*     >- (rpt strip_tac >> qunabbrev_tac `α` >> simp[] >> metis_tac[]) *)
(*     >- (rpt strip_tac >> qunabbrev_tac `α` >> simp[] *)
(*         >>  *)
(* ) *)


(* Induct_on `i` >> qunabbrev_tac `α` >> simp[alph_counter_def] *)
(*       >- (`f 0 ∈ aut.accTrans` by metis_tac[DECIDE ``0 * N = 0``,MOD_EQ_0] *)
(*           >> metis_tac[] *)
(*          ) *)
(*       >- (p) *)


(* ) *)


(*     >- metis_tac[] *)
(*     >- metis_tac[DECIDE ``0 + 1 = 1``] *)
(*     >-  *)
(*    >- (`?k. i <= k ∧ (f (k MOD (N)) = T')` by ( *)
(*           CCONTR_TAC >> fs[] *)
(*           >> `?n. (f n = T') ∧ (n < N)` by ( *)
(*              POP_ASSUM mp_tac >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac *)
(*              >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac *)
(*              >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac *)
(*              >> metis_tac[] *)
(*           ) *)
(*           >> `?p. (i <= p) ∧ (p MOD (N) = n)` suffices_by ( *)
(*               rpt strip_tac >> metis_tac[] *)
(*           ) *)
(*           >> qexists_tac `i - (i MOD (N)) + n + N` *)
(*           >> simp[] >> rpt strip_tac *)
(*           >- (`i MOD (N) < N` by fs[] *)
(*               >> simp[]) *)
(*           >- (`n = (0 + n) MOD (N)` by simp[] *)
(*               >> `(i - (i MOD (N))) MOD (N) = 0` *)
(*                  by metis_tac[MOD_LEMM] *)
(*               >> metis_tac[ADD_MOD,MOD_EQ_0,DECIDE ``0 * n = 0``] *)
(*              ) *)
(*       ) *)
(*        >> qexists_tac `k` >> simp[] *)
(*        >> first_x_assum (qspec_then `T'` mp_tac) >> simp[] >> rpt strip_tac *)
(*        >>  *)


(* ) *)




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
