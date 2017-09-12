open HolKernel Parse bossLib boolLib pred_setTheory relationTheory set_relationTheory arithmeticTheory pairTheory listTheory optionTheory

val _ = new_theory "generalHelpers"

val NONEMPTY_LEMM = store_thm
  ("NONEMPTY_LEMM",
   ``!s. ~(s = {}) ==> ?e s'. (s = {e} ∪ s') /\ ~(e ∈ s')``,
   rpt strip_tac >> fs[] >> qexists_tac `CHOICE s`
   >> qexists_tac `s DIFF {CHOICE s}` >> strip_tac
     >- (`(s ⊆ {CHOICE s} ∪ (s DIFF {CHOICE s}))
        /\ ({CHOICE s} ∪ (s DIFF {CHOICE s}) ⊆ s)`
           suffices_by metis_tac[SET_EQ_SUBSET]
         >> strip_tac >> (fs[SUBSET_DEF,CHOICE_DEF]))
     >- simp[DIFF_DEF]
  );

val RRESTRICT_TRANS = store_thm
 ("RRESTRICT_TRANS",
  ``!s r. transitive r ==> transitive (rrestrict r s)``,
   rpt strip_tac >> fs[transitive_def, rrestrict_def]
   >> rpt strip_tac >> metis_tac[]
 );

val RRESTRICT_ANTISYM = store_thm
  ("RRESTRICT_ANTISYM",
  ``!s r. antisym r ==> antisym (rrestrict r s)``,
   rpt strip_tac >> fs[antisym_def, in_rrestrict]
  );

val ADD_N_INJ_LEMM = store_thm
  ("ADD_N_INJ_LEMM",
  ``!n x y. ((\x. x+n ) x = (\x. x+n) y) ==> (x = y)``,
  rpt strip_tac >> Induct_on `n` >> fs[]
  >> rw[ADD_SUC]
  );

val ADD_N_IMAGE_LEMM = store_thm
  ("ADD_N_IMAGE_LEMM",
  ``!n. IMAGE (\x. x+n) 𝕌(:num) = { x | x >= n }``,
  strip_tac >> fs[IMAGE_DEF]
  >> `({n + x | x | T} ⊆ {x | x ≥ n}) /\ ({x | x ≥ n} ⊆ {n + x | x | T})`
        suffices_by metis_tac[SET_EQ_SUBSET]
  >> rpt strip_tac >> fs[SUBSET_DEF]
  >> rpt strip_tac
  >> qexists_tac `x - n` >> simp[]
  );

val SUBS_UNION_LEMM = store_thm
  ("SUBS_UNION_LEMM",
  ``!s s1 s2. (s = s1) \/ (s = s2) ==> (s ⊆ s1 ∪ s2)``,
  rpt strip_tac >> metis_tac[SUBSET_UNION]
  );

val SUBS_UNION_LEMM2 = store_thm
  ("SUBS_UNION_LEMM2",
  ``!s s1 s2 s3. s ⊆ s1 ∪ s2 /\ s1 ⊆ s3 ==> s ⊆ s3 ∪ s2``,
  fs[UNION_DEF, SUBSET_DEF] >> rpt strip_tac
  >> `x ∈ s1 \/ x ∈ s2` by metis_tac[]
  >> metis_tac[]
  );

val INFINITE_DIFF_FINITE = store_thm
  ("INFINITE_DIFF_FINITE",
   ``!s t. INFINITE s ∧ FINITE t ==> INFINITE (s DIFF t)``,
   rpt strip_tac >> metis_tac[FINITE_DIFF_down]
  );

val INSERT_LEMM = store_thm
  ("INSERT_LEMM",
  ``!f q e s. {f q | q ∈ e INSERT s } = f e INSERT {f q | q ∈ s }``,
   fs[SET_EQ_SUBSET, SUBSET_DEF] >> rpt strip_tac
   >> metis_tac[]
  );

val NO_BOUNDS_INFINITE = store_thm
  ("NO_BOUNDS_INFINITE",
  ``!f. (!i. i <= f i)
  ==> INFINITE { f i | i ∈ 𝕌(:num) }``,
  rpt strip_tac >> fs[FINITE_WEAK_ENUMERATE]
  >> `linear_order (rrestrict (rel_to_reln $<=) {f' n | n < b }) {f' n | n < b }`
     by (fs[linear_order_def,rrestrict_def,rel_to_reln_def] >> rpt strip_tac
           >- (fs[domain_def, SUBSET_DEF] >> rpt strip_tac
               >> metis_tac[]
              )
           >- (fs[range_def, SUBSET_DEF] >> rpt strip_tac
                 >> metis_tac[])
           >- (fs[transitive_def, SUBSET_DEF] >> rpt strip_tac
                 >> metis_tac[])
           >- (fs[antisym_def, SUBSET_DEF] >> rpt strip_tac
                 >> metis_tac[])
        )
   >> `FINITE {f' n | n < b }` by (
      `FINITE {f' n | n ∈ count b }` suffices_by fs[IN_ABS,count_def]
      >> metis_tac[IMAGE_DEF,FINITE_COUNT,IMAGE_FINITE]
  )
   >> Cases_on `b = 0`
     >- (`~ !e. (?i. e = f i)` by fs[]
         >> fs[])
     >- (`~({f' n | n < b} = {})` by (
            `?x. x ∈ {f' n | n < b}` suffices_by fs[MEMBER_NOT_EMPTY]
            >> fs[] >> `b-1 < b` by simp[] >> metis_tac[]
           )
        >> `?x. x ∈ maximal_elements {f' n | n < b }
            (rrestrict (rel_to_reln $<=) {f' n | n < b })`
            by metis_tac[finite_linear_order_has_maximal]
        >> `(∃i. f (SUC x) = f i) ⇔ ∃n. n < b ∧ (f (SUC x) = f' n)` by fs[]
        >> `(∃i. f (SUC x) = f i)` by metis_tac[]
        >> `~?n. n < b ∧ (f (SUC x) = f' n)` suffices_by metis_tac[]
        >> fs[] >> rpt strip_tac
        >> CCONTR_TAC >> fs[]
        >> `SUC x <= f (SUC x)` by fs[]
        >> `f' n <= x` by (
           fs[maximal_elements_def, rrestrict_def, rel_to_reln_def]
           >> first_x_assum (qspec_then `f' n` mp_tac)
           >> rpt strip_tac >> fs[]
           >> CCONTR_TAC
           >> `x < f' n` by metis_tac[DECIDE ``~(f' n <= f' n') = (f' n' < f' n)``]
           >> `x = f' n` by metis_tac[DECIDE ``x < f' n ==> x <= f' n``]
           >> fs[]
        )
        >> fs[]
        )
  );

val FIXPOINT_EXISTS = store_thm
  ("FIXPOINT_EXISTS",
  ``!Rel f. WF Rel /\ (!y. (RC Rel) (f y) y)
                    ==> (!x. ?n. !m. (m >= n) ==> (FUNPOW f m x = FUNPOW f n x))``,
   rpt gen_tac >> strip_tac
    >> IMP_RES_THEN ho_match_mp_tac WF_INDUCTION_THM
    >> rpt strip_tac
    >> `Rel (f x) x \/ (f x = x)` by metis_tac[RC_DEF]
    >- (`∃n. ∀m. m ≥ n ⇒ (FUNPOW f m (f x) = FUNPOW f n (f x))` by metis_tac[]
        >> qexists_tac `SUC n` >> simp[FUNPOW] >> rpt strip_tac
        >> qabbrev_tac `FIX = FUNPOW f n (f x)`
        >> first_x_assum (qspec_then `SUC n` mp_tac) >> simp[FUNPOW_SUC]
        >> strip_tac >> Induct_on `m` >> simp[] >> strip_tac
        >> simp[FUNPOW_SUC]
        >> Cases_on `m = n`
           >- (rw[] >> metis_tac[FUNPOW, FUNPOW_SUC])
           >- (`m >= SUC n` by simp[] >> metis_tac[])
       )
    >- (exists_tac ``0`` >> simp[FUNPOW] >> Induct_on `m` >> simp[FUNPOW])
  );

val char_def = Define `char Σ p = { a | (a ∈ Σ) /\ (p ∈ a)}`;

val char_neg_def = Define `char_neg Σ p = Σ DIFF (char Σ p)`;

val d_conj_def = Define
  `d_conj d1 d2 = { (a1 ∩ a2, e1 ∪ e2) | ((a1,e1) ∈ d1) /\ ((a2,e2) ∈ d2)}`;

val d_conj_set_def = Define`
  d_conj_set ts Σ = ITSET (d_conj o SND) ts {(Σ, {})}`;

val D_CONJ_UNION_DISTR = store_thm
  ("D_CONJ_UNION_DISTR",
  ``!s t d. d_conj s (t ∪ d) = (d_conj s t) ∪ (d_conj s d)``,
   rpt strip_tac >> fs[d_conj_def] >> rw[SET_EQ_SUBSET]
   >> fs[SUBSET_DEF] >> rpt strip_tac >> metis_tac[]
                             );
val D_CONJ_FINITE = store_thm
  ("D_CONJ_FINITE",
   ``!s d. FINITE s ∧ FINITE d ==> FINITE (d_conj s d)``,
   rpt gen_tac
   >> `d_conj s d = {(a1 ∩ a2, e1 ∪ e2) | ((a1,e1),a2,e2) ∈ s × d}`
       by fs[CROSS_DEF, FST, SND, d_conj_def]
   >> rpt strip_tac
   >> qabbrev_tac `f = (λ((a1,e1),(a2,e2)). (a1 ∩ a2, e1 ∪ e2))`
   >> `d_conj s d = {f ((a1,e1),a2,e2) | ((a1,e1),a2,e2) ∈ s × d}` by (
        qunabbrev_tac `f` >> fs[SET_EQ_SUBSET, SUBSET_DEF] >> rpt strip_tac
        >> fs[] >> metis_tac[]
    )
   >> `FINITE (s × d)` by metis_tac[FINITE_CROSS]
   >> `d_conj s d = IMAGE f (s × d)` by (
        fs[IMAGE_DEF] >> fs[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
         >- metis_tac[FST,SND]
         >- (Cases_on `x'` >> Cases_on `q` >> Cases_on `r`
             >> qunabbrev_tac `f`
             >> qexists_tac `q'` >> qexists_tac `q` >> qexists_tac `r'`
             >> qexists_tac `r''` >> fs[]
            )
    )
   >> metis_tac[IMAGE_FINITE]
  );

val D_CONJ_ASSOC = store_thm
  ("D_CONJ_ASSOC",
  ``!s d t. d_conj s (d_conj d t) = d_conj (d_conj s d) t``,
  simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> fs[d_conj_def]
  >> metis_tac[INTER_ASSOC,UNION_ASSOC]
  );

val D_CONJ_COMMUTES = store_thm
  ("D_CONJ_COMMUTES",
  ``!s d t. d_conj s (d_conj d t) = d_conj d (d_conj s t)``,
  simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> fs[d_conj_def]
    >- (qexists_tac `a1'` >> qexists_tac `a1 ∩ a2'`
        >> qexists_tac `e1'` >> qexists_tac `e1 ∪ e2'`
        >> rpt strip_tac
          >- metis_tac[INTER_COMM, INTER_ASSOC]
          >- metis_tac[UNION_COMM, UNION_ASSOC]
          >- metis_tac[]
          >- metis_tac[]
       )
    >- (qexists_tac `a1'` >> qexists_tac `a1 ∩ a2'`
        >> qexists_tac `e1'` >> qexists_tac `e1 ∪ e2'`
        >> rpt strip_tac
          >- metis_tac[INTER_COMM, INTER_ASSOC]
          >- metis_tac[UNION_COMM, UNION_ASSOC]
          >- metis_tac[]
          >- metis_tac[]
       )
  );

val D_CONJ_SND_COMMUTES = store_thm
  ("D_CONJ_SND_COMMUTES",
  ``!s d t. (d_conj o SND) s ((d_conj o SND) d t)
          = (d_conj o SND) d ((d_conj o SND) s t)``,
  rpt strip_tac >> fs[SND] >> metis_tac[D_CONJ_COMMUTES]
  );

val D_CONJ_SET_RECURSES = store_thm
  ("D_CONJ_SET_RECURSES",
  ``!s. FINITE s ==>
      ∀e b. ITSET (d_conj o SND) (e INSERT s) b =
                          (d_conj o SND) e (ITSET (d_conj o SND) (s DELETE e) b)``,
  rpt strip_tac
  >> HO_MATCH_MP_TAC COMMUTING_ITSET_RECURSES
  >> metis_tac[D_CONJ_SND_COMMUTES]
  );

val D_CONJ_SET_LEMM = store_thm
  ("D_CONJ_SET_LEMM",
  ``!A s. FINITE s ==> !a e.(a,e) ∈ d_conj_set s A
           ==> (!q d. (q,d) ∈ s ==> ?a' e'. (a',e') ∈ d ∧ a ⊆ a' ∧ e' ⊆ e)``,
  gen_tac >> Induct_on `s` >> rpt strip_tac >> fs[NOT_IN_EMPTY]
  >> `(a,e') ∈ (d_conj o SND) e (d_conj_set s A)` by (
      fs[d_conj_set_def, DELETE_NON_ELEMENT]
      >> `(a,e') ∈ (d_conj o SND) e (ITSET (d_conj ∘ SND) s {(A,∅)})` suffices_by fs[]
      >> metis_tac[D_CONJ_SET_RECURSES]
  )
    >- (fs[d_conj_def] >> first_x_assum (qspec_then `a2` mp_tac)
        >> rpt strip_tac >> first_x_assum (qspec_then `e2` mp_tac)
        >> rpt strip_tac >> fs[]
        >> `∀q d. (q,d) ∈ s ⇒ ∃a' e'. (a',e') ∈ d ∧ a2 ⊆ a' ∧ e' ⊆ e2` by (
             rpt strip_tac >> metis_tac[]
         )
        >> qexists_tac `a1` >> qexists_tac `e1` >> fs[SND] >> metis_tac[SND]
       )
    >- (fs[d_conj_def]
        >> `∃a' e'. (a',e') ∈ d ∧ a2 ⊆ a' ∧ e' ⊆ e2` by metis_tac[]
        >> qexists_tac `a'` >> qexists_tac `e''`
        >> metis_tac[SUBSET_DEF,IN_INTER,IN_UNION]
        )
  );

val D_CONJ_SET_LEMM2 = store_thm
  ("D_CONJ_SET_LEMM2",
  ``!A s a e. FINITE s ∧ (a,e) ∈ d_conj_set s A
     ==> (!q d. (q,d) ∈ s ==> ?a' e'. (a',e') ∈ d ∧ a ⊆ a' ∧ e' ⊆ e)``,
  rpt strip_tac >> metis_tac[D_CONJ_SET_LEMM]
  );

val CAT_OPTIONS_def = Define`
   (CAT_OPTIONS [] = [])
 ∧ (CAT_OPTIONS (SOME v::ls) = v::(CAT_OPTIONS ls))
 ∧ (CAT_OPTOINS (NONE::ls) = CAT_OPTIONS ls)`;

val OPTION_TO_LIST_def = Define`
    (OPTION_TO_LIST NONE = [])
  ∧ (OPTION_TO_LIST (SOME l) = l)`;

val LIST_INTER_def = Define`
    (LIST_INTER [] ls = [])
  ∧ (LIST_INTER (x::xs) ls = if MEM x ls
                             then x::(LIST_INTER xs ls)
                             else LIST_INTER xs ls)`;

val _ = export_theory();
