open HolKernel Parse bossLib boolLib pred_setTheory relationTheory set_relationTheory arithmeticTheory pairTheory listTheory optionTheory prim_recTheory whileTheory rich_listTheory sortingTheory

(* open relationTheoryHelperTheory *)

val _ = new_theory "generalHelpers"
val _ = ParseExtras.temp_loose_equality()

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

val POW_11 = store_thm
  ("POW_11",
   ``!s1 s2. (POW s1 = POW s2) = (s1 = s2)``,
   simp[EQ_IMP_THM] >> fs[]
   >> `∀s1 s2. (POW s1 = POW s2) ⇒ s1 ⊆ s2` suffices_by metis_tac[SET_EQ_SUBSET]
   >> fs[SET_EQ_SUBSET,SUBSET_DEF,POW_DEF] >> rpt strip_tac
   >> `(∀x'. x' ∈ {x} ⇒ x' ∈ s1) ⇒ ∀x'. x' ∈ {x} ⇒ x' ∈ s2` by metis_tac[]
   >> `∀x'. x' ∈ {x} ⇒ x' ∈ s2` by (
         `(∀x'. x' ∈ {x} ⇒ x' ∈ s1)` suffices_by metis_tac[]
         >> simp[]
   )
   >> fs[]
  );

val IN_BIGINTER_SUBSET = store_thm
  ("IN_BIGINTER_SUBSET",
   ``!x P. (x ∈ P) ==> (BIGINTER P ⊆ x)``,
   rpt strip_tac
   >> `x INSERT P = P` by simp[SET_EQ_SUBSET,SUBSET_DEF]
   >> `x ∩ BIGINTER P = BIGINTER P` by metis_tac[BIGINTER_INSERT]
   >> metis_tac[INTER_SUBSET]
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

val CHAR_LEMM = store_thm
  ("CHAR_LEMM",
   ``!Σ x. char Σ x ⊆ Σ``,
   fs[char_def,SUBSET_DEF] >> rpt strip_tac
  );

val CHAR_NEG_LEMM = store_thm
  ("CHAR_NEG_LEMM",
   ``!Σ x. char_neg Σ x ⊆ Σ``,
   fs[char_neg_def,DIFF_SUBSET]
  );

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

(* val D_CONJ_SET_SND = store_thm *)
(*   ("D_CONJ_SET_SND", *)
(*    ``!aP s1. FINITE s1 ==> *)
(*               !s2. FINITE s2 ==> *)
(*                 ((IMAGE SND s1 = IMAGE SND s2) ∧ FINITE s1 ∧ FINITE s2 *)
(*                   ==> (d_conj_set s1 aP = d_conj_set s2 aP))``, *)
(*    gen_tac >> Induct_on `s1` >> fs[] >> rpt strip_tac *)
(*    >- (`s2 = {}` by metis_tac[IMAGE_EQ_EMPTY] >> fs[d_conj_set_def,ITSET_THM]) *)
(*    >- (`IMAGE SND s1 ⊆ IMAGE SND s2` by ( *)
(*         rw[] >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac *)
(*         >> simp[INSERT_DEF] >> rpt strip_tac >> simp[SUBSET_DEF] *)
(*         >> rpt strip_tac *)
(*         >> `x ∈ {y | y = SND e ∨ ∃x. y = SND x ∧ x ∈ s1}` by ( *)
(*             fs[] >> disj2_tac >> metis_tac[] *)
(*         ) *)
(*         >> `x ∈ IMAGE SND s2` by metis_tac[SET_EQ_SUBSET,SUBSET_DEF] *)
(*         >> fs[IMAGE_DEF] >> metis_tac[] *)
(*        ) *)
(*        >> `IMAGE SND s2 ⊆ IMAGE SND s1 ∪ {SND e}` by ( *)
(*           rw[] >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac *)
(*           >> PURE_REWRITE_TAC[INSERT_DEF] >> rpt strip_tac *)
(*           >> simp[SUBSET_DEF] >> rpt strip_tac *)
(*           >> `x ∈ IMAGE SND s2` by (simp[] >> metis_tac[]) *)
(*           >> `x ∈ {y | y = SND e ∨ y ∈ IMAGE SND s1}` *)
(*               by metis_tac[SET_EQ_SUBSET,SUBSET_DEF] *)
(*           >> fs[] >> disj1_tac >> metis_tac[] *)
(*        ) *)
(*        >> fs[d_conj_set_def] >> simp[D_CONJ_SET_RECURSES] *)
(*        >> Cases_on `SND e ∈ IMAGE SND s1` *)
(*        >- ( *)
(*          `IMAGE SND s1 = IMAGE SND s2` by ( *)
(*              simp[IMAGE_DEF] *)
(*              >> `{SND x | x ∈ s1} ⊆ {SND x | x ∈ s2} *)
(*                ∧ {SND x | x ∈ s2} ⊆ {SND x | x ∈ s1}` *)
(*                   suffices_by metis_tac[SET_EQ_SUBSET] *)
(*              >> simp[SUBSET_DEF] >> rpt strip_tac *)
(*              >- (`x ∈ IMAGE SND s1` by (simp[] >> metis_tac[]) *)
(*                  >> `x ∈ IMAGE SND s2` by metis_tac[SUBSET_DEF] *)
(*                  >> fs[] >> metis_tac[] *)
(*                 ) *)
(*              >- (`x ∈ IMAGE SND s2` by (simp[] >> metis_tac[]) *)
(*                  >> `x ∈ IMAGE SND s1 ∪ {SND e}` by metis_tac[SUBSET_DEF] *)
(*                  >> fs[UNION_DEF] >> metis_tac[] *)
(*                 ) *)
(*          ) *)
(*          >> `?x. x ∈ s1 ∧ SND x = SND e ∧ ~(x = e)` by ( *)
(*              fs[IMAGE_DEF] >> metis_tac[] *)
(*          ) *)
(*          >> `IMAGE SND (s1 DELETE e) = IMAGE SND s1` by ( *)
(*              simp[IMAGE_DEF] *)
(*          ) *)
(*          >>  *)
(*        >> `(IMAGE SND s2) DELETE (SND e) = IMAGE SND s1` by ( *)
(*             simp[DELETE_DEF] *)
(*             >> `IMAGE SND s2 DIFF {SND e} ⊆ IMAGE SND s1 *)
(*                 ∧ IMAGE SND s1 ⊆ IMAGE SND s2 DIFF {SND e}` *)
(*                 suffices_by fs[SET_EQ_SUBSET] *)
(*             >> simp[SUBSET_DEF] >> rpt strip_tac *)
(*             >- (rw[] *)
(*                 >> `SND x' ∈ IMAGE SND s1` by ( *)
(*                    `IMAGE SND s2 ⊆ SND e INSERT IMAGE SND s1` *)
(*                       by metis_tac[SET_EQ_SUBSET] *)
(*                    >> `SND x' ∈ IMAGE SND s2` by simp[IMAGE_DEF] *)
(*                    >> `SND x' ∈ SND e INSERT IMAGE SND s1` *)
(*                        by metis_tac[SUBSET_DEF] *)
(*                    >> `~(SND x' = SND e)` by fs[] *)
(*                    >> POP_ASSUM mp_tac >> simp[INSERT_DEF] *)
(*                  ) *)
(*                 >> fs[IMAGE_DEF] >> metis_tac[] *)
(*                ) *)
(*             >- (`IMAGE SND s1 ⊆ IMAGE SND s2` by ( *)
(*                  rw[] >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac *)
(*                  >> simp[INSERT_DEF] >> rpt strip_tac >> simp[SUBSET_DEF] *)
(*                  >> rpt strip_tac *)
(*                  >> `x ∈ {y | y = SND e ∨ ∃x. y = SND x ∧ x ∈ s1}` by ( *)
(*                       fs[] >> disj2_tac >> metis_tac[] *)
(*                  ) *)
(*                  >> `x ∈ IMAGE SND s2` by metis_tac[SET_EQ_SUBSET,SUBSET_DEF] *)
(*                  >> fs[IMAGE_DEF] >> metis_tac[] *)
(*                 ) *)
(*                 >> `x ∈ IMAGE SND s1` by (simp[IMAGE_DEF] >> metis_tac[]) *)
(*                 >> `x ∈ IMAGE SND s2` by metis_tac[SUBSET_DEF] *)
(*                 >> fs[IMAGE_DEF] >> metis_tac[] *)
(*                ) *)
(*             >- (rw[] >> ) *)



(*                          ) *)



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

val D_CONJ_SET_LEMM2_STRONG = store_thm
  ("D_CONJ_SET_LEMM2_STRONG",
  ``!A s. FINITE s
      ==> !a e. (a,e) ∈ d_conj_set s A
        ==> (?f_a f_e. !q d.
           ((q,d) ∈ s ==> (f_a q d,f_e q d) ∈ d ∧ a ⊆ f_a q d ∧ f_e q d ⊆ e)
         ∧ (A ∩ BIGINTER {f_a q d | (q,d) ∈ s } = a)
         ∧ (BIGUNION {f_e q d | (q,d) ∈ s } = e))``,
  gen_tac >> Induct_on `s` >> rpt strip_tac
  >- (fs[NOT_IN_EMPTY,d_conj_set_def,ITSET_THM])
  >- (rename[`(a,e1) ∈ d_conj_set (e INSERT s) A`]
      >> fs[d_conj_set_def]
      >> `s DELETE e = s` by (simp[SET_EQ_SUBSET,SUBSET_DEF])
      >> `(a,e1) ∈
            (d_conj ∘ SND) e (ITSET (d_conj ∘ SND) (s DELETE e) {A,{}})`
           by metis_tac[D_CONJ_SET_RECURSES]
      >> fs[d_conj_def] >> rw[]
      >> first_x_assum (qspec_then `a2` mp_tac) >> rpt strip_tac
      >> first_x_assum (qspec_then `e2` mp_tac)
      >> `(a2,e2) ∈ ITSET (d_conj ∘ SND) s {(A,∅)}` by metis_tac[]
      >> simp[] >> rpt strip_tac
      >> qabbrev_tac `f_a2 =
           λq d. if (q,d) = e then a1 else f_a q d`
      >> qabbrev_tac `f_e2 =
           λq d. if (q,d) = e then e1' else f_e q d`
      >> qexists_tac `f_a2` >> qexists_tac `f_e2` >> fs[] >> rpt strip_tac
      >> qunabbrev_tac `f_a2` >> qunabbrev_tac `f_e2` >> rw[] >> fs[]
      >> first_x_assum (qspec_then `q` mp_tac) >> rpt strip_tac
      >> first_x_assum (qspec_then `d` mp_tac) >> simp[] >> rpt strip_tac
      >> fs[] >> rw[]
      >- metis_tac[INTER_SUBSET,INTER_ASSOC,SUBSET_TRANS]
      >- metis_tac[SUBSET_UNION,SUBSET_TRANS]
      >- (`{if (q,d) = e
            then a1
            else f_a q d | (q,d) | ((q,d) = e) ∨ ((q,d) ∈ s)} =
           {f_a q d | (q,d) ∈ s} ∪ {a1}` by (
         simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> fs[]
         >- metis_tac[]
         >- metis_tac[]
         >- (qexists_tac `FST e` >> qexists_tac `SND e` >> fs[])
         )
         >> rw[] >> metis_tac[INTER_ASSOC,INTER_COMM]
         )
      >- (`{if (q,d) = e
            then e1'
            else f_e q d | (q,d) | ((q,d) = e) ∨ ((q,d) ∈ s)} =
            {f_e q d | (q,d) ∈ s} ∪ {e1'}` by (
         simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> fs[]
         >- metis_tac[]
         >- metis_tac[]
         >- (qexists_tac `FST e` >> qexists_tac `SND e` >> fs[])
         )
         >> rw[] >> metis_tac[UNION_COMM]
         )
     )
  );

val D_CONJ_SET_LEMM3 = store_thm
  ("D_CONJ_SET_LEMM3",
   ``!s A a a' e'. FINITE s
        ∧ (!q d. (q,d) ∈ s ==> (a' q,e' q) ∈ d ∧ a ⊆ a' q)
        ∧ (a ⊆ A)
     ==> (A ∩ BIGINTER {a' q | q ∈ IMAGE FST s },
          BIGUNION {e' q | q ∈ IMAGE FST s})
                      ∈ d_conj_set s A``,
    `!s. FINITE (s:α # ((β -> bool) # (γ -> bool) -> bool) -> bool)
        ==>
         (!A a a' e'. (!q d. (q,d) ∈ s  ==> (a' q,e' q) ∈ d ∧ a ⊆ a' q)
                  ∧ (a ⊆ A)
          ==> (A ∩ BIGINTER {a' q | q ∈ IMAGE FST s },
               BIGUNION {e' q | q ∈ IMAGE FST s}) ∈ d_conj_set s A)`
    suffices_by metis_tac[]
    >> Induct_on `s` >> rpt strip_tac >> fs[]
     >- fs[d_conj_set_def,ITSET_THM]
     >- (`(A ∩ BIGINTER {a' q | ?x. (q = FST x) ∧ x ∈ s},
           BIGUNION {e' q | ?x. (q = FST x) ∧ x ∈ s}) ∈ d_conj_set s A`
            by metis_tac[]
         >> simp[d_conj_set_def]
         >> `s DELETE e = s` by fs[DELETE_NON_ELEMENT_RWT]
         >> imp_res_tac D_CONJ_SET_RECURSES
         >> first_x_assum (qspec_then `e` mp_tac) >> rpt strip_tac
         >> first_x_assum (qspec_then `{(A,{})}` mp_tac)
         >> rpt strip_tac >> fs[] >> fs[d_conj_set_def]
         >> simp[d_conj_def] >> qexists_tac `a' (FST e)`
         >> qexists_tac `A ∩ BIGINTER {a' q | q ∈ IMAGE FST s }`
         >> qexists_tac `e' (FST e)`
         >> qexists_tac `BIGUNION {e' q | q ∈ IMAGE FST s }`
         >> rpt strip_tac
         >> simp[IN_IMAGE] >> dsimp[] >> simp[SET_EQ_SUBSET,SUBSET_DEF,IN_BIGINTER]
         >> rpt strip_tac >> metis_tac[]
        )
  );

val MEM_SUBSET_def = Define`
    (MEM_SUBSET [] l = T)
  ∧ (MEM_SUBSET (h::ls) l = (MEM h l ∧ MEM_SUBSET ls l))`;

val MEM_SUBSET_SET_TO_LIST = store_thm
  ("MEM_SUBSET_SET_TO_LIST",
   ``!l1 l2. MEM_SUBSET l1 l2 = (set l1 ⊆ set l2)``,
   Induct_on `l1` >> fs[MEM_SUBSET_def] >> rpt strip_tac
  );

val MEM_SUBSET_REFL = store_thm
  ("MEM_SUBSET_REFL",
   ``!l. MEM_SUBSET l l``,
   Induct_on `l` >> fs[MEM_SUBSET_def] >> rpt strip_tac
   >> metis_tac[MEM_SUBSET_SET_TO_LIST,SUBSET_DEF,MEM]
  );

val MEM_SUBSET_APPEND = store_thm
  ("MEM_SUBSET_APPEND",
   ``!l1 l2. MEM_SUBSET l1 (l1++l2)
           ∧ MEM_SUBSET l2 (l1++l2)``,
   rpt strip_tac
   >> metis_tac[MEM_SUBSET_SET_TO_LIST,SUBSET_DEF,MEM,MEM_APPEND]
  );

val MEM_SUBSET_TRANS = store_thm
  ("MEM_SUBSET_TRANS",
   ``!l1 l2 l3. MEM_SUBSET l1 l2 ∧ MEM_SUBSET l2 l3 ==> MEM_SUBSET l1 l3``,
   metis_tac[MEM_SUBSET_SET_TO_LIST,SUBSET_TRANS]
  );

val MEM_EQUAL_def = Define`
  (MEM_EQUAL l1 l2 = (MEM_SUBSET l1 l2 ∧ MEM_SUBSET l2 l1))`;

val MEM_EQUAL_SET = store_thm
  ("MEM_EQUAL_SET",
   ``!l1 l2. MEM_EQUAL l1 l2 = (set l1 = set l2)``,
   metis_tac[MEM_SUBSET_SET_TO_LIST,SET_EQ_SUBSET,MEM_EQUAL_def]
  );

val SET_OF_SUBLISTS_FINITE = store_thm
  ("SET_OF_SUBLISTS_FINITE",
   ``!l. FINITE {qs | MEM_SUBSET qs l ∧ ALL_DISTINCT qs }``,
      Induct_on `l`
      >- (`{qs | MEM_SUBSET qs [] ∧ ALL_DISTINCT qs} = {[]}` by (
           simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
           >> fs[MEM_EQUAL_def,MEM_SUBSET_def,MEM_SUBSET_SET_TO_LIST]
           ) >> rw[]
         )
      >- (rpt strip_tac >> fs[MEM_SUBSET_SET_TO_LIST]
          >> `!k s. k ∈ s ==> (k INSERT s = s)` by (
               rpt strip_tac >> simp[INSERT_DEF,SET_EQ_SUBSET,SUBSET_DEF]
           )
          >> Cases_on `MEM h l` >> fs[]
          >> qabbrev_tac `A = {qs | set qs ⊆ set l ∧ ALL_DISTINCT qs}`
          >> Q.HO_MATCH_ABBREV_TAC `FINITE B`
          >> `B = A ∪ {l1 ++ [h] ++ l2 | (l1++l2) ∈ A }` by (
             simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
             >> qunabbrev_tac `A` >> qunabbrev_tac `B` >> fs[]
             >- (Cases_on `set x ⊆ set l` >> fs[]
                 >> `!k a. MEM a k ∧ ALL_DISTINCT k
                           ==> ?k1 k2. (k = k1 ++ [a] ++ k2)
                                     ∧ ~MEM a k1 ∧ ~MEM a k2` by (
                    Induct_on `k` >> fs[] >> rpt strip_tac
                    >- (rw[] >> qexists_tac `[]` >> fs[])
                    >- (rw[] >> first_x_assum (qspec_then `a` mp_tac)
                        >> simp[] >> rpt strip_tac
                        >> qexists_tac `h'::k1` >> fs[]
                       )
                  )
                 >> `MEM h x` by (
                     `?k. k ∈ set x ∧ ~(k ∈ set l)` by metis_tac[SUBSET_DEF]
                     >> fs[SUBSET_DEF] >> metis_tac[]
                  )
                 >> first_x_assum (qspec_then `x` mp_tac) >> rpt strip_tac
                 >> first_x_assum (qspec_then `h` mp_tac) >> simp[]
                 >> rpt strip_tac >> qexists_tac `k1` >> qexists_tac `k2`
                 >> fs[ALL_DISTINCT_APPEND] >> fs[SUBSET_DEF] >> metis_tac[]
                )
             >- fs[SUBSET_DEF]
             >- (fs[ALL_DISTINCT_APPEND] >> rpt strip_tac >> fs[SUBSET_DEF]
                 >> metis_tac[]
                )
           )
          >> `!P. FINITE P ==> FINITE {l1 ⧺ [h] ⧺ l2 | l1 ⧺ l2 ∈ P}` by (
               HO_MATCH_MP_TAC FINITE_INDUCT >> rpt strip_tac >> fs[]
               >> `!k. FINITE {l1 ++ [h] ++ l2 | l1 ++ l2 = k }` by (
                   Induct_on `k` >> fs[]
                   >- (`{l1 ++ [h] ++ l2 | (l1 = []) ∧ (l2 = []) } = { [h] }` by (
                          simp[SET_EQ_SUBSET,SUBSET_DEF]
                       )
                       >> rw[]
                      )
                   >- (rpt strip_tac
                       >> `{l1 ⧺ [h] ⧺ l2 | l1 ⧺ l2 = h'::k} =
                             (h::h'::k) INSERT
                                      {h'::a | a ∈
                                                 {l1 ⧺ [h] ⧺ l2 | l1 ⧺ l2 = k}}`
                          by (simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                              >- (Cases_on `l1` >> fs[] >> disj2_tac
                                  >> metis_tac[])
                              >- (qexists_tac `[]` >> fs[])
                              >- (rw[] >> qexists_tac `h'::l1` >> fs[])
                             )
                       >> `FINITE {h'::a | a ∈ {l1 ⧺ [h] ⧺ l2 | l1 ⧺ l2 = k}}`
                           suffices_by metis_tac[FINITE_INSERT]
                       >> `{h'::a | a ∈ {l1 ⧺ [h] ⧺ l2 | l1 ⧺ l2 = k}}
                           = IMAGE (λx. h'::x) {l1 ⧺ [h] ⧺ l2 | l1 ⧺ l2 = k}`
                           by fs[IMAGE_DEF]
                       >> metis_tac[IMAGE_FINITE]
                      )
               )
               >> `{l1 ⧺ [h] ⧺ l2 | (l1 ⧺ l2 = e) ∨ l1 ⧺ l2 ∈ P}
                    = {l1 ⧺ [h] ⧺ l2 | (l1 ⧺ l2 = e)}
                          ∪ {l1 ⧺ [h] ⧺ l2 | l1 ⧺ l2 ∈ P}` by (
                   simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                   >> metis_tac[]
               )
               >> metis_tac[FINITE_UNION]
           )
          >> metis_tac[FINITE_UNION]
         )
  );

val NUB_NUB = store_thm
  ("NUB_NUB",
   ``!l. nub (nub l) = nub l``,
   Induct_on `l` >> fs[nub_def] >> rpt strip_tac
   >> Cases_on `MEM h l` >> fs[nub_def]
  );

val ALL_DISTINCT_SAME_NUB = store_thm
  ("ALL_DISTINCT_SAME_NUB",
   ``!l. ALL_DISTINCT l ==> (l = nub l)``,
   Induct_on `l` >> fs[nub_def]
  );

val ALL_DISTINCT_PAIRS_LEMM = store_thm
  ("ALL_DISTINCT_PAIRS_LEMM",
   ``(!x y1 y2 l.
     (ALL_DISTINCT (MAP FST l) ∧ (MEM (x,y1) l) ∧ (MEM (x,y2) l)
     ==> (y1 = y2)))
     ∧ (!x y1 y2 l.
         (ALL_DISTINCT (MAP SND l) ∧ (MEM (y1,x) l) ∧ (MEM (y2,x) l)
                     ==> (y1 = y2)))``,
   strip_tac >> Induct_on `l` >> fs[ALL_DISTINCT] >> rpt strip_tac
   >- (Cases_on `h` >> fs[])
   >- (fs[MEM_MAP] >> Cases_on `h` >> fs[] >> rw[]
       >> first_x_assum (qspec_then `(q,y2)` mp_tac) >> fs[])
   >- (fs[MEM_MAP] >> Cases_on `h` >> fs[] >> rw[]
       >> first_x_assum (qspec_then `(q,y1)` mp_tac) >> fs[])
   >- metis_tac[]
   >- (Cases_on `h` >> fs[])
   >- (fs[MEM_MAP] >> Cases_on `h` >> fs[] >> rw[]
         >> first_x_assum (qspec_then `(y2,r)` mp_tac) >> fs[])
   >- (fs[MEM_MAP] >> Cases_on `h` >> fs[] >> rw[]
         >> first_x_assum (qspec_then `(y1,r)` mp_tac) >> fs[])
   >- metis_tac[]
  );

val FOLDR_INTER = store_thm
  ("FOLDR_INTER",
   ``!f A l.
  (!x. MEM x l
       ==> (FOLDR (λa sofar. f a ∩ sofar) A l
                  ⊆ f x))
  ∧ (FOLDR (λa sofar. f a ∩ sofar) A l
           ⊆ A)``,
   Induct_on `l` >> rpt strip_tac >> fs[]
   >> metis_tac[INTER_SUBSET,SUBSET_TRANS]
  );

val FOLDR_APPEND_LEMM = store_thm
  ("FOLDR_APPEND_LEMM",
   ``!f A l.
  (!x. MEM x l
       ==> MEM_SUBSET (f x) (FOLDR (λa sofar. f a ++ sofar) A l))
  ∧ (MEM_SUBSET A (FOLDR (λa sofar. f a ++ sofar) A l))
  ∧ (set (FOLDR (λa sofar. f a ++ sofar) A l) =
     set A ∪ BIGUNION {set (f a) | MEM a l })``,
   Induct_on `l` >> rpt strip_tac >> fs[]
   >- fs[MEM_SUBSET_REFL]
   >- fs[MEM_SUBSET_APPEND]
   >- metis_tac[MEM_SUBSET_APPEND,MEM_SUBSET_TRANS]
   >- metis_tac[MEM_SUBSET_APPEND,MEM_SUBSET_TRANS]
   >- (simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> fs[]
       >> metis_tac[]
      )
  );

val FOLDR_LEMM5 = store_thm
  ("FOLDR_LEMM5",
   ``!l1 l2 l3 l4 f1 f2 s.
      (FOLDR (λa sofar. f1 a ∩ sofar)
             (FOLDR (λa sofar. f2 a ∩ sofar) s (l1++l2)) (l3++l4))
       = ((FOLDR (λa sofar. f1 a ∩ sofar)
                 (FOLDR (λa sofar. f2 a ∩ sofar) s l1) l3)
              ∩ ((FOLDR (λa sofar. f1 a ∩ sofar)
                        (FOLDR (λa sofar. f2 a ∩ sofar) s l2) l4)))``,
   Induct_on `l3` >> simp[SET_EQ_SUBSET,SUBSET_DEF]
   >> rpt strip_tac >> fs[]
   >> Induct_on `l4`
   >> Induct_on `l1` >> fs[] >> Induct_on `l2` >> fs[]
  );

val FOLDR_INTER_MEMEQUAL = store_thm
  ("FOLDR_INTER_MEMEQUAL",
   ``!l1 l2 s f. (set l1 = set l2)
               ==> (FOLDR (λa sofar. f a ∩ sofar) s l1 =
                     FOLDR (λa sofar. f a ∩ sofar) s l2)``,
   `!l1 l2 s f. (MEM_SUBSET l1 l2)
               ==> (FOLDR (λa sofar. f a ∩ sofar) s l2
                          ⊆ FOLDR (λa sofar. f a ∩ sofar) s l1)`
   suffices_by metis_tac[SET_EQ_SUBSET,SUBSET_DEF,MEM_SUBSET_SET_TO_LIST]
   >> Induct_on `l1`
   >- (rpt strip_tac >> fs[MEM_SUBSET_def,FOLDR_INTER])
   >- (rpt strip_tac >> simp[FOLDR] >> fs[MEM_SUBSET_def]
       >> metis_tac[FOLDR_INTER]
      )
  );

val ZIP_MAP = store_thm
  ("ZIP_MAP",
   ``!l. ZIP (MAP FST l, MAP SND l) = l``,
   Induct_on `l` >> fs[ZIP]
  );

val MAP_LEMM = store_thm
  ("MAP_LEMM",
   ``!l f h a. ~MEM h l
             ==> (MAP (λq. if q = h then a else f q) l = MAP f l)``,
   Induct_on `l` >> rpt strip_tac >> fs[]
  );

val CAT_OPTIONS_def = Define`
   (CAT_OPTIONS [] = [])
 ∧ (CAT_OPTIONS (SOME v::ls) = v::(CAT_OPTIONS ls))
 ∧ (CAT_OPTIONS (NONE::ls) = CAT_OPTIONS ls)`;

val CAT_OPTIONS_MEM = store_thm
  ("CAT_OPTIONS_MEM",
   ``!x l. (MEM x (CAT_OPTIONS l)) = (?y. (SOME x = y) ∧ MEM y l)``,
   Induct_on `l` >> rpt strip_tac >> fs[CAT_OPTIONS_def]
   >> Cases_on `h` >> fs[CAT_OPTIONS_def]
  );

val CAT_OPTIONS_MAP_LEMM = store_thm
  ("CAT_OPTIONS_MAP_LEMM",
   ``!i f ls. MEM i (CAT_OPTIONS (MAP f ls))
  = ?x. MEM x ls ∧ (SOME i = f x)``,
   Induct_on `ls` >> fs[CAT_OPTIONS_def,MAP]
   >> rpt strip_tac >> Cases_on `f h` >> simp[EQ_IMP_THM]
   >> rw[] >> fs[CAT_OPTIONS_def] >> metis_tac[SOME_11,NOT_SOME_NONE]
  );

val CAT_OPTIONS_APPEND = store_thm
  ("CAT_OPTIONS_APPEND",
   ``!l1 l2. CAT_OPTIONS (l1 ++ l2) = CAT_OPTIONS l1 ++ CAT_OPTIONS l2``,
   Induct_on `l1` >> fs[CAT_OPTIONS_def] >> rpt strip_tac
   >> Cases_on `h` >> fs[CAT_OPTIONS_def]
  );

val CAT_OPTIONS_LENGTH = store_thm
  ("CAT_OPTIONS_LENGTH",
   ``!l. (EVERY IS_SOME l = (LENGTH (CAT_OPTIONS l) = LENGTH l))
       ∧ (LENGTH (CAT_OPTIONS l) <= LENGTH l)``,
   Induct_on `l` >> fs[CAT_OPTIONS_def] >> rpt strip_tac
   >> Cases_on `h` >> fs[IS_SOME_DEF,CAT_OPTIONS_def]
  );

val CAT_OPTIONS_EL = store_thm
  ("CAT_OPTIONS_EL",
   ``!l. EVERY IS_SOME l
          ==> !i. (i < LENGTH l)
          ==> (SOME (EL i (CAT_OPTIONS l)) = EL i l)``,
   Induct_on `l` >> fs[CAT_OPTIONS_def] >> rpt strip_tac
   >> Cases_on `h` >> fs[IS_SOME_DEF,CAT_OPTIONS_def]
   >> Cases_on `i` >> fs[EL]
  );

val OPTION_TO_LIST_def = Define`
    (OPTION_TO_LIST NONE = [])
  ∧ (OPTION_TO_LIST (SOME l) = l)`;

val OPTION_TO_LIST_MEM = store_thm
  ("OPTION_TO_LIST_MEM",
   ``!x o_l. MEM x (OPTION_TO_LIST o_l)
             = ?l. (o_l = SOME l) ∧ (MEM x l)``,
   rpt strip_tac >> Cases_on `o_l` >> fs[OPTION_TO_LIST_def]
  );

val LIST_INTER_def = Define`
    (LIST_INTER [] ls = [])
  ∧ (LIST_INTER (x::xs) ls = if MEM x ls
                             then x::(LIST_INTER xs ls)
                             else LIST_INTER xs ls)`;

(* val GROUP_BY_def = tDefine "GROUP_BY" *)
(*   `(GROUP_BY P [] = []) *)
(*  ∧ (GROUP_BY P (x::xs) = *)
(*        (FILTER (P x) (x::xs))::(GROUP_BY P (FILTER ($~ o (P x)) xs)) *)
(*    )` *)
(*   (WF_REL_TAC `measure (LENGTH o SND)` >> rpt strip_tac >> fs[] *)
(*    >> Q.HO_MATCH_ABBREV_TAC `A < SUC B` >> `A <= B ` suffices_by simp[] *)
(*    >> metis_tac[LENGTH_FILTER_LEQ] *)
(*   ); *)

(* val GROUP_BY_SET_LEMM = store_thm *)
(*   ("GROUP_BY_SET_LEMM", *)
(*    ``!P l. (!x. P x x) ==> set l = (set (FLAT (GROUP_BY P l)))``, *)
(*    Induct_on `l` >> fs[GROUP_BY_def] >> rpt strip_tac *)
(*    >> Cases_on `P h h` >> fs[] *)
(*    >- () *)

(* ) *)

val SPAN_def = Define`
   (SPAN R [] = ([],[]))
 ∧ (SPAN R (x::xs) =
    if R x
    then (let (ys,rs) = SPAN R xs
          in (x::ys,rs))
    else ([],x::xs)
   )`;

val SPAN_APPEND = store_thm
  ("SPAN_APPEND",
   ``!R l l1 l2. (SPAN R l = (l1,l2)) ==> (l1 ++ l2 = l)``,
   gen_tac >> Induct_on `l` >> fs[SPAN_def] >> rpt strip_tac
   >> Cases_on `R h` >> fs[]
   >> Cases_on `SPAN R l` >> rw[] >> fs[]
  );

val SPAN_EQ = store_thm
  ("SPAN_EQ",
   ``!R x y t. equivalence R ∧ R x y ==> (SPAN (R x) t = SPAN (R y) t)``,
   gen_tac >> Induct_on `t` >> fs[SPAN_def] >> rpt strip_tac
   >> `SPAN (R x) t = SPAN (R y) t` by metis_tac[]
   >> `R x h = R y h` by (
       metis_tac[equivalence_def,relationTheory.transitive_def,
                 relationTheory.reflexive_def,
                 relationTheory.symmetric_def]
   )
   >> Cases_on `R x h` >> fs[]
  );

val SPAN_FST_LEMM = store_thm
  ("SPAN_FST_LEMM",
   ``!x R l. MEM x (FST (SPAN R l)) ==> R x``,
   Induct_on `l` >> fs[SPAN_def] >> rpt strip_tac
   >> Cases_on `R h` >> fs[] >> Cases_on `x = h` >> fs[]
   >> Cases_on `SPAN R l` >> fs[]
  );

val GROUP_BY_def = tDefine "GROUP_BY"
  `(GROUP_BY P []  = [])
 ∧ (GROUP_BY P (x::xs) =
    let (ys,rs) = SPAN (P x) (xs)
    in (x::ys)::(GROUP_BY P rs)
   )`
   (WF_REL_TAC `measure (LENGTH o SND)` >> rpt strip_tac
    >> `ys ++ rs = xs` by metis_tac[SPAN_APPEND]
    >> `LENGTH ys + LENGTH rs = LENGTH xs` by metis_tac[LENGTH_APPEND]
    >> fs[]
   );

val GROUP_BY_FLAT = store_thm
  ("GROUP_BY_FLAT",
   ``!P l. (FLAT (GROUP_BY P l)) = l``,
   gen_tac
   >> `!l1 l2 l. (l1 ++ l2 = l)
                 ==> ((FLAT (GROUP_BY P l2)) = l2)` by (
       Induct_on `l` >> fs[GROUP_BY_def] >> rpt strip_tac
       >> Cases_on `l1`
       >- (fs[] >> simp[GROUP_BY_def] >> Cases_on `SPAN (P h) l`
           >> `q ++ r = l` by metis_tac[SPAN_APPEND]
           >> fs[] >> `(FLAT (GROUP_BY P r)) = r` by metis_tac[]
           >> rw[LIST_TO_SET_APPEND]
          )
       >- (Cases_on `l2` >> fs[GROUP_BY_def] >> rw[]
           >> Cases_on `SPAN (P h'') t'` >> fs[]
           >> `q++r = t'` by metis_tac[SPAN_APPEND]
           >> first_x_assum (qspec_then `t ++ [h''] ++ q` mp_tac) >> simp[]
           >> rpt strip_tac >> rw[LIST_TO_SET_APPEND]
          )
   )
   >> strip_tac >> `[] ++ l = l` by simp[] >> metis_tac[]
  );

val rel_corr_def = Define `
  rel_corr R P =
   !x y. R x y = (P x y ∧ P y x)`;

val REL_CORR_GROUP_BY = store_thm
  ("REL_CORR_GROUP_BY",
   ``!R P. rel_corr R P
             ∧ equivalence R ∧ transitive P
             ==> !k_hd k_tl l.
             (GROUP_BY R l = (k_hd::k_tl))
                ∧ (SORTED P l)
                ==> (!x y k. (MEM x k_hd)
                           ∧ (MEM k k_tl)
                           ∧ (MEM y k)
                              ==> ~R x y)``,
    gen_tac >> gen_tac >> strip_tac >> Induct_on `l` >> fs[GROUP_BY_def,SPAN_def]
    >> (rpt strip_tac >> rename[`SORTED P (H::l)`]
        >> Cases_on `SPAN (R H) l`
        >> Cases_on `l`
        >- (fs[GROUP_BY_def,SPAN_def] >> rw[] >> fs[GROUP_BY_def])
        >- (fs[GROUP_BY_def,SPAN_def] >> rename[`SORTED P (H::h2::t1)`]
            >> Cases_on `R H h2` >> fs[]
            >- (first_x_assum (qspec_then `q` mp_tac)
                >> rpt strip_tac
                >> first_x_assum (qspec_then `GROUP_BY R r` mp_tac)
                >> simp[GROUP_BY_def] >> fs[SORTED_DEF]
                >> strip_tac
                >> `SPAN (R h2) t1 = SPAN (R H) t1`
                        by metis_tac[SPAN_EQ]
                >> rw[] >> Cases_on `SPAN (R H) t1` >> fs[]
                >- (rw[] >> metis_tac[equivalence_def,
                                      relationTheory.symmetric_def,relationTheory.transitive_def])
                >- (rw[] >> qexists_tac `x` >> simp[] >> fs[] >> rw[]
                    >> metis_tac[equivalence_def,relationTheory.symmetric_def,
                                 relationTheory.transitive_def]
                   )
               )
            >- (rw[] >> Cases_on `GROUP_BY R (h2::t1)` >> fs[]
                >> rw[] >> fs[SORTED_DEF]
                >> rename[`GROUP_BY R (h3::t2) = h4::t3`]
                >- (`R h3 y` by (
                        fs[GROUP_BY_def,SPAN_def]
                        >> Cases_on `SPAN (R h3) t2` >> fs[]
                        >> `!x. MEM x (FST (q,r)) ==> (R h3 x)`
                                 by metis_tac[SPAN_FST_LEMM]
                        >> Cases_on `y = h3` >> fs[]
                        >> `MEM y q` by (rw[] >> fs[])
                        >> metis_tac[]
                    )
                    >> metis_tac[equivalence_def,relationTheory.symmetric_def,relationTheory.transitive_def]
                   )
                >- (`P h3 H` by (
                     Cases_on `y = h3` >> rw[]
                     >- metis_tac[equivalence_def, relationTheory.reflexive_def]
                     >- (
                      `MEM y t2` by (
                         `FLAT (GROUP_BY R (h3::t2)) = h3::t2`
                             by metis_tac[GROUP_BY_FLAT]
                          >> `MEM y (FLAT (GROUP_BY R (h3::t2)))` by (
                             simp[MEM_FLAT] >> metis_tac[]
                          )
                          >> `MEM y (h3::t2)` by metis_tac[]
                          >> fs[] >> metis_tac[]
                      )
                      >> `P h3 y` by metis_tac[SORTED_EQ]
                      >> fs[rel_corr_def]
                      >> metis_tac[equivalence_def,relationTheory.symmetric_def,relationTheory.transitive_def]
                     )
                   )
                   >> metis_tac[rel_corr_def]
                   )
               )
           )
       )
  );

val _ = Cond_rewr.stack_limit := 1

val SORTED_GROUP_BY = store_thm
  ("SORTED_GROUP_BY",
    ``!R P l. SORTED P l ∧ transitive P ∧ equivalence R
            ∧ rel_corr R P
       ==> (!l_sub. MEM l_sub (GROUP_BY R l)
            ==> ((!x y. MEM x l_sub ∧ MEM y l_sub ==> R x y)
               ∧ (!x y. MEM x l_sub ∧ MEM y l ∧ R x y ==> MEM y l_sub)))``,
   gen_tac >> gen_tac >> Induct_on `l`
   >- (rpt strip_tac >> fs[GROUP_BY_def])
   >- (
    simp[] >> gen_tac >> strip_tac >>  strip_tac >> strip_tac
    >> Cases_on `l` >> fs[]
    >- (rpt strip_tac >> fs[GROUP_BY_def,SPAN_def,equivalence_def] >> rw[]
        >> fs[] >> rw[] >> metis_tac[relationTheory.reflexive_def]
       )
    >- (fs[SORTED_DEF] >> Cases_on `GROUP_BY R (h'::t)` >> fs[]
     >- (fs[GROUP_BY_def,SPAN_def] >> Cases_on `R h h'` >> fs[]
         >> Cases_on `SPAN (R h) t` >> Cases_on `SPAN (R h') t`
         >> fs[SPAN_EQ]
        )
     >- (Cases_on `R h h'`
      >- (Cases_on `GROUP_BY R (h::h'::t)` >> fs[]
          >> `h''' = h::h''` by (
              fs[GROUP_BY_def,SPAN_def] >> Cases_on `R h h'` >> fs[]
              >> `SPAN (R h) t = SPAN (R h') t` by metis_tac[SPAN_EQ]
              >> rw[] >> Cases_on `SPAN (R h') t` >> fs[] >> rw[]
             )
          >> `t' = t''` by (
               fs[GROUP_BY_def,SPAN_def] >> Cases_on `R h h'` >> fs[]
                 >> `SPAN (R h) t = SPAN (R h') t`  by metis_tac[SPAN_EQ]
                 >> rw[] >> Cases_on `SPAN (R h') t` >> fs[] >> rw[]
           )
          >> strip_tac
          >- (rw[] >> fs[]
              >> first_x_assum (qspec_then `h''` mp_tac) >> simp[]
              >> rpt strip_tac >> fs[HD] >> rw[] >> rpt strip_tac
              >- metis_tac[equivalence_def,relationTheory.reflexive_def]
              >- (rw[]
                  >> `MEM h' h''` by (
                     fs[GROUP_BY_def,SPAN_def]
                      >> rw[] >> Cases_on `R h h'` >> fs[]
                      >> Cases_on `SPAN (R h) t` >> Cases_on `SPAN (R h') t`
                      >> fs[SPAN_EQ] >> rw[]
                   )
                  >> metis_tac[equivalence_def,relationTheory.transitive_def]
                 )
              >- (rw[]
                  >> `MEM h' h''` by (
                       fs[GROUP_BY_def,SPAN_def]
                       >> rw[] >> Cases_on `R h h'` >> fs[]
                       >> Cases_on `SPAN (R h) t` >> Cases_on `SPAN (R h') t`
                       >> fs[SPAN_EQ] >> rw[]
                   )
                  >> metis_tac[equivalence_def,relationTheory.transitive_def,
                               relationTheory.symmetric_def]
                 )
             )
          >- (first_x_assum (qspec_then `h''` mp_tac) >> simp[]
              >> rpt strip_tac >> rw[]
              >> fs[GROUP_BY_def,SPAN_def] >> Cases_on `R h h'` >> fs[]
              >> `SPAN (R h) t = SPAN (R h') t` by metis_tac[SPAN_EQ]
              >> rw[] >> Cases_on `SPAN (R h') t` >> fs[] >> rw[]
              >> Cases_on `y = h` >> Cases_on `y = h'` >> fs[]
              >> metis_tac[equivalence_def,relationTheory.transitive_def,
                           relationTheory.reflexive_def,
                           relationTheory.symmetric_def]
             )
          >- (first_x_assum (qspec_then `l_sub` mp_tac) >> simp[])
          >- (first_x_assum (qspec_then `l_sub` mp_tac) >> simp[]
              >> rpt strip_tac >> rw[]
              >- (fs[SORTED_EQ]
                  >> `FLAT (h''::t') = h'::t`
                      by metis_tac[GROUP_BY_FLAT]
                  >> `MEM x (FLAT (h''::t'))` by (simp[MEM_FLAT] >> metis_tac[])
                  >> `MEM x (h'::t)` by metis_tac[]
                  >> Cases_on `x = h'`
                  >> rw[]
                  >> `SORTED P (h::h'::t)` by (
                       simp[SORTED_EQ] >> rpt strip_tac >> fs[]
                       >> metis_tac[relationTheory.transitive_def]
                  )
                  >> `!k_hd k_tl l.
                       (GROUP_BY R l = k_hd::k_tl) ∧ SORTED P l
                       ==> ∀x y k. MEM x k_hd ∧ MEM k k_tl ∧ MEM y k ⇒ ¬R x y`
                      by (HO_MATCH_MP_TAC REL_CORR_GROUP_BY >> metis_tac[])
                  >> first_x_assum (qspec_then `h::h''` mp_tac)
                  >> rpt strip_tac
                  >> first_x_assum (qspec_then `t'` mp_tac)
                  >> rpt strip_tac
                  >> first_x_assum (qspec_then `h::h'::t` mp_tac) >> simp[]
                  >> rpt strip_tac
                  >> (fs[]
                  >- metis_tac[]
                  >- (fs[MEM_FLAT] >> `~R h x` by metis_tac[]
                      >> metis_tac[equivalence_def,relationTheory.symmetric_def]
                     ))
                 )
              >- metis_tac[]
              >- metis_tac[]
             )
         )
      >- (`(l_sub = [h]) \/ (l_sub  = h'') \/ (MEM l_sub t')` by (
            fs[GROUP_BY_def,SPAN_def]
          )
          >- (rpt strip_tac >> rw[]
              >- (`(x = h) ∧ (y = h)` by fs[]
                  >> metis_tac[equivalence_def,relationTheory.reflexive_def]
                 )
              >- (`x = h` by fs[] >> metis_tac[])
              >- (`x = h` by fs[] >> rw[]
                  >> `SORTED P (h::h'::t)` by (
                     simp[SORTED_EQ] >> rpt strip_tac >> fs[SORTED_EQ]
                     >> metis_tac[relationTheory.transitive_def]
                  )
                  >> `FLAT (GROUP_BY R (h::h'::t)) = h::h'::t`
                      by fs[GROUP_BY_FLAT]
                  >> `!k_hd k_tl l.
                        (GROUP_BY R l = k_hd::k_tl) ∧ SORTED P l
                        ==> ∀x y k. MEM x k_hd ∧ MEM k k_tl ∧ MEM y k ⇒ ¬R x y`
                     by (HO_MATCH_MP_TAC REL_CORR_GROUP_BY >> metis_tac[])
                  >> Cases_on `GROUP_BY R (h::h'::t)`
                  >- fs[FLAT]
                  >- (
                    rename[`GROUP_BY R (h::h1::t) = h3::t2`]
                    >> first_x_assum (qspec_then `h3` mp_tac)
                    >> rpt strip_tac
                    >> first_x_assum (qspec_then `t2` mp_tac)
                    >> rpt strip_tac
                    >> first_x_assum (qspec_then `h::h1::t` mp_tac) >> simp[]
                    >> rpt strip_tac >> fs[GROUP_BY_def]
                    >> Cases_on `SPAN (R h) (h1::t)` >> fs[]
                    >> fs[SPAN_def] >> Cases_on `R h h1` >> fs[]
                    >> rw[] >> Cases_on `SPAN (R h1) t` >> fs[]
                    >> rw[] >> `MEM y (FLAT (GROUP_BY R (h1::t)))` by fs[]
                    >> fs[MEM_FLAT]
                  )
                 )
             )
          >- (rpt strip_tac >> rw[]
           >- (first_x_assum (qspec_then `h''` mp_tac) >> simp[]
               >> rpt strip_tac >> rw[]
               >> `FLAT (h''::t') = h'::t` by metis_tac[GROUP_BY_FLAT]
               >> `MEM h' h''` by (Cases_on `h''` >> fs[FLAT])
               >> metis_tac[equivalence_def,relationTheory.symmetric_def,
                            relationTheory.transitive_def]
              )
           >- (first_x_assum (qspec_then `h''` mp_tac) >> simp[]
               >> rpt strip_tac >> rw[]
               >> `SORTED P (h::h'::t)` by (
                    simp[SORTED_EQ] >> rpt strip_tac >> fs[SORTED_EQ]
                    >> metis_tac[relationTheory.transitive_def]
                )
               >> `FLAT (GROUP_BY R (h::h'::t)) = h::h'::t`
                   by fs[GROUP_BY_FLAT]
               >> `!k_hd k_tl l.
                   (GROUP_BY R l = k_hd::k_tl) ∧ SORTED P l
                   ==> ∀x y k. MEM x k_hd ∧ MEM k k_tl ∧ MEM y k ⇒ ¬R x y`
                       by (HO_MATCH_MP_TAC REL_CORR_GROUP_BY >> metis_tac[])
               >> Cases_on `GROUP_BY R (h::h'::t)`
               >- fs[FLAT]
               >- (rename[`GROUP_BY R (h::h1::t) = h3::t2`]
                   >> first_x_assum (qspec_then `h3` mp_tac)
                   >> rpt strip_tac
                   >> first_x_assum (qspec_then `t2` mp_tac)
                   >> rpt strip_tac
                   >> first_x_assum (qspec_then `h::h1::t` mp_tac) >> simp[]
                   >> rpt strip_tac >> fs[GROUP_BY_def]
                   >- (Cases_on `SPAN (R h) (h1::t)` >> fs[]
                      >> fs[SPAN_def] >> Cases_on `R h h1` >> fs[]
                      >> rw[] >> Cases_on `SPAN (R h1) t` >> fs[]
                      >> rw[] >> `MEM y (FLAT (GROUP_BY R (h1::t)))` by fs[])
                   >- (Cases_on `SPAN (R h) (h1::t)` >> fs[]
                       >> fs[SPAN_def] >> Cases_on `R h h1` >> fs[]
                       >> rw[] >> Cases_on `SPAN (R h1) t` >> fs[]
                       >> metis_tac[equivalence_def,relationTheory.symmetric_def]
                      )
                  )
              )
           >- metis_tac[]
             )
          >- (rpt strip_tac >> rw[]
               >- metis_tac[]
               >- (first_x_assum (qspec_then `l_sub` mp_tac) >> simp[]
                   >> rpt strip_tac >> `SORTED P (h::h'::t)` by (
                    simp[SORTED_EQ] >> rpt strip_tac >> fs[SORTED_EQ]
                    >> metis_tac[relationTheory.transitive_def]
                )
               >> `FLAT (GROUP_BY R (h::h'::t)) = h::h'::t`
                   by fs[GROUP_BY_FLAT]
               >> `!k_hd k_tl l.
                   (GROUP_BY R l = k_hd::k_tl) ∧ SORTED P l
                   ==> ∀x y k. MEM x k_hd ∧ MEM k k_tl ∧ MEM y k ⇒ ¬R x y`
                       by (HO_MATCH_MP_TAC REL_CORR_GROUP_BY >> metis_tac[])
               >> Cases_on `GROUP_BY R (h::h'::t)`
               >- fs[FLAT]
               >- (rename[`GROUP_BY R (h::h1::t) = h3::t2`]
                   >> first_x_assum (qspec_then `h3` mp_tac)
                   >> rpt strip_tac
                   >> first_x_assum (qspec_then `t2` mp_tac)
                   >> rpt strip_tac
                   >> first_x_assum (qspec_then `h::h1::t` mp_tac) >> simp[]
                   >> rpt strip_tac >> fs[GROUP_BY_def]
                   >- (Cases_on `SPAN (R h) (h1::t)` >> fs[]
                      >> fs[SPAN_def] >> Cases_on `R h h1` >> fs[]
                      >> rw[] >> Cases_on `SPAN (R h1) t` >> fs[]
                      >> rw[] >> `MEM y (FLAT (GROUP_BY R (h1::t)))` by fs[])
                   >- (Cases_on `SPAN (R h) (h1::t)` >> fs[]
                       >> fs[SPAN_def] >> Cases_on `R h h1` >> fs[]
                       >> rw[] >> Cases_on `SPAN (R h1) t` >> fs[]
                       >> metis_tac[equivalence_def,relationTheory.symmetric_def]
                      )
                  )
                  )
               >- metis_tac[]
               >- metis_tac[]
              )
         )
        )
       )
   )
  );

val ONLY_MINIMAL_def = Define`
  ONLY_MINIMAL P l =
    FILTER (λa. ~EXISTS (λx. P x a ∧ ~(x = a)) l) l`;


  (*   (ONLY_MINIMAL P [] = []) *)
  (* ∧ (ONLY_MINIMAL P (x::xs) = *)
  (*     (* if EXISTS (λx1. P x1 x) xs *) *)
  (*     (* then ONLY_MINIMAL P xs *) *)
  (*     x::(FILTER (λa. ~P a x) (ONLY_MINIMAL P xs)) *)
  (*   )`; *)

val ONLY_MINIMAL_SUBSET = store_thm
  ("ONLY_MINIMAL_SUBSET",
   ``!P l. MEM_SUBSET (ONLY_MINIMAL P l) l``,
   gen_tac >> Induct_on `l` >> fs[ONLY_MINIMAL_def,MEM_SUBSET_def]
   >> rpt strip_tac >> fs[MEM_SUBSET_SET_TO_LIST]
   >> Cases_on `EVERY ($~ ∘ (λx. P x h ∧ x ≠ h)) l`
   >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> fs[MEM_FILTER,EVERY_MEM]
  );

val ONLY_MINIMAL_MEM = store_thm
  ("ONLY_MINIMAL_MEM",
   ``!P l x.
       (MEM x (ONLY_MINIMAL P l) =
        (MEM x l ∧ (!y. MEM y l ∧ ~(x = y) ==> ~P y x)))``,
   simp[EQ_IMP_THM] >> rpt strip_tac
   >- metis_tac[MEM_SUBSET_SET_TO_LIST,ONLY_MINIMAL_SUBSET,MEM,SUBSET_DEF]
   >- (fs[ONLY_MINIMAL_def,MEM_FILTER,EVERY_MEM] >> metis_tac[])
   >- (simp[ONLY_MINIMAL_def,MEM_FILTER,EVERY_MEM] >> rpt strip_tac
       >> metis_tac[]
      )
  );

val INDEX_FIND_LEMM = store_thm
  ("INDEX_FIND_LEMM",
   ``!P i ls. OPTION_MAP SND (INDEX_FIND i P ls)
                            = OPTION_MAP SND (INDEX_FIND (SUC i) P ls)``,
   gen_tac >> Induct_on `ls` >> fs[OPTION_MAP_DEF,INDEX_FIND_def]
   >> Cases_on `P h`
    >- fs[OPTION_MAP_DEF,INDEX_FIND_def]
    >- metis_tac[]
  );

val FIND_LEMM = store_thm
  ("FIND_LEMM",
   ``!P x l. MEM x l ∧ P x
           ==> ?y. (FIND P l = SOME y) ∧ (P y)``,
  gen_tac >> Induct_on `l` >> rpt strip_tac >> fs[]
   >- (rw[] >> simp[FIND_def,INDEX_FIND_def])
   >- (rw[]
       >> `?y. (OPTION_MAP SND (INDEX_FIND 0 P (h::l)) = SOME y)
             ∧ (P y)` suffices_by fs[FIND_def]
       >> first_x_assum (qspec_then `x` mp_tac)
       >> rpt strip_tac
       >> `?y. (OPTION_MAP SND (INDEX_FIND 0 P l) = SOME y)
             ∧ (P y)` by fs[FIND_def]
       >> Cases_on `P h`
        >- fs[INDEX_FIND_def]
        >- (`∃y. (OPTION_MAP SND (INDEX_FIND 1 P l) = SOME y) ∧ P y`
            suffices_by fs[INDEX_FIND_def]
            >> qexists_tac `y` >> rpt strip_tac
            >> metis_tac[INDEX_FIND_LEMM,DECIDE ``SUC 0 = 1``])
      )
  );

val FIND_LEMM2 = store_thm
  ("FIND_LEMM2",
   ``!P x l. (FIND P l = SOME x) ==> (MEM x l ∧ P x)``,
   gen_tac >> Induct_on `l` >> fs[FIND_def,INDEX_FIND_def]
   >> rpt strip_tac >> Cases_on `P h` >> fs[] >> Cases_on `z`
   >> fs[]
   >> `OPTION_MAP SND (INDEX_FIND 0 P l) =
                 OPTION_MAP SND (INDEX_FIND 1 P l)`
      by metis_tac[INDEX_FIND_LEMM,DECIDE ``SUC 0 = 1``]
   >> rw[]
   >> `OPTION_MAP SND (INDEX_FIND 0 P l) = SOME r` by (
       `OPTION_MAP SND (INDEX_FIND 1 P l) = SOME r` by fs[]
       >> metis_tac[]
   )
   >> fs[]
  );

val FIND_UNIQUE = store_thm
  ("FIND_UNIQUE",
   ``!P x l. P x ∧ (!y. MEM y l ∧ P y ==> (y = x)) ∧ MEM x l
         ==> (FIND P l = SOME x)``,
   gen_tac >> Induct_on `l` >> rpt strip_tac
   >- fs[]
   >- (Cases_on `P h`
       >- (`x = h` by fs[] >> rw[]
           >> fs[FIND_def,INDEX_FIND_def]
          )
       >- (fs[FIND_def] >> rw[] >> fs[]
           >> fs[INDEX_FIND_def]
           >> `∃z. (INDEX_FIND 0 P l = SOME z) ∧ (x = SND z)`
                 by metis_tac[]
           >> Cases_on `z`
           >> `OPTION_MAP SND (INDEX_FIND 0 P l)
               = OPTION_MAP SND (INDEX_FIND (SUC 0) P l)`
              by metis_tac[INDEX_FIND_LEMM]
           >> `OPTION_MAP SND (INDEX_FIND 0 P l) = SOME r`
              by fs[OPTION_MAP_DEF] >> fs[]
           >> `OPTION_MAP SND (INDEX_FIND 1 P l) = SOME r`
              by fs[OPTION_MAP_DEF] >> fs[]
           >> metis_tac[]
          )
      )
  );


val PSUBSET_WF = store_thm
 ("PSUBSET_WF",
  ``!d. FINITE d ==> WF (\s t. s ⊂ t ∧ s ⊆ d ∧ t ⊆ d)``,
  rpt strip_tac
  >> qabbrev_tac `r_reln = rel_to_reln (\s t. s ⊂ t ∧ s ⊆ d ∧ t ⊆ d)`
  >> `transitive r_reln` by (
      simp[transitive_def] >> rpt strip_tac >> qunabbrev_tac `r_reln`
      >> fs[rel_to_reln_def] >> metis_tac[PSUBSET_TRANS]
  )
  >> `acyclic r_reln` by (
      fs[acyclic_def] >> rpt strip_tac
      >> `(x,x) ∈ r_reln` by metis_tac[transitive_tc]
      >> qunabbrev_tac `r_reln` >> fs[rel_to_reln_def]
  )
  >> `domain r_reln ⊆ (POW d)` by (
      qunabbrev_tac `r_reln` >> fs[domain_def,rel_to_reln_def]
      >> simp[SUBSET_DEF] >> rpt strip_tac
      >> metis_tac[SUBSET_DEF,IN_POW]
  )
  >> `range r_reln ⊆ (POW d)` by (
      qunabbrev_tac `r_reln` >> fs[range_def,rel_to_reln_def]
      >> simp[SUBSET_DEF] >> rpt strip_tac
      >> metis_tac[SUBSET_DEF,IN_POW]
  )
  >> `(λs t. s ⊂ t ∧ s ⊆ d ∧ t ⊆ d) = reln_to_rel r_reln` by (
      qunabbrev_tac `r_reln` >> fs[rel_to_reln_inv])
  >> `FINITE (POW d)` by metis_tac[FINITE_POW]
  >> `WF (reln_to_rel r_reln)` suffices_by fs[]
  >> metis_tac[acyclic_WF]
 );

val BOUNDED_INCR_WF_LEMM = store_thm
  ("BOUNDED_INCR_WF_LEMM",
   ``!b m n. WF (λ(i,j) (i1,j1).
                  (b (i,j) = b (i1,j1))
                  ∧ (i1 < i) ∧ (i <= b (i,j)))``,
   rpt strip_tac >> rw[WF_IFF_WELLFOUNDED] >> simp[wellfounded_def]
   >> rpt strip_tac >> CCONTR_TAC >> fs[]
   >> `!n. b (FST (f n), SND (f n)) = b (FST (f 0), SND (f 0))` by (
       Induct_on `n` >> first_x_assum (qspec_then `n` mp_tac) >> rpt strip_tac
       >> fs[] >> Cases_on `f n` >> Cases_on `f (SUC n)`
       >> fs[]
   )
   >> qabbrev_tac `B = b (FST (f 0),SND (f 0))`
   >> `!n. (λ(i,j) (i1,j1). i1 < i ∧ i <= B) (f (SUC n)) (f n)` by (
       rpt strip_tac >> rpt (first_x_assum (qspec_then `n` mp_tac))
       >> rpt strip_tac >> Cases_on `f n` >> Cases_on `f (SUC n)`
       >> fs[]
   )
   >> `!k. ?n. (FST (f n) > k)` by (
       Induct_on `k`
        >- (Cases_on `FST (f 0)` >> fs[]
         >- (first_x_assum (qspec_then `0` mp_tac) >> rpt strip_tac
             >> qexists_tac `SUC 0` >> Cases_on `f (SUC 0)` >> Cases_on `f 0`
             >> fs[]
            )
         >- (qexists_tac `0` >> fs[])
           )
        >- (fs[] >> Cases_on `FST (f n) = SUC k`
         >- (first_x_assum (qspec_then `n` mp_tac) >> rpt strip_tac
             >> Cases_on `f (SUC n)` >> Cases_on `f n` >> fs[]
             >> qexists_tac `SUC n` >> fs[]
            )
         >- (qexists_tac `n` >> fs[])
           )
   )
   >> first_x_assum (qspec_then `B` mp_tac) >> rpt strip_tac
   >> first_x_assum (qspec_then `n` mp_tac) >> rpt strip_tac
   >> Cases_on `f (SUC n)` >> Cases_on `f n` >> fs[]
  );

val WF_LEMM = store_thm
  ("WF_LEMM",
   ``!P A b. (!k. A k ==> WF (P k))
         ==> ((!k. A (b k)) ==> WF (λa a2. (b a = b a2) ∧ P (b a) a a2))``,
   rpt strip_tac >> rw[WF_IFF_WELLFOUNDED] >> simp[wellfounded_def]
    >> rpt strip_tac >> CCONTR_TAC >> fs[]
    >> `∀n. b (f (SUC n)) = b (f n)` by metis_tac[]
    >> `!n. b (f (SUC n)) = b (f 0)` by (Induct_on `n` >> fs[])
    >> `!n. P (b (f (SUC n))) (f (SUC n)) (f n)` by metis_tac[]
    >> `!n. P (b (f 0)) (f (SUC n)) (f n)` by metis_tac[]
    >> `!n. P (b (f 0)) (f (SUC n)) (f n)` by metis_tac[]
    >> `~wellfounded (P (b (f 0)))` by metis_tac[wellfounded_def]
    >> metis_tac[WF_IFF_WELLFOUNDED]
  );

val NoNodeProcessedTwice_def = Define`
  NoNodeProcessedTwice g m (a,ns) (a2,ns2) =
    ((g DIFF (m a) ⊂ g DIFF (m a2))
         \/ ((g DIFF (m a) = g DIFF (m a2))
           ∧ (LENGTH ns) < (LENGTH ns2)))`;

val NNPT_WF = store_thm
 ("NNPT_WF",
  ``!g m. FINITE g ==> WF (NoNodeProcessedTwice g m)``,
   rpt strip_tac
   >> `WF (λs t. s ⊂ t
         ∧ s ⊆ g ∧ t ⊆ g)` by metis_tac[PSUBSET_WF]
   >> `WF ($<)` by metis_tac[WF_LESS]
   >> `WF (λ (x:γ list) y.
            LENGTH x < LENGTH y)` by (
       `inv_image ($<) (LENGTH:(γ list -> num))
              = (λx y.
                  LENGTH x < LENGTH y)` by simp[inv_image_def]
       >> `WF (inv_image ($<) (LENGTH:(γ list -> num)))` suffices_by fs[]
       >> metis_tac[WF_inv_image]
   )
   >> qabbrev_tac `P = (λs t. s ⊂ t ∧ s ⊆ g ∧ t ⊆ g)`
   >> qabbrev_tac `Q = (λ(x:γ list) (y:γ list). LENGTH x < LENGTH y)`
   >> qabbrev_tac `f = λ a. g DIFF (m a)`
   >> `inv_image P f = λ a a2.
                        (g DIFF (m a)
                         ⊂ g DIFF (m a2))` by (
      qunabbrev_tac `P`
      >> fs[inv_image_def]
      >> `(\x y. f x ⊂ f y) = (λa a2. f a ⊂ f a2)`
         suffices_by (
          fs[] >> qunabbrev_tac `f` >> simp[inv_image_def]
      )
      >> metis_tac[]
   )
   >> `WF (inv_image P f)` by metis_tac[WF_inv_image]
   >> `WF (P LEX Q)` by metis_tac[WF_LEX]
   >> qabbrev_tac
        `j = λ(a,l:(γ list)). (g DIFF (m a),l)`
   >> `WF (inv_image (P LEX Q) j)` by metis_tac[WF_inv_image]
   >> `!x y. (NoNodeProcessedTwice g m) x y ==> (inv_image (P LEX Q) j) x y` by (
       fs[inv_image_def,LEX_DEF] >> rpt strip_tac
         >> Cases_on `x` >> Cases_on `y` >> fs[NoNodeProcessedTwice_def]
         >> qunabbrev_tac `f` >> qunabbrev_tac `P` >> qunabbrev_tac `Q`
         >> simp[] >> simp[EQ_IMP_THM] >> rpt strip_tac
         >> (qunabbrev_tac `j` >> simp[])
   )
   >> metis_tac[WF_SUBSET]
 );

val P_DIVIDED_WF_LEMM = store_thm
  ("P_DIVIDED_WF_LEMM",
   ``!P R1 R2.
     WF (λx y. ~P x ∧ ~P y ∧ R1 x y) ∧ WF R2
     ∧ (!x y. P y ∧ R2 x y ==> P x)
     ==> WF (λx y. ((~P y ∧ ~P x) ==> R1 x y) ∧ (P y ==> R2 x y))``,
   rpt strip_tac >> rw[WF_IFF_WELLFOUNDED] >> simp[wellfounded_def]
   >> rpt strip_tac
   >> `!k. P (f k)
        ==> ?j. k <= j ∧ (P (f j) ∧ ~R2 (f (SUC j)) (f j))` by (
       rpt strip_tac
       >> `¬∃f. ∀n. R2 (f (SUC n)) (f n)`
          by metis_tac[WF_IFF_WELLFOUNDED,wellfounded_def] >> fs[]
       >> qabbrev_tac `f_k = λn. f (n + k)`
       >> qabbrev_tac `N = $LEAST (λk. ~R2 (f_k (SUC k)) (f_k k))`
       >> `(λk. ~R2 (f_k (SUC k)) (f_k k)) N
           ∧ !n. n < N ==> ~(λk. ~R2 (f_k (SUC k)) (f_k k)) n` by (
           qunabbrev_tac `N`
           >> Q.HO_MATCH_ABBREV_TAC `
               Q ($LEAST Q)
               ∧ !n. n < ($LEAST Q) ==> ~Q n`
           >> HO_MATCH_MP_TAC LEAST_EXISTS_IMP >> fs[]
           >> qunabbrev_tac `Q` >> fs[]
       )
       >> `!a. a <= N ==> P (f_k a)` by (
           Induct_on `a` >> fs[]
           >- (qunabbrev_tac `f_k` >> fs[])
           >- (strip_tac >> `a < N` by fs[]
               >> metis_tac[DECIDE ``a < N ==> a <= N``]
              )
       )
       >> qexists_tac `N+k` >> qunabbrev_tac `f_k` >> fs[]
       >> metis_tac[DECIDE ``SUC (N + k) = k + SUC N``]
   )
   >> Cases_on `?a. P (f a)` >> fs[]
   >- metis_tac[]
   >- (`?k. P (f k) \/ (~P (f k) ∧ ~R1 (f (SUC k)) (f k))` by (
        `?n. P (f (SUC n)) ∨ P (f n) ∨ (¬R1 (f (SUC n)) (f n) ∧ ~P (f n))`
            by (fs[WF_IFF_WELLFOUNDED, wellfounded_def]
                >> metis_tac[])
        >> metis_tac[]
       )
       >> metis_tac[]
      )
  );

val MOD_LEMM = store_thm
  ("MOD_LEMM",
   ``!x n. (0 < n) ==> ((x - (x MOD n)) MOD n = 0)``,
   rpt strip_tac
    >> `((x - (x MOD n) + (x MOD n)) MOD n = ((0 + (x MOD n)) MOD n))` by (
       `(x MOD n) <= x` by simp[MOD_LESS_EQ]
       >> `x - (x MOD n) + (x MOD n) = x` by simp[]
       >> fs[]
   )
    >> metis_tac[ADD_MOD,MOD_EQ_0,DECIDE ``0 * n = 0``]
  );

val MOD_GEQ_2_INCREASES = store_thm
  ("MOD_GEQ_2_INCREASES",
   ``!N x. 2 <= N ==> ~((x + 1) MOD N = x MOD N)``,
   rpt strip_tac >> simp[] >> `0 < N` by simp[]
   >> `(x + 1 + (N - (x MOD N))) MOD N = (x + (N - (x MOD N))) MOD N`
      by metis_tac[ADD_MOD]
   >> `x MOD N < N` by metis_tac[MOD_LESS] >> fs[]
   >> `0 < N` by simp[] >> `x MOD N <= x` by metis_tac[MOD_LESS_EQ]
   >> `(N + ((x + 1) − (x MOD N))) MOD N = (N + (x − (x MOD N))) MOD N` by fs[]
   >> `(x + 1 - (x MOD N)) MOD N = (x - (x MOD N)) MOD N`
         by metis_tac[ADD_MODULUS]
   >> `(x - (x MOD N)) MOD N = 0` by metis_tac[MOD_LEMM]
   >> rw[] >> `((x - (x MOD N)) +1) MOD N = 1` suffices_by fs[]
   >> `(x - (x MOD N)) MOD N = 0 MOD N` by simp[]
   >> `1 MOD N = 1` by simp[] >> metis_tac[ADD_MOD,DECIDE ``0 + 1 = 1``]
  );

val INCREASING_MOD_CYCLES = store_thm
  ("INCREASING_MOD_CYCLES",
   ``!f N. (!j. (f (SUC j) = f j) \/ ((f (SUC j)) = ((f j + 1) MOD N)))
         ∧ (!i. ?k. (i <= k) ∧ ~(f (SUC k) = f k))
         ∧ (f 0 = 0) ∧ (0 < N)
         ==> (!n. (n < N) ==> !i. ?k. (i <= k) ∧ (f k = n))``,
   strip_tac >> strip_tac >> strip_tac
   >> `!a. f a < N` by (
       Induct_on `a` >> fs[]
       >> `(f (SUC a) = f a) ∨ (f (SUC a) = (f a + 1) MOD N)` by simp[] >> fs[]
   )
   >> rpt strip_tac >> CCONTR_TAC
   >> qabbrev_tac `U = { u | u < N ∧ !k. i <= k ==> ~(f k = u)}`
   >> `U ⊆ (count N)` by (
       qunabbrev_tac `U` >> simp[count_def,SUBSET_DEF]
       >> rpt strip_tac >> fs[]
   )
   >> `CARD U <= N` by metis_tac[CARD_COUNT,CARD_SUBSET,FINITE_COUNT]
   >> Cases_on `CARD U < N`
   >- (`0 < CARD U` by (
         `~(U = {})` suffices_by metis_tac[CARD_EQ_0,FINITE_COUNT,PSUBSET_DEF,
                                           PSUBSET_FINITE,
                                           DECIDE ``0 < CARD U = ~(CARD U = 0)``
                                          ]
         >> `?u. u ∈ U` suffices_by metis_tac[MEMBER_NOT_EMPTY]
         >> qexists_tac `n` >> qunabbrev_tac `U` >> fs[] >> rpt strip_tac
         >> metis_tac[]
      )
      >> `!a. ~((f i + a) MOD N ∈ U)` by (
          Induct_on `a` >> fs[] >> rpt strip_tac
          >- (qunabbrev_tac `U` >> fs[] >> metis_tac[DECIDE ``i <= i``])
          >- (qunabbrev_tac `U` >> fs[]
              >> qabbrev_tac `P = \p. k <= p ∧ ~(f (SUC p) = f p)`
              >> qabbrev_tac `p0 = $LEAST P`
              >> `P p0 ∧ !n. n < p0 ==> ~P n` by (
                   `?p. P p` suffices_by metis_tac[LEAST_EXISTS]
                   >> qunabbrev_tac `P` >> fs[]
               )
              >> qunabbrev_tac `P` >> fs[]
              >> `!l. k <= l ∧ l <= p0 ==> (f k = f l)` by (
                   Induct_on `l` >> fs[] >> rpt strip_tac
                   >- metis_tac[]
                   >- (first_x_assum (qspec_then `l` mp_tac) >> simp[]
                       >> Cases_on `k = SUC l` >> fs[] >> rw[]
                      )
               )
              >> `f p0 = f k` by fs[] >> rw[]
              >> `(f (SUC p0) = (f p0 + 1) MOD N)` by metis_tac[]
              >> `i <= SUC p0` by simp[]
              >> `(f p0 + 1) MOD N = (f i + SUC a) MOD N` suffices_by metis_tac[]
              >> rw[] >> metis_tac[DECIDE ``a + (f i + 1) = f i + SUC a``]
             )
       )
      >> `?k. (f i + k) MOD N = n` by (
          `{a | ?k. a = (f i + k) MOD N } = count N` by (
              simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
              >- metis_tac[MOD_LESS]
              >- (qexists_tac `N -(f i MOD N) + (x MOD N)` >> simp[]
                      >> `f i < N` by metis_tac[] >> simp[]
                 )
          )
          >> `n ∈ count N` by simp[count_def]
          >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
          >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
          >> metis_tac[]
          )
      >> `n ∈ U` suffices_by metis_tac[]
      >> qunabbrev_tac `U` >> fs[] >> metis_tac[]
      )
   >- (`CARD U = N` by fs[]
       >> `U = count N`
             by metis_tac[FINITE_COUNT,PSUBSET_FINITE,
                          PSUBSET_DEF,SUBSET_EQ_CARD,CARD_COUNT]
       >> `f i ∈ U`
            by (`f i ∈ count N` suffices_by metis_tac[] >> fs[count_def])
       >> qunabbrev_tac `U` >> fs[] >> metis_tac[DECIDE ``i <= i``]
      )
  );



val _ = export_theory();
