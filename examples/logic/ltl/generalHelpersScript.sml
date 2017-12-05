open HolKernel Parse bossLib boolLib pred_setTheory relationTheory set_relationTheory arithmeticTheory pairTheory listTheory optionTheory prim_recTheory whileTheory rich_listTheory

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
   ``!l1 l2. MEM_EQUAL l1 l2 ==> (set l1 = set l2)``,
   metis_tac[MEM_SUBSET_SET_TO_LIST,SET_EQ_SUBSET,MEM_EQUAL_def]
  );

(* val REM_RIGHT_def = Define` *)
(*     (REM_RIGHT x [] = ([], F)) *)
(*   ∧ (REM_RIGHT x (h::ls) = *)
(*      if h = x *)
(*      then (ls,T) *)
(*      else REM_RIGHT x ls *)
(*     )`; *)

(* val REM_RIGHT_SND_LEMM = store_thm *)
(*   ("REM_RIGHT_LEMM", *)
(*    ``!x l. (SND (REM_RIGHT x l) = (MEM x l))``, *)
(*    Induct_on `l` >> fs[REM_RIGHT_def] >> rpt strip_tac *)
(*    >> Cases_on `x = h` >> fs[] *)
(*   ); *)

(* val MEM_EQUAL_def = Define` *)
(*    (MEM_EQUAL [] [] = T) *)
(*  ∧ (MEM_EQUAL (h::ls) [] = F) *)
(*  ∧ (MEM_EQUAL [] (h::ls) = F) *)
(*  ∧ (MEM_EQUAL (h1::ls1) (h2::ls2) = *)
(*     let (rest,mem) = REM_RIGHT h1 ls2 *)
(*     in if mem *)
(*        then MEM_EQUAL ls1 rest *)
(*        else F *)
(*    )`; *)

(* val MEM_EQUAL_AD_SYMM = store_thm *)
(*   ("MEM_EQUAL_AD_SYMM", *)
(*    ``!l1 l2. ALL_DISTINCT l1 ∧ ALL_DISTINCT l2 *)
(*        ==> (MEM_EQUAL l1 l2 = MEM_EQUAL l2 l1 *)
(*           ∧ (MEM_EQUAL l1 l2 = (set l1 = set l2)))``, *)
(*    Induct_on `l2` >> rpt strip_tac >> fs[MEM_EQUAL_def] *)
(*    >- (Cases_on `l1` >> fs[MEM_EQUAL_def]) *)
(*    >- (Cases_on `l1` >> fs[MEM_EQUAL_def]) *)
(*    >- (Cases_on `l1` >> simp[MEM_EQUAL_def] >> fs[] *)
(*        >> `MEM_EQUAL t l2 = MEM_EQUAL l2 t *)
(*          ∧ MEM_EQUAL t l2 = (set t = set l2)` by metis_tac[] *)
(*        >> Cases_on `MEM_EQUAL t l2` *)
(*        >- (fs[] *)
(*            >> `~SND (REM_RIGHT h' l2)` by metis_tac[MEM,REM_RIGHT_SND_LEMM] *)
(*            >> `~SND (REM_RIGHT h t)` by metis_tac[MEM,REM_RIGHT_SND_LEMM] *)
(*            >> Cases_on `REM_RIGHT h' l2` >> Cases_on `REM_RIGHT h t` >> fs[] *)
(*           ) *)
(*        >- (fs[] >> qabbrev_tac `R_t = FST (REM_RIGHT h t)` *)
(*            >> `~(MEM_EQUAL l2 R_t) *)


(*            >> `?x. (MEM x t ∧ ~MEM x l2) \/ (~MEM x t ∧ MEM x l2)` *)
(*                 by (CCONTR_TAC >> fs[] *)
(*                     >> `!x. MEM x t = MEM x l2` by metis_tac[] *)
(*                     >> `set t = set l2` *)
(*                        by (PURE_REWRITE_TAC[SET_EQ_SUBSET,SUBSET_DEF] *)
(*                            >> rpt strip_tac >> metis_tac[MEM] *)
(*                           ) *)
(*                     >- (`~(h' = x)` by metis_tac[] >> fs[] *)



(*                         >> Cases_on `x = h` >> fs[] *)
(*                         >- (rw[] >> ) *)
(*                        ) *)
(*                    ) *)
(*            ) *)
(*        ) *)
(*    >- (Cases_on `l1` >> fs[MEM_EQUAL_def] >> ) *)


(* ) *)

(* Cases_on `MEM x t` >> fs[] >> ) *)
(* ) *)


(* ) *)
(* ) *)


(* ) *)



(* val MEM_EQUAL_AD_SET = store_thm *)
(*   ("MEM_EQUAL_ALL_DISTINCT", *)
(*  ``!ls1 ls2. ALL_DISTINCT ls1 ∧ ALL_DISTINCT ls2 *)
(*         ==> (MEM_EQUAL ls1 ls2 = (set ls1 = set ls2))``, *)
(*  simp[EQ_IMP_THM] >> rpt strip_tac *)
(*  >- () *)



(* ) *)

val ALL_DISTINCT_PAIRS_LEMM = store_thm
  ("ALL_DISTINCT_PAIRS_LEMM",
   ``!x y1 y2 l.
     ALL_DISTINCT (MAP FST l)
     ∧ (MEM (x,y1) l)
     ∧ (MEM (x,y2) l)
     ==> (y1 = y2)``,
   Induct_on `l` >> fs[ALL_DISTINCT] >> rpt strip_tac
   >- (Cases_on `h` >> fs[])
   >- (fs[MEM_MAP] >> Cases_on `h` >> fs[] >> rw[]
       >> first_x_assum (qspec_then `(q,y2)` mp_tac) >> fs[])
   >- (fs[MEM_MAP] >> Cases_on `h` >> fs[] >> rw[]
       >> first_x_assum (qspec_then `(q,y1)` mp_tac) >> fs[])
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

val FOLDR_APPEND = store_thm
  ("FOLDR_APPEND",
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
   ``!P l. set (FLAT (GROUP_BY P l)) = set l``,
   gen_tac
   >> `!l1 l2 l. (l1 ++ l2 = l)
                 ==> (set (FLAT (GROUP_BY P l2)) = set l2)` by (
       Induct_on `l` >> fs[GROUP_BY_def] >> rpt strip_tac
       >> Cases_on `l1`
       >- (fs[] >> simp[GROUP_BY_def] >> Cases_on `SPAN (P h) l`
           >> `q ++ r = l` by metis_tac[SPAN_APPEND]
           >> fs[] >> `set (FLAT (GROUP_BY P r)) = set r` by metis_tac[]
           >> rw[LIST_TO_SET_APPEND]
          )
       >- (Cases_on `l2` >> fs[GROUP_BY_def] >> rw[]
           >> Cases_on `SPAN (P h'') t'` >> fs[]
           >> `q++r = t'` by metis_tac[SPAN_APPEND]
           >> first_x_assum (qspec_then `t ++ [h''] ++ q` mp_tac) >> simp[]
           >> rpt strip_tac >> rw[LIST_TO_SET_APPEND]
          )
   )
   >> `[] ++ l = l` by simp[] >> metis_tac[]
  );

val ONLY_MINIMAL_def = Define`
    (ONLY_MINIMAL P [] = [])
  ∧ (ONLY_MINIMAL P (x::xs) =
      if EXISTS (λx1. P x1 x) xs
      then ONLY_MINIMAL P xs
      else x::(ONLY_MINIMAL P xs)
    )`;


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
