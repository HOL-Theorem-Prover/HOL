open HolKernel Parse bossLib boolLib gfgTheory listTheory optionTheory pred_setTheory rich_listTheory arithmeticTheory

open sptreeTheory ltlTheory generalHelpersTheory concrRepTheory concrltl2waaTheory

val _ = new_theory "concrGBArep"

val _ = monadsyntax.temp_add_monadsyntax();
val _ = overload_on("monad_bind",``OPTION_BIND``);

val _ = Datatype`
  edgeLabelGBA = <| pos_lab : (α list) ;
                    neg_lab : (α list) ;
                    acc_set : (α ltl_frml) list
                  |>` ;

val _ = Datatype`
  nodeLabelGBA = <| frmls : (α ltl_frml) list |>` ;

val _ = Datatype`
  concrGBA = <| graph : (α nodeLabelGBA, α edgeLabelGBA) gfg ;
                init : (num list) ;
                atomicProp : α list
             |>`;

val gba_trans_concr_def = Define`
  gba_trans_concr ts_lists =
    FOLDR d_conj_concr [(concrEdge [] [] [])] ts_lists `;

val GBA_TRANS_LEMM1 = store_thm
  ("GBA_TRANS_LEMM1",
   ``!x s. MEM x (gba_trans_concr s)
        ==> ((!l. MEM l s
                 ==> (?cE. MEM cE l
                   ∧ (MEM_SUBSET cE.pos x.pos)
                   ∧ (MEM_SUBSET cE.neg x.neg)
                   ∧ (MEM_SUBSET cE.sucs x.sucs)
                     ))
          ∧ (?f. let s_with_ind = GENLIST (λn. (EL n s,n)) (LENGTH s)
               in
                let x1 =
                   FOLDR
                    (λsF e.
                     <|pos := sF.pos ⧺ e.pos; neg := sF.neg ⧺ e.neg;
                       sucs := sF.sucs ⧺ e.sucs|>)
                    (concrEdge [] [] []) (MAP f s_with_ind)
               in (cE_equiv x x1)
                ∧ (!q i. MEM (q,i) s_with_ind
                       ==> MEM (f (q,i)) q))
        ∧ (ALL_DISTINCT x.pos ∧ ALL_DISTINCT x.neg
           ∧ ALL_DISTINCT x.sucs))``,
   Q.HO_MATCH_ABBREV_TAC
    `!x s. MEM x (gba_trans_concr s) ==> A x s ∧ B x s`
   >> `!x s. MEM x (gba_trans_concr s) ==> A x s ∧ (A x s ==> B x s)`
      suffices_by fs[]
   >> qunabbrev_tac `A` >> qunabbrev_tac `B`
   >> Induct_on `s` >> fs[gba_trans_concr_def] >> rpt strip_tac
   >- (fs[cE_equiv_def,MEM_EQUAL_def,MEM_SUBSET_def])
   >- (fs[cE_equiv_def,MEM_EQUAL_def,MEM_SUBSET_def]
       >> fs[d_conj_concr_def,FOLDR_LEMM4] >> qexists_tac `e1` >> simp[]
       >> metis_tac[MEM_SUBSET_APPEND,nub_set,MEM_SUBSET_SET_TO_LIST]
      )
   >- (fs[cE_equiv_def,MEM_EQUAL_def,MEM_SUBSET_def]
       >> fs[d_conj_concr_def,FOLDR_LEMM4]
       >> `∃cE.
            MEM cE l ∧ MEM_SUBSET cE.pos e2.pos ∧
            MEM_SUBSET cE.neg e2.neg ∧ MEM_SUBSET cE.sucs e2.sucs`
          by metis_tac[]
       >> qexists_tac `cE`
       >> metis_tac[MEM_SUBSET_APPEND,MEM_SUBSET_TRANS,nub_set,
                    MEM_SUBSET_SET_TO_LIST]
      )
   >- (Cases_on `s= []` >> fs[]
    >- (fs[d_conj_concr_def,FOLDR_CONS,MEM_MAP]
        >> qexists_tac `
             λ(q,i).
               if (q,i) = (h,0) then e1 else ARB`
        >> simp[] >> fs[d_conj_concr_def,FOLDR_CONS,MEM_MAP]
        >> simp[cE_equiv_def,nub_set,MEM_EQUAL_SET]
       )
    >- (fs[d_conj_concr_def,FOLDR_LEMM4]
       >> first_x_assum (qspec_then `e2` mp_tac) >> simp[] >> strip_tac
       >> qabbrev_tac `s_ind = (GENLIST (λn. (EL n s,n)) (LENGTH s))`
       >> `∃f.
           cE_equiv e2
               (FOLDR
              (λsF e.
                 <|pos := sF.pos ⧺ e.pos; neg := sF.neg ⧺ e.neg;
                  sucs := sF.sucs ⧺ e.sucs|>) (concrEdge [] [] [])
              (MAP f s_ind))
          ∧ (!q i. MEM (q,i) s_ind ==> MEM (f (q,i)) q)
          ∧ ALL_DISTINCT e2.pos ∧ ALL_DISTINCT e2.neg
          ∧ ALL_DISTINCT e2.sucs` by metis_tac[]
       >> qexists_tac `
             λ(q,i).
              if i = 0
              then e1
              else f (q,i-1)` >> simp[]
       >> fs[FOLDR_CONCR_EDGE] >> fs[nub_append] >> rpt strip_tac
       >> fs[concrEdge_component_equality]
       >- (qunabbrev_tac `s_ind` >> fs[]
               >> fs[cE_equiv_def] >> rw[MEM_EQUAL_SET,LIST_TO_SET_FILTER]
               >> (simp[SET_EQ_SUBSET,SUBSET_DEF]
                   >> strip_tac >> fs[GENLIST]
                   >- (rpt strip_tac
                       >> Q.HO_MATCH_ABBREV_TAC
                           `MEM k (FOLDR (λe pr. (g e) ⧺ pr) [] L)`
                       >- (`MEM e1 L`
                             suffices_by metis_tac[MEM_SUBSET_SET_TO_LIST,
                                                   FOLDR_APPEND_LEMM,SUBSET_DEF]
                           >> qunabbrev_tac `L` >> simp[MEM_MAP]
                           >> qexists_tac `(h,0)` >> fs[EL,MEM_GENLIST]
                           >> simp[LENGTH_NOT_NULL,NULL_EQ]
                          )
                       >- (`?e. MEM e L ∧ (MEM k (g e))`
                             suffices_by metis_tac[FOLDR_LEMM6]
                           >> qunabbrev_tac `L` >> simp[MEM_MAP] >> fs[]
                           >> `MEM k
                                (FOLDR (λe pr. g e ⧺ pr) []
                                 (MAP f (GENLIST (λn. (EL n s,n)) (LENGTH s))))`
                               by metis_tac[MEM_EQUAL_SET]
                            >> fs[FOLDR_LEMM6] >> qexists_tac `a` >> strip_tac
                            >- (fs[MEM_MAP] >> qexists_tac `(FST y,SND y+1)`
                                >> simp[] >> fs[MEM_GENLIST]
                                >> Cases_on `SUC n=LENGTH s` >> fs[]
                                >> metis_tac[EL,TL,DECIDE ``n+1 = SUC n``]
                               )
                            >- fs[]
                          )
                      )
                   >- (rpt strip_tac >> fs[FOLDR_LEMM6,MEM_MAP]
                    >- (rw[] >> fs[] >> Cases_on `s = []` >> fs[]
                        >> disj2_tac >> Q.HO_MATCH_ABBREV_TAC `MEM k (g e2)`
                        >> `MEM k
                             (FOLDR (λe pr. g e ⧺ pr) []
                              (MAP f (GENLIST (λn. (EL n s,n)) (LENGTH s))))`
                           suffices_by metis_tac[MEM_EQUAL_SET]
                        >> simp[FOLDR_LEMM6,MEM_GENLIST,MEM_MAP]
                        >> qexists_tac `f (EL (LENGTH s) (h::s),LENGTH s − 1)`
                        >> simp[]
                        >> qexists_tac `(EL (LENGTH s) (h::s),LENGTH s − 1)`
                        >> fs[] >> `0 < LENGTH s` by (Cases_on `s` >> fs[])
                        >> rw[]
                        >> `?n. SUC n = LENGTH s`
                           by (Cases_on `LENGTH s` >> simp[])
                        >> `n = LENGTH s -1` by simp[] >> metis_tac[EL,TL]
                       )
                    >- (fs[MEM_GENLIST] >> rw[] >> fs[]
                        >> Cases_on `n = 0` >> fs[] >> disj2_tac
                        >> Q.HO_MATCH_ABBREV_TAC `MEM k (g e2)`
                        >> `MEM k
                             (FOLDR (λe pr. g e ⧺ pr) []
                                (MAP f (GENLIST (λn. (EL n s,n)) (LENGTH s))))`
                            suffices_by metis_tac[MEM_EQUAL_SET]
                        >> simp[FOLDR_LEMM6,MEM_GENLIST,MEM_MAP]
                        >> qexists_tac `f (EL n (h::s),n-1)`
                        >> simp[]
                        >> qexists_tac `(EL n (h::s),n − 1)`
                        >> fs[] >> `0 < n` by fs[]
                        >> `?p. SUC p = n`
                              by (Cases_on `n` >> simp[])
                        >> `p = n -1` by simp[] >> metis_tac[EL,TL]
                       )
                  )
                  )
              )
       >> qunabbrev_tac `s_ind` >> fs[]
       >> Cases_on `i=0` >> fs[MEM_GENLIST]
       >> `?p. SUC p = i` by (Cases_on `i` >> simp[])
       >> rw[]
       )
       )
   >- (fs[d_conj_concr_def] >> fs[FOLDR_LEMM4] >> fs[all_distinct_nub])
   >- (fs[d_conj_concr_def] >> fs[FOLDR_LEMM4] >> fs[all_distinct_nub])
   >- (fs[d_conj_concr_def] >> fs[FOLDR_LEMM4] >> fs[all_distinct_nub])
  );

val GBA_TRANS_LEMM2 = store_thm
  ("GBA_TRANS_LEMM2",
   ``!s f. (!q i. ((q = EL i s) ∧ i < LENGTH s)
                      ==> MEM (f i) q)
         ==> ?x. cE_equiv x
            (FOLDR
                (λsF e.
                     <|pos := sF.pos ⧺ e.pos; neg := sF.neg ⧺ e.neg;
                 sucs := sF.sucs ⧺ e.sucs|>)
                (concrEdge [] [] []) (MAP f (COUNT_LIST (LENGTH s))))
            ∧ MEM x(gba_trans_concr s)``,
   Induct_on `s` >> fs[gba_trans_concr_def]
   >> rw[FOLDR_CONCR_EDGE]
   >- fs[cE_equiv_def,MEM_EQUAL_def,MEM_SUBSET_def,COUNT_LIST_def]
   >- (first_x_assum (qspec_then `λn. f (n + 1)` mp_tac)
       >> `!i. i < LENGTH s ==> MEM (f (i + 1)) (EL i s)` by (
            rpt strip_tac >> `MEM (f (SUC i)) (EL (SUC i) (h::s))` by fs[]
            >> fs[EL,TL] >> metis_tac[DECIDE ``i+1=SUC i``]
        )
       >> simp[]
       >> rpt strip_tac >> simp[d_conj_concr_def] >> rw[FOLDR_LEMM4]
       >> fs[FOLDR_CONCR_EDGE]
       >> qexists_tac `
            concrEdge
              (nub ((f 0).pos ++ x.pos))
              (nub ((f 0).neg ++ x.neg))
              (nub ((f 0).sucs ++ x.sucs))`
       >> fs[] >> strip_tac
       >- (fs[cE_equiv_def,MEM_EQUAL_SET] >> rpt strip_tac
           >> Q.HO_MATCH_ABBREV_TAC `
               set (g (f 0)) ∪
               set
               (FOLDR (λe pr. (g e) ⧺ pr) []
                      (MAP (λn. f (n + 1)) (COUNT_LIST (LENGTH s)))) =
               set (FOLDR (λe pr. (g e) ⧺ pr) []
                          (MAP f (COUNT_LIST (SUC (LENGTH s)))))`
           >> `MAP f (COUNT_LIST (SUC (LENGTH s)))
               = f 0 :: MAP (λn. f (n + 1)) (COUNT_LIST (LENGTH s))` by (
                simp[COUNT_LIST_def,MAP_MAP_o]
                >> `(f o SUC) = (λn. f (n + 1))` suffices_by fs[]
                >> `!n. (f o SUC) n = (λn. f (n + 1)) n` suffices_by metis_tac[]
                >> fs[SUC_ONE_ADD]
            )
           >> rw[]
          )
       >- (qexists_tac `f 0` >> fs[]
           >> qexists_tac `x` >> fs[FOLDR_CONCR_EDGE,concrEdge_component_equality]
           >> `MEM (f 0) (EL 0 (h::s))`
                by metis_tac[DECIDE ``0 < SUC (LENGTH s)``]
           >> fs[EL,TL]
          )
      )
  );

val GBA_TRANS_LEMM = store_thm
  ("GBA_TRANS_LEMM",
   ``!aP trns_concr_list.
      ALL_DISTINCT (MAP FST trns_concr_list)
   ==>
     let concr_edgs_list = MAP SND trns_concr_list
     in let to_abstr l = MAP (concr2AbstractEdge aP) l
     in set (to_abstr (gba_trans_concr concr_edgs_list))
        = d_conj_set (set (MAP (λ(q,d). (q,set (to_abstr d)))
                               trns_concr_list)) (POW aP)``,
   rpt strip_tac >> fs[] >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
   >> fs[MEM_MAP]
   >- (Q.HO_MATCH_ABBREV_TAC `concr2AbstractEdge aP y ∈ d_conj_set s A`
       >> Cases_on `s = {}`
       >- (qunabbrev_tac `s` >> rw[] >> simp[d_conj_set_def,ITSET_THM]
           >> fs[gba_trans_concr_def,concr2AbstractEdge_def,transformLabel_def]
          )
       >-(
       qabbrev_tac `s_ind =
          GENLIST (λn. (EL n (MAP SND trns_concr_list),n))
                  (LENGTH (MAP SND trns_concr_list))`
       >> `?f. cE_equiv y
          (FOLDR
              (λsF e.
                   <|pos := sF.pos ⧺ e.pos; neg := sF.neg ⧺ e.neg;
                     sucs := sF.sucs ⧺ e.sucs|>) (concrEdge [] [] [])
              (MAP f s_ind))
              ∧ (!q i. MEM (q,i) s_ind ==> MEM (f (q,i)) q)`
           by metis_tac[GBA_TRANS_LEMM1]
       >> qabbrev_tac
            `a_sel = λq.
              if ?d i. (q,d) = EL i trns_concr_list
                     ∧ i < LENGTH trns_concr_list
              then (let d = @(x,i). (q,x) = EL i trns_concr_list
                                  ∧ MEM (x,i) s_ind
                    in transformLabel aP (f d).pos (f d).neg)
              else ARB`
       >> qabbrev_tac
           `e_sel = λq.
             if ?d i. (q,d) = EL i trns_concr_list
                    ∧ i < LENGTH trns_concr_list
             then (let d = @(x,i). (q,x) = EL i trns_concr_list
                                 ∧ MEM (x,i) s_ind
                   in set ((f d).sucs))
             else ARB`
       >> qabbrev_tac `Y =
                  (FOLDR
                       (λsF e.
                            <|pos := sF.pos ⧺ e.pos; neg := sF.neg ⧺ e.neg;
                        sucs := sF.sucs ⧺ e.sucs|>) (concrEdge [] [] [])
                       (MAP f s_ind))`
       >> `concr2AbstractEdge aP Y ∈ d_conj_set s A`
            suffices_by metis_tac[C2A_EDGE_CE_EQUIV]
       >> `concr2AbstractEdge aP Y =
            ((POW aP) ∩ BIGINTER {a_sel q | q ∈ IMAGE FST s},
             BIGUNION {e_sel q | q ∈ IMAGE FST s})` by (
            qunabbrev_tac `Y`
            >> simp[concr2AbstractEdge_def,FOLDR_LEMM6]
            >> rw[FOLDR_CONCR_EDGE] >> simp[concr2AbstractEdge_def]
            >> rpt strip_tac
            >- (simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
             >- (qunabbrev_tac `A` >> metis_tac[TRANSFORMLABEL_AP,SUBSET_DEF])
             >- (`x ∈ a_sel q` suffices_by rw[]
                 >> qunabbrev_tac `s` >> qunabbrev_tac `a_sel` >> fs[]
                 >> `∃d i. (FST x',d) = EL i trns_concr_list
                          ∧ i < LENGTH trns_concr_list` by (
                    fs[MEM_ZIP,MEM_EL]
                    >> qexists_tac `SND (EL n' trns_concr_list)`
                    >> qexists_tac `n'` >> fs[LENGTH_MAP,EL_MAP]
                    >> Cases_on `EL n' trns_concr_list` >> fs[]
                 )
                 >> `x ∈ transformLabel aP
                       (f (@(x,i). (FST x',x) = EL i trns_concr_list
                                 ∧ MEM (x,i) s_ind)).pos
                       (f (@(x,i). (FST x',x) = EL i trns_concr_list
                                 ∧ MEM (x,i) s_ind)).neg`
                  suffices_by metis_tac[]
               >> qabbrev_tac `D = (@(x,i). (FST x',x) = EL i trns_concr_list
                                          ∧ MEM (x,i) s_ind)`
               >> `(FST x',FST D) = EL (SND D) trns_concr_list
                   ∧ MEM D s_ind` by (
                   `(λk. (FST x',FST k) = EL (SND k) trns_concr_list
                         ∧ MEM k s_ind) D` suffices_by fs[]
                   >> qunabbrev_tac `D` >> Q.HO_MATCH_ABBREV_TAC `(J ($@ Q))`
                   >> HO_MATCH_MP_TAC SELECT_ELIM_THM >> qunabbrev_tac `J`
                   >> qunabbrev_tac `Q` >> fs[] >> rpt strip_tac
                   >- (qunabbrev_tac `s_ind` >> simp[MEM_GENLIST,MEM_EL]
                       >> qexists_tac `(d,i)` >> fs[EL_MAP] >> rw[]
                       >> Cases_on `EL i trns_concr_list` >> fs[]
                      )
                   >- (Cases_on `x''` >> fs[])
                   >- (Cases_on `x''` >> fs[])
               )
               >> `MEM (f D) (MAP f s_ind)` by (
                    simp[MEM_MAP] >> qexists_tac `D` >> fs[]
                    >> qexists_tac `(FST x',D)` >> fs[]
               )
               >> metis_tac[TRANSFORMLABEL_SUBSET,FOLDR_APPEND_LEMM,SUBSET_DEF]
                )
             >- (`!q. MEM q (MAP FST trns_concr_list) ==> x ∈ a_sel q` by (
                   rpt strip_tac >> fs[MEM_MAP]
                   >> first_x_assum (qspec_then `a_sel q` mp_tac)
                   >> simp[] >> Q.HO_MATCH_ABBREV_TAC `(Q ==> B) ==> B`
                   >> `Q` suffices_by fs[] >> qunabbrev_tac `Q`
                   >> qexists_tac `q` >> rw[]
                   >> qunabbrev_tac `s` >> simp[MEM_MAP]
                   >> rename [`MEM k trns_concr_list`]
                   >> qexists_tac
                        `(λ(q,d). (q,set (MAP (concr2AbstractEdge aP) d))) k`
                   >> simp[]
                   >> Cases_on `k` >> simp[] >> qexists_tac `(q,r)`
                   >> simp[]
                )
                >> `(∀e. MEM e (MAP f s_ind)
                      ⇒ x ∈ transformLabel aP e.pos e.neg) ∧ x ∈ POW aP`
                   suffices_by metis_tac[TRANSFORMLABEL_FOLDR]
                >> rpt strip_tac >> fs[MEM_MAP]
                >> qunabbrev_tac `s_ind` >> fs[MEM_GENLIST]
                >> `MEM (EL n trns_concr_list) trns_concr_list`
                        by metis_tac[EL_MEM]
                >> `?q d. EL n trns_concr_list = (q,d)` by (
                     Cases_on `EL n trns_concr_list` >> fs[]
                )
                >> `MEM (q,d) trns_concr_list ∧ FST (q,d) = q` by fs[]
                >> `x ∈ a_sel q` by metis_tac[MEM_EL]
                >> qunabbrev_tac `a_sel` >> fs[]
                >> `x ∈
                     transformLabel aP
                     (f (@(x,i). (q,x) = EL i trns_concr_list
                               ∧ i < LENGTH trns_concr_list
                               ∧ (x = EL i (MAP SND trns_concr_list)))).pos
                     (f (@(x,i). (q,x) = EL i trns_concr_list
                               ∧ i < LENGTH trns_concr_list
                               ∧ x = EL i (MAP SND trns_concr_list))).neg` by (
                  `∃d i. (q,d) = EL i trns_concr_list
                       ∧ (i < LENGTH trns_concr_list)` suffices_by metis_tac[]
                  >> qexists_tac `d` >> fs[] >> metis_tac[MEM_EL]
                )
                >> `(@(x,i). (q,x) = EL i trns_concr_list
                            ∧ i < LENGTH trns_concr_list
                            ∧ (x = EL i (MAP SND trns_concr_list))) = (d,n)` by (
                    `(λj. (j = (d,n)))
                       ($@ (λ(x,i). (q,x) = EL i trns_concr_list
                                  ∧ i < LENGTH trns_concr_list
                                  ∧ (x = EL i (MAP SND trns_concr_list))))`
                      suffices_by fs[]
                    >> Q.HO_MATCH_ABBREV_TAC `Q ($@ M)`
                    >> HO_MATCH_MP_TAC SELECT_ELIM_THM >> qunabbrev_tac `Q`
                    >> rpt strip_tac >> fs[] >> qunabbrev_tac `M`
                    >- (qexists_tac `(d,n)` >> fs[EL_MAP])
                    >- (Cases_on `x'` >> fs[] >> `r = n` suffices_by fs[EL_MAP]
                        >> `EL n (MAP FST trns_concr_list) = q` by fs[EL_MAP]
                        >> `EL r (MAP FST trns_concr_list) =
                             FST (EL r trns_concr_list)` by metis_tac[EL_MAP]
                        >> rw[] >> Cases_on `EL r trns_concr_list`
                        >> rw[]
                        >> `EL r (MAP FST trns_concr_list) =
                             EL n (MAP FST trns_concr_list)` by fs[]
                        >> metis_tac[ALL_DISTINCT_EL_IMP,LENGTH_MAP]
                       )
                )
                >> `EL n (MAP SND trns_concr_list) = d` by fs[EL_MAP]
                >> rw[] >> metis_tac[]
                )
               )
            >- (`BIGUNION {e_sel q | ?x. q = FST x ∧ x ∈ s} =
                 BIGUNION {set d.sucs | MEM d
                                        (MAP f s_ind)}`
                 by (
                  `!q r i. (q,r) = EL i trns_concr_list
                         ∧ i < LENGTH trns_concr_list
                      ==> ((?d n. (q,d) = EL n trns_concr_list)
                         ∧ ((r,i) =
                              @(x,i). (q,x) = EL i trns_concr_list
                                    ∧ MEM (x,i) s_ind)
                         ∧ ?n. n < LENGTH s_ind ∧ (r,i) = EL n s_ind)` by (
                      rpt strip_tac
                      >- metis_tac[]
                      >- (`(λk. (k = (r,i)))
                              ($@ (λ(x,j). (q,x) = EL j trns_concr_list
                                         ∧ ?n. (n < LENGTH s_ind)
                                             ∧ (x,j) = EL n s_ind))`
                            suffices_by fs[MEM_EL]
                         >> Q.HO_MATCH_ABBREV_TAC `Q ($@ M)`
                         >> HO_MATCH_MP_TAC SELECT_ELIM_THM >> qunabbrev_tac `Q`
                         >> rpt strip_tac >> fs[] >> qunabbrev_tac `M`
                         >- (qexists_tac `(r,i)` >> fs[]
                             >> qunabbrev_tac `s_ind` >> qexists_tac `i`
                             >> simp[LENGTH_GENLIST,EL_MAP]
                             >> Cases_on `EL i trns_concr_list` >> fs[]
                            )
                         >- (Cases_on `x` >> fs[]
                             >> `EL i (MAP FST trns_concr_list) =
                                  FST (EL i trns_concr_list)` by metis_tac[EL_MAP]
                             >> `MEM (q',r') s_ind` by metis_tac[MEM_EL]
                             >> qunabbrev_tac `s_ind` >> fs[MEM_GENLIST]
                             >> `EL r' (MAP FST trns_concr_list) =
                                  FST (EL r' trns_concr_list)` by metis_tac[EL_MAP]
                             >> `r' = i` suffices_by
                                  (rw[] >> fs[] >> Cases_on `EL i trns_concr_list`
                                   >> fs[])
                             >> Cases_on `EL i trns_concr_list`
                             >> Cases_on `EL r' trns_concr_list` >> rw[] >> fs[]
                             >> metis_tac[ALL_DISTINCT_EL_IMP,LENGTH_MAP])
                         )
                      >- (qunabbrev_tac `s_ind` >> qexists_tac `i`
                          >> simp[LENGTH_GENLIST,EL_MAP]
                          >> Cases_on `EL i trns_concr_list` >> fs[]
                         )
                  )
                  >> qunabbrev_tac `e_sel` >> simp[MEM_MAP] >> qunabbrev_tac `s`
                  >> simp[MEM_MAP,SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                  >- (rename [`MEM k trns_concr_list`] >> fs[MEM_EL]
                             >> rename[`k = EL i trns_concr_list`]
                             >> Cases_on `k` >> fs[] >> rw[]
                             >> qexists_tac `set (f (r,i)).sucs` >> fs[]
                             >> first_x_assum (qspec_then `q` mp_tac) >> simp[]
                             >> strip_tac
                             >> first_x_assum (qspec_then `r` mp_tac) >> simp[]
                             >> strip_tac
                             >> first_x_assum (qspec_then `i` mp_tac) >> simp[]
                             >> strip_tac >> rpt strip_tac
                             >- metis_tac[]
                             >- (qexists_tac `f (r,i)` >> fs[] >> rpt strip_tac
                                >- metis_tac[MEM_EL]
                                >- metis_tac[MEM_EL]
                                >- (qexists_tac `(r,i)` >> fs[]
                                    >> qexists_tac `n''` >> fs[]
                                   )
                                )
                     )
                  >- (qunabbrev_tac `s_ind` >> fs[MEM_GENLIST]
                      >> `MEM (EL n trns_concr_list) trns_concr_list` by fs[EL_MEM]
                      >> `?q r. EL n trns_concr_list = (q,r)` by (
                             Cases_on `EL n trns_concr_list` >> fs[]
                       )
                      >> first_x_assum (qspec_then `q` mp_tac) >> simp[]
                      >> strip_tac
                      >> first_x_assum (qspec_then `r` mp_tac) >> simp[]
                      >> strip_tac
                      >> first_x_assum (qspec_then `n` mp_tac) >> simp[]
                      >> rpt strip_tac
                      >> qexists_tac `set (f (r,n)).sucs` >> fs[]
                      >> fs[] >> rpt strip_tac >> rw[] >> fs[]
                      >- fs[EL_MAP]
                      >- (qexists_tac `q`>> fs[] >> rw[]
                          >- metis_tac[]
                          >- metis_tac[]
                          >- (qexists_tac `(q,set (MAP (concr2AbstractEdge aP)r))`
                              >> fs[] >> qexists_tac `(q,r)` >> fs[])
                         )
                     )
               )
                 >> metis_tac[FOLDR_APPEND_LEMM,LIST_TO_SET,UNION_EMPTY]
               )
        )
       >> `(∀q d. (q,d) ∈ s ⇒ (a_sel q,e_sel q) ∈ d
             ∧ BIGINTER {a_sel q | q ∈ IMAGE FST s} ⊆ a_sel q)
           ∧ BIGINTER {a_sel q | q ∈ IMAGE FST s} ⊆ A`
           suffices_by metis_tac[FINITE_LIST_TO_SET,D_CONJ_SET_LEMM3]
       >> `!q r. (q,r) ∈ s
           ==> (?d i. (q,d) = EL i trns_concr_list
                 ∧ (r = set (MAP (concr2AbstractEdge aP) d))
                 ∧ (i < LENGTH trns_concr_list)
                 ∧ ((@(x,i). (q,x) = EL i trns_concr_list
                           ∧ MEM (x,i) s_ind) = (d,i)))` by (
            rpt strip_tac >> qunabbrev_tac `s` >> fs[MEM_MAP]
            >> Cases_on `y'` >> fs[MEM_EL]
            >> `(r',n') =
                 (@(x,i). (q',x) = EL i trns_concr_list
               ∧ (MEM (x,i) s_ind))` by (
                `(λk. (k = (r',n')))
                    ($@ (λ(x,i). (q',x) = EL i trns_concr_list
                               ∧ MEM (x,i) s_ind))`
                  suffices_by fs[]
                >> Q.HO_MATCH_ABBREV_TAC `Q ($@ M)`
                >> HO_MATCH_MP_TAC SELECT_ELIM_THM >> qunabbrev_tac `Q`
                >> rpt strip_tac >> fs[] >> qunabbrev_tac `M`
                >- (qexists_tac `(r',n')` >> fs[]
                    >> qunabbrev_tac `s_ind` >> simp[MEM_GENLIST,EL_MAP]
                    >> Cases_on `EL n' trns_concr_list` >> fs[])
                >- (Cases_on `x'` >> fs[]
                    >> `n' = r''` suffices_by (
                         Cases_on `EL n' trns_concr_list`
                         >> Cases_on `EL r'' trns_concr_list` >> rw[] >> fs[]
                     ) >> rw[]
                    >> `EL n' (MAP FST trns_concr_list) =
                         FST (EL n' trns_concr_list)` by metis_tac[EL_MAP]
                    >> qunabbrev_tac `s_ind` >> fs[MEM_GENLIST]
                    >> `EL r'' (MAP FST trns_concr_list) =
                         FST (EL r'' trns_concr_list)` by metis_tac[EL_MAP]
                    >> Cases_on `EL n' trns_concr_list`
                    >> Cases_on `EL r'' trns_concr_list` >> rw[] >> fs[]
                    >> metis_tac[ALL_DISTINCT_EL_IMP,LENGTH_MAP]
                   )
            )
            >> qexists_tac `r'` >> qexists_tac `n'` >> fs[]
            >> simp[MEM_EL] >> qunabbrev_tac `s_ind` >> simp[MEM_GENLIST,EL_MAP]
        )
       >> rpt strip_tac
       >- (qunabbrev_tac `a_sel` >> qunabbrev_tac `e_sel`
           >> first_x_assum (qspec_then `q` mp_tac) >> rpt strip_tac
           >> first_x_assum (qspec_then `d` mp_tac) >> simp[] >> strip_tac
           >> simp[MEM_MAP]
           >> qabbrev_tac `D = (d',i)`
           >> qexists_tac `f D`
           >> `(transformLabel aP (f D).pos (f D).neg, set (f D).sucs) =
                  concr2AbstractEdge aP (f D) ∧ MEM (f D) d'`
              suffices_by metis_tac[]
           >> Cases_on `f D` >> simp[concr2AbstractEdge_def]
           >> `MEM (d',i) s_ind` suffices_by metis_tac[]
           >> qunabbrev_tac `s_ind` >> simp[MEM_GENLIST]
           >> simp[EL_MAP]
           >> Cases_on `EL i trns_concr_list` >> fs[]
          )
       >- (HO_MATCH_MP_TAC IN_BIGINTER_SUBSET >> fs[]
           >> qexists_tac `q` >> fs[] >> qexists_tac `(q,d)` >> fs[]
          )
       >- (HO_MATCH_MP_TAC BIGINTER_SUBSET >> rpt strip_tac
           >- (fs[] >> Cases_on `x'` >> rw[]
               >> qunabbrev_tac `a_sel` >> fs[]
               >> metis_tac[TRANSFORMLABEL_AP]
              )
           >- (`?x. x ∈ {a_sel q | q ∈ IMAGE FST s}`
                 suffices_by metis_tac[MEMBER_NOT_EMPTY]
               >> simp[] >> metis_tac[MEMBER_NOT_EMPTY]
              )
          )
        )
      )
   >- (
    qabbrev_tac `s = set
                         (MAP (λ(q,d). (q,set (MAP (concr2AbstractEdge aP) d)))
                              trns_concr_list)`
    >> Cases_on `s = {}`
    >- (qunabbrev_tac `s` >> rw[] >> fs[d_conj_set_def,ITSET_THM]
        >> simp[gba_trans_concr_def,concr2AbstractEdge_def,transformLabel_def]
       )
    >- (
     `?a e. x = (a,e)` by (Cases_on `x` >> fs[])
     >> `∃f_a f_e.
          ∀q d.
          ((q,d) ∈ s ⇒
                 (f_a q d,f_e q d) ∈ d ∧ a ⊆ f_a q d ∧ f_e q d ⊆ e)
          ∧ ((POW aP) ∩ BIGINTER {f_a q d | (q,d) ∈ s} = a)
          ∧ (BIGUNION {f_e q d | (q,d) ∈ s} = e)`
        by metis_tac[D_CONJ_SET_LEMM2_STRONG,FINITE_LIST_TO_SET]
     >> qunabbrev_tac `s` >> fs[MEM_MAP]
     >> qabbrev_tac `c2a = concr2AbstractEdge aP` >> fs[]
     >> `?f. !q d d_c i.
          ((q,d) = (λ(q,d). (q,set (MAP c2a d))) (q,d_c))
          ∧ ((q,d_c) = EL i trns_concr_list
             ∧ i < LENGTH trns_concr_list)
          ==> (MEM (f i) d_c
             ∧ (c2a (f i) = (f_a q d,f_e q d)))` by (
         qabbrev_tac `sel =
           λi.
            if i < LENGTH trns_concr_list
            then
             let (q,d_c) = EL i trns_concr_list
             in let d =
                      set (MAP (concr2AbstractEdge aP) d_c)
             in @cE. MEM cE d_c
                   ∧ concr2AbstractEdge aP cE = (f_a q d,f_e q d)
            else ARB`
         >> qexists_tac `sel` >> fs[] >> rpt gen_tac >> strip_tac
         >> `sel i =
                @cE.
                  MEM cE d_c
                  ∧ concr2AbstractEdge aP cE =
                     (f_a q (set (MAP c2a d_c)),
                      f_e q (set (MAP c2a d_c)))` by (
             qunabbrev_tac `sel` >> fs[] >> simp[]
             >> Cases_on `EL i trns_concr_list` >> fs[]
         )
         >> fs[]
         >> Q.HO_MATCH_ABBREV_TAC
              `MEM ($@ P) d_c ∧ c2a ($@ P) = (A,E)`
         >> qabbrev_tac `Q = λc. MEM c d_c ∧ c2a c = (A,E)`
         >> `Q ($@ P)` suffices_by fs[] >> HO_MATCH_MP_TAC SELECT_ELIM_THM
         >> qunabbrev_tac `P` >> qunabbrev_tac `Q` >> fs[]
         >> qabbrev_tac `d = set (MAP c2a d_c)` >> fs[]
         >> first_x_assum (qspec_then `q` mp_tac) >> rpt strip_tac
         >> first_x_assum (qspec_then `d` mp_tac) >> rpt strip_tac
         >> `(f_a q d,f_e q d) ∈ d ∧ a ⊆ f_a q d ∧ f_e q d ⊆ e` by (
           `∃y.
            (q,d) = (λ(q,d). (q,set (MAP (concr2AbstractEdge aP) d))) y
                  ∧ MEM y trns_concr_list` suffices_by fs[]
           >> qexists_tac `(q,d_c)` >> rw[] >> fs[EL_MEM]
         )
         >> qunabbrev_tac `d`
         >> rw[] >> fs[MEM_MAP] >> metis_tac[]
     )
     >> `!d_c i. d_c = EL i (MAP SND trns_concr_list)
               ∧ i < LENGTH (MAP SND trns_concr_list)
                          ==> MEM (f i) d_c` by (
         simp[MEM_MAP,EL_MAP] >> rpt strip_tac
         >> qabbrev_tac `d_c = SND (EL i trns_concr_list)`
         >> `?q. MEM (q,d_c) trns_concr_list
               ∧ EL i trns_concr_list = (q,d_c)` by (
             `MEM (EL i trns_concr_list) trns_concr_list` by fs[EL_MEM]
             >> Cases_on `EL i trns_concr_list` >> qunabbrev_tac `d_c`
             >> fs[] >> metis_tac[]
         )
         >> first_x_assum (qspec_then `q` mp_tac) >> rpt strip_tac
         >> first_x_assum (qspec_then `set (MAP c2a d_c)` mp_tac)
         >> rpt strip_tac
         >> first_x_assum (qspec_then `d_c` mp_tac) >> rw[]
     )
     >> IMP_RES_TAC GBA_TRANS_LEMM2
     >> `c2a
          (FOLDR
          (λsF e.
               <|pos := sF.pos ⧺ e.pos; neg := sF.neg ⧺ e.neg;
           sucs := sF.sucs ⧺ e.sucs|>) (concrEdge [] [] [])
          (MAP f (COUNT_LIST (LENGTH (MAP SND trns_concr_list))))) = (a,e)`
         suffices_by metis_tac[C2A_EDGE_CE_EQUIV]
     >> rw[FOLDR_CONCR_EDGE] >> qunabbrev_tac `c2a`
     >> simp[concr2AbstractEdge_def]
     >> `(POW aP ∩ BIGINTER
         {f_a q d |
          ∃y.
           (q,d) =
             (λ(q,d). (q,set (MAP (concr2AbstractEdge aP) d))) y
                     ∧ MEM y trns_concr_list} = a)
       ∧ (BIGUNION
          {f_e q d |
           ∃y.
            (q,d) =
           (λ(q,d). (q,set (MAP (concr2AbstractEdge aP) d))) y
          ∧ MEM y trns_concr_list} = e)` by (
       `∃q d y.
        (q,d) = (λ(q,d). (q,set (MAP (concr2AbstractEdge aP) d))) y
      ∧ MEM y trns_concr_list` suffices_by (rpt strip_tac >> fs[] >> metis_tac[])
       >> `?q d. MEM (q,d) trns_concr_list` by (
           Cases_on `trns_concr_list` >> rw[] >> Cases_on `h` >> metis_tac[])
       >> qexists_tac `q` >> fs[]
       >> qexists_tac `set (MAP (concr2AbstractEdge aP) d)` >> fs[]
       >> qexists_tac `(q,d)` >> fs[]
     )
     >> strip_tac
     >- (simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> fs[]
      >- (rw[]
          >- (fs[transformLabel_def] >> metis_tac[FOLDR_INTER,SUBSET_DEF])
          >- (`?d_c. y = (q,d_c)` by (Cases_on `y` >> fs[])
              >> `?i. (q,d_c) = EL i trns_concr_list
                    ∧ i < LENGTH trns_concr_list` by metis_tac[MEM_EL]
              >> `MEM (f i) d_c
                ∧ concr2AbstractEdge aP (f i) =
                   (f_a q (set (MAP (concr2AbstractEdge aP) d_c)),
                    f_e q (set (MAP (concr2AbstractEdge aP) d_c)))`
               by metis_tac[]
              >> `(MEM_SUBSET (f i).pos
                    (FOLDR (λe pr. e.pos ⧺ pr)
                      [] (MAP f (COUNT_LIST
                                     (LENGTH (MAP SND trns_concr_list))))))
                ∧ (MEM_SUBSET (f i).neg
                    (FOLDR (λe pr. e.neg ⧺ pr)
                      [] (MAP f (COUNT_LIST
                                     (LENGTH (MAP SND trns_concr_list))))))`
                suffices_by (
                Cases_on `f i` >> fs[concr2AbstractEdge_def]
                >> Cases_on `EL i trns_concr_list` >> fs[] >> rw[]
                >> metis_tac[TRANSFORMLABEL_SUBSET,SUBSET_DEF]
              )
              >> `MEM (f i) (MAP f (COUNT_LIST (LENGTH trns_concr_list)))`
                     suffices_by (simp[] >> metis_tac[FOLDR_APPEND_LEMM])
              >> simp[MEM_MAP] >> qexists_tac `i` >> fs[]
              >> metis_tac[MEM_COUNT_LIST]
             )
          )
      >- (rw[] >> fs[IN_INTER,IN_BIGINTER]
          >> HO_MATCH_MP_TAC TRANSFORMLABEL_FOLDR >> rpt strip_tac
          >- (POP_ASSUM mp_tac >> simp[MEM_MAP] >> rpt strip_tac
              >> `y < LENGTH trns_concr_list` by fs[MEM_COUNT_LIST]
              >> `MEM (f y) (EL y (MAP SND trns_concr_list))` by metis_tac[]
              >> qabbrev_tac `d_c = EL y (MAP SND trns_concr_list)`
              >> `?q. (q,d_c) = EL y trns_concr_list` by (
                   `MEM (EL y trns_concr_list) trns_concr_list` by fs[EL_MEM]
                   >> qunabbrev_tac `d_c` >> fs[]
                   >> Cases_on `EL y trns_concr_list` >> rw[] >> simp[EL_MAP]
               )
              >> rw[]
              >> qabbrev_tac `d = set (MAP (concr2AbstractEdge aP) d_c)`
              >> first_x_assum (qspec_then `f_a q d` mp_tac)
              >> simp[] >> rpt strip_tac
              >> `x ∈ f_a q d` by (
                 `(∃q' d'.
                      f_a q d = f_a q' d'
                    ∧ ∃y.
                      (q',d') = (λ(q,d).
                                  (q,set (MAP (concr2AbstractEdge aP) d))) y
                    ∧ MEM y trns_concr_list)` suffices_by metis_tac[]
                 >> qexists_tac `q` >> qexists_tac `d` >> fs[]
                 >> qexists_tac `(q,d_c)` >> fs[EL_MEM]
               )
              >> first_x_assum (qspec_then `q` mp_tac) >> rpt strip_tac
              >> first_x_assum (qspec_then `d_c` mp_tac) >> simp[]
              >> rpt strip_tac >> first_x_assum (qspec_then `y` mp_tac)
              >> simp[]
              >> Cases_on `f y` >> fs[concr2AbstractEdge_def]
             )
          >- fs[]
         )
        )
     >- (rw[] >> Q.HO_MATCH_ABBREV_TAC `S1 = BIGUNION S2`
         >> `S2 = {set x.sucs |
                     MEM x (MAP f (COUNT_LIST (LENGTH trns_concr_list))) }`
            suffices_by (
            qunabbrev_tac `S1` >> qunabbrev_tac `S2` >> fs[] >> rw[]
            >> metis_tac[LIST_TO_SET,FOLDR_APPEND_LEMM,UNION_EMPTY]
          )
         >> qunabbrev_tac `S2` >> fs[] >> simp[SET_EQ_SUBSET,SUBSET_DEF]
         >> rpt strip_tac
         >- (`?d_c. y = (q,d_c)` by (Cases_on `y` >> fs[])
             >> `?i. i < LENGTH trns_concr_list
                   ∧ EL i trns_concr_list = (q,d_c)` by metis_tac[MEM_EL]
             >> `concr2AbstractEdge aP (f i) =
                 (f_a q (set (MAP (concr2AbstractEdge aP) d_c)),
                  f_e q (set (MAP (concr2AbstractEdge aP) d_c)))`
                by metis_tac[]
             >> Cases_on `f i` >> fs[concr2AbstractEdge_def]
             >> qexists_tac `f i` >> rw[] >> simp[MEM_MAP]
             >> qexists_tac `i` >> fs[] >> metis_tac[MEM_COUNT_LIST]
            )
         >- (fs[MEM_MAP]
             >> `?j. j = EL y trns_concr_list` by metis_tac[MEM_EL,MEM_COUNT_LIST]
             >> `?q d_c. j = (q,d_c)` by (Cases_on `j` >> fs[])
             >> `y < LENGTH (trns_concr_list)` by fs[MEM_COUNT_LIST]
             >> `concr2AbstractEdge aP (f y) =
                (f_a q (set (MAP (concr2AbstractEdge aP) d_c)),
                 f_e q (set (MAP (concr2AbstractEdge aP) d_c)))`
                by metis_tac[]
             >> qabbrev_tac `d = set (MAP (concr2AbstractEdge aP) d_c)`
             >> qexists_tac `q` >> qexists_tac `d` >> fs[]
             >> Cases_on `f y` >> fs[concr2AbstractEdge_def]
             >> rw[] >> qexists_tac `(q,d_c)` >> fs[EL_MEM]
            )
        )
    )
   )
  );

val tlg_concr_def = Define`
  tlg_concr (t1,acc_t1) (t2,acc_t2) =
    ((MEM_SUBSET t1.pos t2.pos)
  ∧ (MEM_SUBSET t1.neg t2.neg)
  ∧ (MEM_SUBSET t1.sucs t2.sucs)
  ∧ (MEM_SUBSET acc_t2 acc_t1))`;

val acc_cond_concr_def = Define`
  acc_cond_concr cE f f_trans =
     (~(MEM f cE.sucs)
   \/ (EXISTS (λcE1. MEM_SUBSET cE1.pos cE.pos
                   ∧ MEM_SUBSET cE1.neg cE.neg
                   ∧ MEM_SUBSET cE1.sucs cE.sucs
                   ∧ ~(MEM f cE1.sucs)) f_trans))`;

val inGBA_def = Define`
  inGBA g qs =
    let gbaNodes = MAP SND (toAList g.nodeInfo)
    in EXISTS (λn. MEM_EQUAL n.frmls qs) gbaNodes`;

val addNodeToGBA_def = Define`
  addNodeToGBA g qs =
    if inGBA g qs
    then g
    else addNode (nodeLabelGBA qs) g`;

val ADDNODE_GBA_NOTWF_LEMM = store_thm
  ("ADDNODE_GBA_NOTWF_LEMM",
   ``!g qs. { x | inGBA (addNodeToGBA g qs) x } =
             { x | inGBA g x } ∪ {qs} ``,
   simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
   >> fs[addNodeToGBA_def] >> Cases_on `inGBA g qs`
   >> fs[] >> fs[inGBA_def]
   >- (fs[EXISTS_MEM,MEM_MAP] >> `?i. y = (i,n)` by (Cases_on `y` >> fs[])
       >> `lookup i (addNode (nodeLabelGBA qs) g).nodeInfo = SOME n`
            by metis_tac[MEM_toAList]
       >> disj1_tac >> qexists_tac `n` >> fs[] >> qexists_tac `y` >> fs[]
       >> `lookup i g.nodeInfo = SOME n` suffices_by metis_tac[MEM_toAList]
       >> fs[addNode_def] >> 
)
)



val addEdgeToGBA_def = Define`
  addEdgeToGBA g id eL suc =
    case findNode (λ(i,q). MEM_EQUAL q.frmls suc) g of
      | SOME (i,q) =>  addEdge id (eL,i) g
      | NONE => NONE`;


val extractGBATrans_def = Define`
  extractGBATrans aP g q =
    do (id,n) <- findNode (λ(i,n). ((set n.frmls) = q)) g ;
       fls <- lookup id g.followers ;
       SOME (
         CAT_OPTIONS
             (MAP (λ(eL,i).
                    do nL <- lookup i g.nodeInfo ;
                       SOME (
                        (transformLabel aP eL.pos_lab eL.neg_lab,
                         set nL.frmls)
                       )
                    od
                  ) fls
             )
       )
     od `;

val _ = export_theory();
