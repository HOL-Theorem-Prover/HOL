open HolKernel Parse bossLib boolLib gfgTheory listTheory optionTheory pred_setTheory rich_listTheory arithmeticTheory sortingTheory relationTheory

open sptreeTheory ltlTheory generalHelpersTheory concrRepTheory concrltl2waaTheory buechiATheory

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
                all_acc_frmls : (α ltl_frml) list;
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
                              >> rename [‘n + 1 = LENGTH s’,
                                         ‘EL (LENGTH s) (h::s)’]
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
                      >> rename [‘MEM x (_ (if n = 0 then _ else _))’]
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

val GBA_TRANS_LEMM3 = store_thm
  ("GBA_TRANS_LEMM3",
   ``(!s x t. MEM x (gba_trans_concr t) ∧ MEM s x.sucs
             ==> (?l ce. MEM l t ∧ MEM ce l ∧ MEM s ce.sucs))
   ∧ (!s x t. MEM x (gba_trans_concr t) ∧ MEM s x.pos
         ==> (?l ce. MEM l t ∧ MEM ce l ∧ MEM s ce.pos))
   ∧ (!s x t. MEM x (gba_trans_concr t) ∧ MEM s x.neg
         ==> (?l ce. MEM l t ∧ MEM ce l ∧ MEM s ce.neg))``,
   rpt conj_tac
   >> Induct_on `t` >> rpt strip_tac >> fs[gba_trans_concr_def]
   >- (fs[concrEdge_component_equality] >> metis_tac[MEMBER_NOT_EMPTY,MEM])
   >- (fs[d_conj_concr_def,FOLDR_LEMM4,concrEdge_component_equality]
       >> `MEM s (nub (e1.sucs ++ e2.sucs))` by metis_tac[]
       >> fs[nub_append]
       >> `MEM s (nub (FILTER (λx. ¬MEM x e2.sucs) e1.sucs))
           \/ MEM s (nub e2.sucs)` by metis_tac[MEM_APPEND]
       >> metis_tac[]
      )
   >- (fs[concrEdge_component_equality] >> metis_tac[MEMBER_NOT_EMPTY,MEM])
   >- (fs[d_conj_concr_def,FOLDR_LEMM4,concrEdge_component_equality]
         >> `MEM s (nub (e1.pos ++ e2.pos))` by metis_tac[]
         >> fs[nub_append]
         >> `MEM s (nub (FILTER (λx. ¬MEM x e2.pos) e1.pos))
               \/ MEM s (nub e2.pos)` by metis_tac[MEM_APPEND]
         >> metis_tac[]
      )
   >- (fs[concrEdge_component_equality] >> metis_tac[MEMBER_NOT_EMPTY,MEM])
   >- (fs[d_conj_concr_def,FOLDR_LEMM4,concrEdge_component_equality]
         >> `MEM s (nub (e1.neg ++ e2.neg))` by metis_tac[]
         >> fs[nub_append]
         >> `MEM s (nub (FILTER (λx. ¬MEM x e2.neg) e1.neg))
            \/ MEM s (nub e2.neg)` by metis_tac[MEM_APPEND]
         >> metis_tac[]
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
                >> rename [‘n < LENGTH trns_concr_list’,
                           ‘(EL n (MAP SND trns_concr_list), n)’]
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
                      >> rename [‘n < LENGTH trns_concr_list’,
                                 ‘(EL n (MAP SND trns_concr_list), n)’]
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

val trns_is_empty_def = Define`
  trns_is_empty cE = EXISTS (λp. MEM p cE.neg) cE.pos`;

val TRNS_IS_EMPTY_LEMM = store_thm
  ("TRNS_IS_EMPTY_LEMM",
   ``!cE ap. ((set cE.pos ⊆ ap) ∧ (set cE.neg ⊆ ap))
  ==> trns_is_empty cE = (transformLabel ap cE.pos cE.neg = {})``,
   rpt strip_tac >> fs[trns_is_empty_def]
   >> `(EXISTS (λp. MEM p cE.neg) cE.pos) = ~(set cE.neg ∩ set cE.pos = {})`
      by (
       simp[EQ_IMP_THM] >> rpt strip_tac >> fs[EXISTS_MEM]
       >- (`p ∈ set cE.neg ∩ set cE.pos` by simp[IN_INTER]
           >> metis_tac[MEMBER_NOT_EMPTY]
          )
       >- (`?p. p ∈ set cE.neg ∩ set cE.pos` by metis_tac[MEMBER_NOT_EMPTY]
           >> metis_tac[IN_INTER]
          )
   )
   >> metis_tac[TRANSFORMLABEL_EMPTY,INTER_COMM]
  );

val TRANSFORMLABEL_LEMM = store_thm
  ("TRANSFORMLABEL_LEMM",
   ``!ce1 ce2 aP. (((~trns_is_empty ce1 ∧ ~trns_is_empty ce2)
               ∧ ~(MEM_EQUAL ce1.pos ce2.pos ∧ MEM_EQUAL ce1.neg ce2.neg)
               ∧ !x. ((MEM x ce1.pos \/ MEM x ce1.neg \/ MEM x ce2.pos
                    \/ MEM x ce2.neg) ==> MEM x aP))
                    ==> ~(transformLabel (set aP) ce1.pos ce1.neg =
                          transformLabel (set aP) ce2.pos ce2.neg))``,
   rpt gen_tac >> strip_tac
   >> `(set ce1.pos ⊆ set aP) ∧ (set ce2.pos ⊆ set aP)
     ∧ (set ce1.neg ⊆ set aP) ∧ (set ce2.neg ⊆ set aP)` by fs[SUBSET_DEF]
   >> `~(transformLabel (set aP) ce1.pos ce1.neg = {})` by metis_tac[TRNS_IS_EMPTY_LEMM]
   >> `~(transformLabel (set aP) ce2.pos ce2.neg = {})` by metis_tac[TRNS_IS_EMPTY_LEMM]
   >> simp[SET_EQ_SUBSET]
   >> `!l1 l2. ~(set l1 ⊆ set l2) ==> ~MEM_SUBSET l1 l2`
          by fs[MEM_SUBSET_SET_TO_LIST]
   >> fs[MEM_EQUAL_SET]
   >> IMP_RES_TAC TRANSFORMLABEL_SUBSET2
   >> metis_tac[SET_EQ_SUBSET,MEM_SUBSET_SET_TO_LIST]
  );

val tlg_concr_def = Define`
  tlg_concr (t1,acc_t1) (t2,acc_t2) =
    (((MEM_SUBSET t1.pos t2.pos)
  ∧ (MEM_SUBSET t1.neg t2.neg) \/ trns_is_empty t2)
  ∧ (MEM_SUBSET t1.sucs t2.sucs)
  ∧ (MEM_SUBSET acc_t2 acc_t1))`;

val acc_cond_concr_def = Define`
  acc_cond_concr cE f f_trans =
     (~(MEM f cE.sucs)
   \/ (if trns_is_empty cE
       then (EXISTS (λcE1.
                     MEM_SUBSET cE1.sucs cE.sucs
                     ∧ ~(MEM f cE1.sucs)) f_trans)
       else (EXISTS (λcE1.
                         MEM_SUBSET cE1.pos cE.pos
                         ∧ MEM_SUBSET cE1.neg cE.neg
                         ∧ MEM_SUBSET cE1.sucs cE.sucs
                         ∧ ~(MEM f cE1.sucs)) f_trans)))`;

val concr_extrTrans_def = Define`
  concr_extrTrans g_AA aa_id =
    case lookup aa_id g_AA.followers of
      | NONE => NONE
      | SOME aa_edges =>
        let aa_edges_with_frmls =
            CAT_OPTIONS
                (MAP
                 (λ(eL,id).
                   case lookup id g_AA.nodeInfo of
                     | NONE => NONE
                     | SOME n => SOME (eL,n.frml))
                 aa_edges
                )
        in let aa_edges_grpd =
               GROUP_BY
                   (λ(eL1,f1) (eL2,f2). eL1.edge_grp = eL2.edge_grp)
                   aa_edges_with_frmls
        in let concr_edges:(α concrEdge) list =
               CAT_OPTIONS
                (MAP
                 (λgrp. case grp of
                          | [] => NONE
                          | ((eL,f)::xs) =>
                            SOME
                             (concrEdge eL.pos_lab eL.neg_lab (nub (f::MAP SND xs)))
                 ) aa_edges_grpd)
        in do node <- lookup aa_id g_AA.nodeInfo ;
              true_edges <-
                SOME (MAP
                       (λeL. (concrEdge eL.pos_lab eL.neg_lab []))
                       node.true_labels) ;
              SOME (concr_edges ++ true_edges)
                   od`;

val CONCR_EXTRTRANS_NODES = store_thm
  ("CONCR_EXTRTRANS_NODES",
   ``!g_AA x l.
       (concr_extrTrans g_AA x = SOME l)
       ==> (!ce q. MEM ce l ∧ MEM q ce.sucs
              ==> (MEM q (graphStates g_AA)
                  ∧ ALL_DISTINCT ce.sucs))``,
   rpt strip_tac >> fs[concr_extrTrans_def]
   >> Cases_on `lookup x g_AA.followers` >> fs[]
   >> rw[] >> fs[MEM_APPEND,CAT_OPTIONS_MEM,MEM_MAP]
   >- (Cases_on `grp` >> fs[] >> Cases_on `h` >> fs[]
       >> fs[concrEdge_component_equality]
       >> qabbrev_tac `L =
              CAT_OPTIONS
                  (MAP
                       (λ(eL,id).
                         case lookup id g_AA.nodeInfo of
                             NONE => NONE
                           | SOME n => SOME (eL,n.frml)) x')`
       >> `MEM q (MAP SND (FLAT (GROUP_BY
                            (λ(eL1,f1) (eL2,f2). eL1.edge_grp = eL2.edge_grp)
                            L)))` by (
            simp[MEM_MAP,MEM_FLAT]
            >> `q = r \/ MEM q (MAP SND t)` by metis_tac[MEM,nub_set]
            >- (qexists_tac `(q',r)` >> fs[]
                >> qexists_tac `(q',r)::t` >> fs[]
               )
            >- (fs[MEM_MAP] >> qexists_tac `y` >> fs[]
                >> qexists_tac `(q',r)::t` >> fs[]
               )
        )
       >> `MEM q (MAP SND L)` by metis_tac[GROUP_BY_FLAT]
       >> qunabbrev_tac `L` >> fs[MEM_MAP,CAT_OPTIONS_MEM]
       >> rename[`MEM y2 trns`, `SOME y1 = _ y2`]
       >> Cases_on `y2` >> fs[] >> rename[`MEM (eL,id) trns`]
       >> Cases_on `lookup id g_AA.nodeInfo` >> fs[]
       >> rename[`lookup id g_AA.nodeInfo = SOME node`]
       >> simp[graphStates_def,MEM_MAP] >> qexists_tac `(id,node)`
       >> fs[] >> metis_tac[MEM_toAList]
      )
   >- (fs[concrEdge_component_equality] >> metis_tac[MEM])
   >- (Cases_on `grp` >> fs[] >> Cases_on `h` >> fs[]
       >> fs[all_distinct_nub]
      )
  );

val CONCR_EXTRTRANS_LEMM = store_thm
  ("CONCR_EXTRTRANS_LEMM",
   ``!g_AA id aP.
    wfg g_AA ∧ flws_sorted g_AA ∧ unique_node_formula g_AA
    ==> case lookup id g_AA.followers of
      | NONE => T
      | SOME aa_edges =>
    ?n cT. (concr_extrTrans g_AA id = SOME cT)
       ∧ (lookup id g_AA.nodeInfo = SOME n)
       ∧ (set (MAP (concr2AbstractEdge aP) cT) =
              concrTrans g_AA aP n.frml)``,
   rpt strip_tac >> fs[] >> Cases_on `lookup id g_AA.followers` >> fs[]
   >> `?n.lookup id g_AA.nodeInfo = SOME n` by (
       fs[wfg_def] >> metis_tac[domain_lookup]
   )
   >> qexists_tac `n` >> fs[]
   >> `?cT. concr_extrTrans g_AA id = SOME cT` by (
       simp[concr_extrTrans_def]
   )
   >> qexists_tac `cT` >> fs[] >> simp[SET_EQ_SUBSET,SUBSET_DEF]
   >> qabbrev_tac `E =
       (λ((eL1:α edgeLabelAA),(f1:α ltl_frml))
         ((eL2:α edgeLabelAA),(f2:α ltl_frml)).
         eL1.edge_grp = eL2.edge_grp)`
   >> qabbrev_tac `P =
       (λ(f1:α edgeLabelAA # num)
         (f2:α edgeLabelAA # num).
         (FST f2).edge_grp ≤ (FST f1).edge_grp)`
   >> qabbrev_tac `P_c =
       (λ(f1:α edgeLabelAA # α ltl_frml)
         (f2:α edgeLabelAA # α ltl_frml).
         (FST f2).edge_grp ≤ (FST f1).edge_grp)`
   >> `rel_corr E P_c` by (
       simp[rel_corr_def] >> qunabbrev_tac `E`
       >> qunabbrev_tac `P_c`
       >> simp[EQ_IMP_THM] >> rpt strip_tac
       >> Cases_on `x'` >> Cases_on `y` >> fs[]
   )
   >> `!l1 l2. (MAP FST l1 = MAP FST l2)
            ==> (SORTED P l1 ==> SORTED P_c l2)` by (
       Induct_on `l2`  >> fs[] >> rpt strip_tac
       >> `transitive P_c`
           by (qunabbrev_tac `P_c` >> simp[transitive_def])
       >> simp[SORTED_EQ] >> Cases_on `l1` >> fs[]
       >> rename[`SORTED P (h1::t1)`]
       >> `SORTED P t1` by metis_tac[SORTED_TL]
       >> `SORTED P_c l2` by metis_tac[] >> fs[]
       >> rpt strip_tac >> Cases_on `y`
       >> `MEM q (MAP FST t1)` by (
           `MEM q (MAP FST l2)` suffices_by metis_tac[]
           >> simp[MEM_MAP] >> qexists_tac `(q,r)` >> fs[]
       )
       >> fs[MEM_MAP]
       >> `transitive P` by (qunabbrev_tac `P` >> simp[transitive_def])
       >> `P h1 y` by metis_tac[SORTED_EQ]
       >> qunabbrev_tac `P_c` >> Cases_on `y` >> fs[]
       >> Cases_on `h1` >> Cases_on `h` >> fs[] >> rw[]
       >> qunabbrev_tac `P` >> fs[]
   )
   >> qabbrev_tac `J =
       λ(l:((α edgeLabelAA # num) list)). CAT_OPTIONS
        (MAP
           (λ(eL,id).
             case lookup id g_AA.nodeInfo of
                 NONE => NONE
               | SOME n => SOME (eL,n.frml)) l)`
   >> `!k. EVERY
            (λx. IS_SOME (lookup (SND x) g_AA.nodeInfo)) k
            ==> (MAP FST k = MAP FST (J k))` by (
       Induct_on `k`
       >- (qunabbrev_tac `J` >> fs[CAT_OPTIONS_def])
       >- (rpt strip_tac
           >> `MAP FST k = MAP FST (J k)`
                by metis_tac[EVERY_DEF]
           >> `(FST h)::(MAP FST (J k)) = MAP FST (J (h::k))`
                suffices_by metis_tac[MAP]
           >> Cases_on `J (h::k)` >> fs[]
           >- (`?n. lookup (SND h) g_AA.nodeInfo = SOME n`
                  by metis_tac[IS_SOME_EXISTS]
               >> `MEM (FST h, n'.frml) (J (h::k))` by (
                  qunabbrev_tac `J` >> simp[CAT_OPTIONS_MEM]
                  >> fs[CAT_OPTIONS_MAP_LEMM]
                  >> Cases_on `h` >> fs[CAT_OPTIONS_def]
               )
               >> fs[] >> rw[] >> metis_tac[MEM]
              )
           >- (qunabbrev_tac `J` >> fs[]
               >> Cases_on `h` >> fs[CAT_OPTIONS_def]
               >> fs[IS_SOME_EXISTS]
               >> Cases_on `lookup r g_AA.nodeInfo` >> fs[]
               >> fs[CAT_OPTIONS_def] >> rw[]
              )
          )
   )
   >> `EVERY (λx. IS_SOME (lookup (SND x) g_AA.nodeInfo)) x` by (
       simp[EVERY_MEM] >> rpt strip_tac
       >> rename[`MEM fl fls`] >> Cases_on `fl`
       >> rename[`MEM (eL_f,fl_id) fls`] >> fs[wfg_def]
       >> fs[wfAdjacency_def]
       >> `fl_id ∈ domain g_AA.followers` by metis_tac[]
       >> metis_tac[IS_SOME_DEF,domain_lookup]
   )
   >> `MAP FST x = MAP FST (J x)` by metis_tac[]
   >> `transitive P_c` by (
       qunabbrev_tac `P_c` >> simp[transitive_def]
   )
   >> `equivalence E` by (
       qunabbrev_tac `E` >> simp[equivalence_def]
       >> simp[reflexive_def,symmetric_def,transitive_def]
       >> rpt strip_tac
       >- (Cases_on `x'` >> fs[])
       >- (Cases_on `x'` >> Cases_on `y` >> fs[])
       >- (Cases_on `x'` >> Cases_on `y` >> Cases_on `z` >> fs[])
   )
   >> rpt strip_tac >> fs[concrTrans_def,extractTrans_def,concr_extrTrans_def]
   >> rw[]
   >- (Cases_on `lookup id g_AA.followers` >> fs[]
       >> fs[MEM_MAP,CAT_OPTIONS_MAP_LEMM] >> rw[]
       >> fs[CAT_OPTIONS_MEM,MEM_MAP]
       >- (Cases_on `grp` >> fs[] >> disj1_tac
           >> `?eL frml. h = (eL,frml)` by (Cases_on `h` >> fs[])
           >> qexists_tac `(eL.edge_grp,
                            eL.pos_lab,
                            eL.neg_lab,
                            set (frml::(MAP SND t)))`
           >> fs[flws_sorted_def] >> first_x_assum (qspec_then `id` mp_tac)
           >> `id ∈ domain g_AA.nodeInfo`
               by (fs[wfg_def] >> metis_tac[domain_lookup])
           >> simp[] >> rpt strip_tac
           >- simp[concr2AbstractEdge_def]
           >- (qexists_tac `eL` >> simp[]
               >> Q.HO_MATCH_ABBREV_TAC `
                   (0 < eL.edge_grp)
                   ∧ ~(A = {})
                   ∧ (frml INSERT set (MAP SND t)
                      = A)`
               >> `0 < eL.edge_grp ∧ (frml INSERT set (MAP SND t) = A)`
                   suffices_by (
                    simp[] >> rpt strip_tac >> `frml ∈ A` by fs[]
                    >> metis_tac[MEMBER_NOT_EMPTY]
                ) >> rpt strip_tac
            >- (`MEM (eL,frml) (FLAT (GROUP_BY E (J x)))` by (
                 simp[MEM_FLAT] >> qexists_tac `(eL,frml)::t` >> fs[]
                )
                >> `MEM (eL,frml) (J x)` by metis_tac[GROUP_BY_FLAT]
                >> qunabbrev_tac `J` >> fs[CAT_OPTIONS_MEM,MEM_MAP]
                >> rename[`MEM edge x`] >> Cases_on `edge`
                >> fs[] >> Cases_on `lookup r g_AA.nodeInfo` >> fs[]
                >> rw[] >> `0 < (FST (eL,r)).edge_grp` by metis_tac[]
                >> fs[]
               )
            >- (qabbrev_tac `c_edge_list = (eL,frml)::t`
                >> `set (MAP SND c_edge_list) = A` suffices_by (
                     qunabbrev_tac `c_edge_list` >> fs[]
                 )
                >> qunabbrev_tac `A` >> simp[SET_EQ_SUBSET,SUBSET_DEF]
                >> qabbrev_tac `L =
                         CAT_OPTIONS
                          (MAP
                           (λ(eL,id).
                             case lookup id g_AA.nodeInfo of
                                NONE => NONE
                              | SOME n => SOME (eL,n.frml)) x)`
                >> `L = J x` by (qunabbrev_tac `J` >> qunabbrev_tac `L` >> fs[])
                >> `!e f. MEM (e,f) c_edge_list ==>
                          (MEM (e,f) L
                          ∧ ?id node. MEM (e,id) x
                                  ∧ (lookup id g_AA.nodeInfo = SOME node)
                                  ∧ (node.frml = f))` by (
                        rpt gen_tac >> strip_tac
                        >> `MEM (e,f)
                             (FLAT (GROUP_BY
                               (λ(eL1,f1) (eL2,f2).
                                 eL1.edge_grp = eL2.edge_grp) L))` by (
                             simp[MEM_FLAT] >> qexists_tac `c_edge_list` >> fs[]
                         )
                        >> `!R. FLAT (GROUP_BY R L) = L`
                              by metis_tac[GROUP_BY_FLAT]
                        >> `MEM (e,f) L` by metis_tac[]
                        >> qunabbrev_tac `L` >> fs[CAT_OPTIONS_MEM,MEM_MAP]
                        >> rename[`MEM y2 x`]
                        >> `?y_id. y2 = (e,y_id)` by (
                             Cases_on `y2` >> Cases_on `lookup r g_AA.nodeInfo`
                             >> fs[]
                        ) >> fs[] >> strip_tac
                        >- (qexists_tac `(e,y_id)` >> simp[])
                        >- (qexists_tac `y_id` >> rw[] >> fs[]
                            >> `?node. lookup y_id g_AA.nodeInfo = SOME node`
                               by (Cases_on `lookup y_id g_AA.nodeInfo` >> fs[])
                            >> qexists_tac `node` >> fs[]
                           )
                     )
                >> `∀l_sub.
                         MEM l_sub (GROUP_BY E L) ⇒
                         (∀x y. MEM x l_sub ∧ MEM y l_sub ⇒ E x y) ∧
                         ∀x y. MEM x l_sub ∧ MEM y L ∧ E x y ⇒ MEM y l_sub` by (
                         HO_MATCH_MP_TAC SORTED_GROUP_BY
                         >> qexists_tac `P_c` >> fs[] >> metis_tac[]
                     )
                >> rpt strip_tac
                >- (rename[`MEM frml1 (MAP SND c_edge_list)`]
                    >> `?eL1. MEM (eL1,frml1) c_edge_list` by (
                           fs[MEM_MAP] >> rename[`MEM y1 c_edge_list`]
                            >> qexists_tac `FST y1` >> fs[]
                     )
                    >> `MEM (eL,frml) L ∧
                         ∃id node.
                          MEM (eL,id) x ∧ lookup id g_AA.nodeInfo = SOME node
                          ∧ node.frml = frml` by (
                            `MEM (eL,frml) c_edge_list` suffices_by metis_tac[]
                            >> qunabbrev_tac `c_edge_list` >> fs[]
                     )
                    >> `MEM (eL1,frml1) L ∧
                         ∃id1 node1.
                          MEM (eL1,id1) x ∧ lookup id1 g_AA.nodeInfo = SOME node1
                          ∧ node1.frml = frml1` by metis_tac[]
                    >> fs[] >> rw[]
                    >> first_x_assum (qspec_then `c_edge_list` mp_tac) >> simp[]
                    >> rpt strip_tac >> rw[]
                    >> `eL1 = eL` by (
                         `eL1.edge_grp = eL.edge_grp` by (
                          `MEM (eL,node.frml) c_edge_list` by (
                            qunabbrev_tac `c_edge_list` >> fs[]
                          )
                          >> `E (eL,node.frml) (eL1,node1.frml)` by metis_tac[]
                          >> qunabbrev_tac `E` >> fs[]
                         )
                         >> `(FST (eL,id')).edge_grp =
                               (FST (eL1,id1)).edge_grp` by fs[]
                         >> `FST (eL,id') = FST (eL1,id1)` by metis_tac[]
                         >> fs[]
                     )
                    >> rw[]
                    >> qexists_tac `node1` >> fs[] >> qexists_tac `id1`
                    >> simp[OPTION_TO_LIST_MEM] >> qexists_tac `x` >> fs[]
                    >> qexists_tac `(id,n)` >> fs[]
                    >> metis_tac[UNIQUE_NODE_FIND_LEMM]
                   )
                >- (simp[MEM_MAP] >> fs[OPTION_TO_LIST_MEM]
                    >> rename[`findNode _ g_AA = SOME x2`]
                    >> `x2 = (id,n)` by metis_tac[UNIQUE_NODE_FIND_LEMM,SOME_11]
                    >> rw[] >> fs[] >> rw[] >> qexists_tac `(eL,suc.frml)`
                    >> fs[]
                    >> `MEM (eL,suc.frml) (J l)` by (
                         qunabbrev_tac `J` >> simp[CAT_OPTIONS_MEM,MEM_MAP]
                         >> qexists_tac `(eL,sucId)` >> fs[]
                         >> Cases_on `lookup sucId g_AA.nodeInfo` >> fs[]
                     )
                   >> `MEM c_edge_list (GROUP_BY E (J l))` by fs[]
                   >> `MEM (eL,suc.frml) (FLAT (GROUP_BY E (J l)))` by (
                         metis_tac[GROUP_BY_FLAT]
                     )
                   >> fs[MEM_FLAT] >> rename[`MEM c_e_list2 (GROUP_BY E (J l))`]
                   >> first_x_assum (qspec_then `c_edge_list` mp_tac) >> simp[]
                   >> rpt strip_tac
                   >> first_x_assum (qspec_then `(eL,frml)` mp_tac)
                   >> `MEM (eL,frml) c_edge_list` by
                        (qunabbrev_tac `c_edge_list` >> fs[])
                   >> simp[] >> rpt strip_tac
                   >> `E (eL,frml) (eL,suc.frml)` suffices_by metis_tac[]
                   >> qunabbrev_tac `E` >> simp[]
                   )
               )
              )
          )
       >- (disj2_tac >> qexists_tac `(0,eL.pos_lab,eL.neg_lab,{})`
           >> simp[concr2AbstractEdge_def] >> qexists_tac `eL`
           >> simp[OPTION_TO_LIST_MEM] >> qexists_tac `n.true_labels`
           >> simp[] >> qexists_tac `(id,n)` >> fs[]
           >> metis_tac[UNIQUE_NODE_FIND_LEMM]
          )
      )
   >- (Cases_on `lookup id g_AA.followers` >> fs[]
       >> fs[MEM_MAP,CAT_OPTIONS_MAP_LEMM] >> rw[]
       >> fs[CAT_OPTIONS_MEM,MEM_MAP]
       >> Q.HO_MATCH_ABBREV_TAC `
           ?y. (transformLabel aP label.pos_lab label.neg_lab,
                SUCS) = concr2AbstractEdge aP y
             ∧ ((?grp.
                 SOME y = CE grp
               ∧ MEM grp CONCR_TRNS) \/ A y)`
       >> `?grp cE. (SOME cE = CE grp) ∧ (MEM grp CONCR_TRNS)
                  ∧ (set cE.sucs = SUCS)
                  ∧ ((cE.pos = label.pos_lab) ∧ (cE.neg = label.neg_lab))` by (
         `?f. f ∈ SUCS` by metis_tac[MEMBER_NOT_EMPTY]
         >> qunabbrev_tac `SUCS` >> fs[OPTION_TO_LIST_MEM]
         >> rename[`findNode _ g_AA = SOME node`]
         >> `node = (id,n)` by metis_tac[SOME_11,UNIQUE_NODE_FIND_LEMM]
         >> rw[] >> fs[] >> rw[]
         >> rename[`lookup id g_AA.followers = SOME fls`]
         >> `FLAT CONCR_TRNS = J fls` by (
            qunabbrev_tac `CONCR_TRNS` >> fs[] >> metis_tac[GROUP_BY_FLAT]
         )
         >> `MEM (label,suc.frml) (J fls)` by (
            qunabbrev_tac `J` >> simp[CAT_OPTIONS_MEM,MEM_MAP]
            >> qexists_tac `(label,sucId)` >> simp[]
            >> Cases_on `lookup sucId g_AA.nodeInfo` >> fs[]
         )
         >> `?grp. MEM grp CONCR_TRNS ∧ MEM (label,suc.frml) grp`
             by metis_tac[MEM_FLAT]
         >> qexists_tac `grp`
         >> `?cE. CE grp = SOME cE` by (
             qunabbrev_tac `CE` >> simp[] >> Cases_on `grp` >> fs[]
             >> Cases_on `h` >> fs[]
         )
         >> qexists_tac `cE` >> simp[SET_EQ_SUBSET,SUBSET_DEF]
         >> strip_tac
         >- (rpt strip_tac
          >- (`!lab f. MEM (lab,f) grp ==> (lab = label)` by (
              rpt strip_tac
               >> `SORTED P fls
                  ∧ ∀x y.
                  (MEM x fls ∧ MEM y fls ∧ (FST x).edge_grp = (FST y).edge_grp)
                  ⇒ (FST x = FST y)` by (
                  fs[flws_sorted_def] >> metis_tac[domain_lookup]
              )
               >> `∀l_sub.
                  MEM l_sub (GROUP_BY E (J fls)) ⇒
                  (∀x y. MEM x l_sub ∧ MEM y l_sub ⇒ E x y) ∧
                  ∀x y. MEM x l_sub ∧ MEM y (J fls) ∧ E x y
                  ⇒ MEM y l_sub` by (
                  HO_MATCH_MP_TAC SORTED_GROUP_BY
                  >> qexists_tac `P_c` >> fs[] >> metis_tac[]
              )
               >> first_x_assum (qspec_then `grp` mp_tac) >> simp[]
               >> rpt strip_tac
               >> `MEM (lab,f) (J fls)` by (
                   `MEM (lab,f) (FLAT CONCR_TRNS)` by (
                       fs[MEM_FLAT] >> qexists_tac `grp` >> simp[]
                   )
                   >> metis_tac[]
              )
               >> `E (label,suc.frml) (lab,f)` by metis_tac[]
               >> first_x_assum (qspec_then `(label,sucId)` mp_tac)
               >> simp[] >> rpt strip_tac
               >> qunabbrev_tac `J` >> fs[CAT_OPTIONS_MEM,MEM_MAP]
               >> rename[`MEM y2 fls`,`SOME (lab,x) = _ y2`]
               >> Cases_on `y2` >> fs[]
               >> first_x_assum (qspec_then `(lab,r)` mp_tac)
               >> Cases_on `lookup r g_AA.nodeInfo` >> fs[]
               >> rw[] >> qunabbrev_tac `E` >> fs[]
             )
             >> qunabbrev_tac `CE` >> Cases_on `grp` >> fs[] >> Cases_on `h`
             >> fs[concrEdge_component_equality] >> rw[]
             >- (Cases_on `x = suc.frml`
                 >- (qexists_tac `suc` >> simp[] >> qexists_tac `sucId`
                     >> simp[]
                    )
                 >- (`MEM x (MAP SND t)` by metis_tac[MEM,nub_set]
                     >> fs[MEM_MAP] >> rename[`MEM edge t`]
                     >> `edge = (label,x)`
                          by (Cases_on `edge` >> fs[] >> metis_tac[])
                     >> rw[]
                     >> `MEM (label,x) (J fls)` by (
                          `MEM (label,x) (FLAT CONCR_TRNS)` by (
                            simp[MEM_FLAT]
                            >> qexists_tac `(label,suc.frml)::t` >> simp[]
                          )
                          >> metis_tac[]
                     )
                     >> qunabbrev_tac `J` >> fs[CAT_OPTIONS_MEM,MEM_MAP]
                     >> rename[`MEM edge fls`] >> Cases_on `edge`
                     >> rename[`MEM (e_f,e_id) fls`]
                     >> Cases_on `lookup e_id g_AA.nodeInfo` >> fs[]
                     >> rename[`lookup _ _ = SOME node`]
                     >> qexists_tac `node` >> fs[] >> qexists_tac `e_id`
                     >> fs[]
                    )
                )
             >- (Cases_on `x = suc.frml`
                 >- (qexists_tac `suc` >> simp[] >> qexists_tac `sucId`
                     >> simp[]
                    )
                 >- (`MEM x (r::MAP SND t)` by metis_tac[nub_set]
                     >> `MEM x (MAP SND ((label,r)::t))` by fs[MEM]
                     >- (`MEM (label,x) (J fls)` by (
                          `MEM (label,x) (FLAT CONCR_TRNS)` by (
                              simp[MEM_FLAT]
                              >> qexists_tac `(label,r)::t` >> simp[]
                              >> fs[MEM_MAP] >> Cases_on `y` >> fs[]
                              >> rw[] >> metis_tac[]
                          )
                          >> metis_tac[]
                         )
                         >> qunabbrev_tac `J` >> fs[CAT_OPTIONS_MEM,MEM_MAP]
                         >> rename[`MEM edge fls`] >> Cases_on `edge`
                         >> rename[`MEM (e_f,e_id) fls`]
                         >> Cases_on `lookup e_id g_AA.nodeInfo` >> fs[]
                         >> rename[`lookup _ _ = SOME node`]
                         >> qexists_tac `node` >> fs[] >> qexists_tac `e_id`
                         >> fs[])
                    (*  >- ( *)
                    (*    rename[`MEM edge t`] *)
                    (*    >> `edge = (label,x)` *)
                    (*       by (Cases_on `edge` >> fs[] >> metis_tac[]) *)
                    (*    >> rw[] *)
                    (*    >> `MEM (label,x) (J fls)` by ( *)
                    (*        `MEM (label,x) (FLAT CONCR_TRNS)` by ( *)
                    (*          simp[MEM_FLAT] *)
                    (*          >> qexists_tac `(label,r)::t` >> simp[] *)
                    (*          >> rw[] >> fs[] >> metis_tac[] *)
                    (*        ) *)
                    (*        >> metis_tac[] *)
                    (*    ) *)
                    (*    >> qunabbrev_tac `J` >> fs[CAT_OPTIONS_MEM,MEM_MAP] *)
                    (*    >> rename[`MEM edge fls`] >> Cases_on `edge` *)
                    (*    >> rename[`MEM (e_f,e_id) fls`] *)
                    (*    >> Cases_on `lookup e_id g_AA.nodeInfo` >> fs[] *)
                    (*    >> rename[`lookup _ _ = SOME node`] *)
                    (*    >> qexists_tac `node` >> fs[] >> qexists_tac `e_id` *)
                    (*    >> fs[] *)
                    (* ) *)
                    )
                )
            )
         >- (rename[`MEM (label,sucId1) fls`,
                    `SOME suc1 = lookup sucId1 g_AA.nodeInfo`]
             >> `MEM (label,suc1.frml) grp` by (
               `SORTED P fls
                  ∧ ∀x y.
                    (MEM x fls ∧ MEM y fls ∧ (FST x).edge_grp = (FST y).edge_grp)
                    ⇒ (FST x = FST y)` by (
                 fs[flws_sorted_def] >> metis_tac[domain_lookup]
               )
               >> `∀l_sub.
                   MEM l_sub (GROUP_BY E (J fls)) ⇒
                   (∀x y. MEM x l_sub ∧ MEM y l_sub ⇒ E x y) ∧
                   ∀x y. MEM x l_sub ∧ MEM y (J fls) ∧ E x y
                   ⇒ MEM y l_sub` by (
                 HO_MATCH_MP_TAC SORTED_GROUP_BY
                 >> qexists_tac `P_c` >> fs[] >> metis_tac[]
               )
               >> first_x_assum (qspec_then `grp` mp_tac) >> simp[]
               >> rpt strip_tac
               >> `MEM (label,suc1.frml) (J fls)` by (
                   qunabbrev_tac `J` >> fs[CAT_OPTIONS_MEM,MEM_MAP]
                   >> qexists_tac `(label,sucId1)` >> simp[]
                   >> Cases_on `lookup sucId1 g_AA.nodeInfo` >> fs[]
               )
               >> `E (label,suc.frml) (label,suc1.frml)` by (
                   qunabbrev_tac `E` >> fs[]
               )
               >> metis_tac[]
              )
             >> qunabbrev_tac `CE` >> fs[] >> Cases_on `grp` >> fs[]
             >> Cases_on `h` >> fs[concrEdge_component_equality]
             >- (rw[] >> fs[MEM] >> metis_tac[MEM,nub_set])
             >- (rw[] >> fs[MEM]
                 >> `MEM suc1.frml (MAP SND t)` by (
                      fs[MEM_MAP] >> qexists_tac `(label,suc1.frml)` >> simp[]
                  )
                 >> metis_tac[MEM,nub_set]
                )
             >- (rw[] >> fs[MEM] >> metis_tac[MEM,nub_set])
             >- (rw[] >> fs[MEM]
                   >> `MEM suc1.frml (MAP SND t)` by (
                      fs[MEM_MAP] >> qexists_tac `(label,suc1.frml)` >> simp[]
                  )
                   >> metis_tac[MEM,nub_set]
                )
            )
            )
         >- (qunabbrev_tac `CE` >> Cases_on `grp` >> fs[] >> Cases_on `h`
             >> fs[concrEdge_component_equality]
             >> `q = label` by (
                `SORTED P fls
                ∧ ∀x y.
                 (MEM x fls ∧ MEM y fls ∧ (FST x).edge_grp = (FST y).edge_grp)
                 ⇒ (FST x = FST y)` by (
                    fs[flws_sorted_def] >> metis_tac[domain_lookup]
                )
                >> `∀l_sub.
                    MEM l_sub (GROUP_BY E (J fls)) ⇒
                    (∀x y. MEM x l_sub ∧ MEM y l_sub ⇒ E x y) ∧
                    ∀x y. MEM x l_sub ∧ MEM y (J fls) ∧ E x y
                    ⇒ MEM y l_sub` by (
                    HO_MATCH_MP_TAC SORTED_GROUP_BY
                    >> qexists_tac `P_c` >> fs[] >> metis_tac[]
                )
                >> first_x_assum (qspec_then `(q,r)::t` mp_tac) >> simp[]
                >> rpt strip_tac
                >> `MEM (q,r) (J fls)` by (
                  `MEM (q,r) (FLAT CONCR_TRNS)` suffices_by metis_tac[]
                  >> simp[MEM_FLAT] >> qexists_tac `((q,r)::t)` >> simp[]
                )
                >> `E (q,r) (label,suc.frml)` by metis_tac[]
                >> qunabbrev_tac `J` >> fs[CAT_OPTIONS_MEM,MEM_MAP]
                >> rename[`MEM edge fls`] >> Cases_on `edge` >> fs[]
                >> rename[`MEM (e_lab,e_id) fls`]
                >> Cases_on `lookup e_id g_AA.nodeInfo` >> fs[]
                >> first_x_assum (qspec_then `(e_lab,e_id)` mp_tac) >> simp[]
                >> rpt strip_tac
                >> first_x_assum (qspec_then `(label,sucId)` mp_tac)
                >> qunabbrev_tac `E` >> fs[] >> rw[]
              )
             >> rw[]
            )
        )
       >> qexists_tac `cE` >> Cases_on `cE` >> simp[concr2AbstractEdge_def]
       >> rw[]
       >- fs[concrEdge_component_equality]
       >- (disj1_tac >> metis_tac[])
      )
   >- (Cases_on `lookup id g_AA.followers` >> fs[] >> simp[MEM_MAP]
       >> fs[OPTION_TO_LIST_MEM]
       >> rename[`findNode _ g_AA = SOME x2`,`_ x2 = SOME el_list`]
       >> `x2 = (id,node)` by metis_tac[UNIQUE_NODE_FIND_LEMM,SOME_11]
       >> rw[] >> fs[] >> rename[`lookup id g_AA.followers = SOME fls`]
       >> qexists_tac `concrEdge l.pos_lab l.neg_lab []`
       >> simp[concr2AbstractEdge_def,CAT_OPTIONS_MEM,MEM_MAP] >> disj2_tac
       >> metis_tac[]
      )
  );

val suff_wfg_def = Define
`suff_wfg g = !n. (g.next <= n) ==> ~(n ∈ domain g.nodeInfo)`;

val WF_IMP_SUFFWFG = store_thm
  ("WF_IMP_SUFFWFG",
   ``!g. wfg g ==> suff_wfg g``,
       rpt strip_tac >> fs[suff_wfg_def,wfg_def]
  )

val inGBA_def = Define`
  inGBA g qs =
    let gbaNodes = MAP SND (toAList g.nodeInfo)
    in EXISTS (λn. MEM_EQUAL n.frmls qs) gbaNodes`;

val IN_GBA_MEM_EQUAL = store_thm
  ("IN_GBA_MEM_EQUAL",
  ``!G x y. MEM_EQUAL x y ==> (inGBA G x = inGBA G y)``,
  gen_tac
  >> `!x y. MEM_EQUAL x y ==> (inGBA G x ==> inGBA G y)`
          suffices_by metis_tac[MEM_EQUAL_SET]
  >> simp[EQ_IMP_THM] >> rpt strip_tac
  >> fs[inGBA_def]
  >> `(λn. MEM_EQUAL n.frmls x) = (λn. MEM_EQUAL n.frmls y)` by (
      Q.HO_MATCH_ABBREV_TAC `A = B`
      >> `!x. A x = B x` suffices_by metis_tac[]
      >> rpt strip_tac >> qunabbrev_tac `A`
      >> qunabbrev_tac `B` >> fs[]
      >> fs[MEM_EQUAL_SET]
  )
  >> fs[]
  );

val addNodeToGBA_def = Define`
  addNodeToGBA g qs =
    if inGBA g qs
    then g
    else addNode (nodeLabelGBA qs) g`;


val ADDNODE_GBA_WFG = store_thm
  ("ADDNODE_GBA_WFG",
   ``!g qs. wfg g ==> wfg (addNodeToGBA g qs)``,
   rpt strip_tac >> simp[addNodeToGBA_def] >> Cases_on `inGBA g qs` >> fs[]
  );

val ADDNODE_GBA_WFG_FOLDR = store_thm
  ("ADDNODE_GBA_WFG_FOLDR",
  ``!G l. wfg G ==>
  (let G_WITH_IDS =
       FOLDR
           (λn (ids,g).
               if inGBA g n then (ids,g)
               else (g.next::ids,addNodeToGBA g n)) ([],G) l
   in wfg (SND G_WITH_IDS))``,
   gen_tac >> Induct_on `l` >> rpt strip_tac >> fs[]
   >> Cases_on `FOLDR
                 (λn (ids,g).
                     if inGBA g n then (ids,g)
                     else (g.next::ids,addNodeToGBA g n)) ([],G) l`
   >> fs[] >> Cases_on `inGBA r h` >> fs[ADDNODE_GBA_WFG]
  );

val ADDNODE_GBA_DOM_FOLDR = store_thm
  ("ADDNODE_GBA_DOM_FOLDR",
   ``!G l. wfg G ==>
  (let G_WITH_IDS =
       FOLDR
           (λn (ids,g).
               if inGBA g n then (ids,g)
               else (g.next::ids,addNodeToGBA g n)) ([],G) l
   in ((set (FST (G_WITH_IDS))) ∪ domain G.nodeInfo =
        domain (SND G_WITH_IDS).nodeInfo)
      ∧ (G.next <= (SND G_WITH_IDS).next))``,
   gen_tac >> Induct_on `l` >> rpt strip_tac >> fs[]
   >> Cases_on `FOLDR
  (λn (ids,g).
      if inGBA g n then (ids,g)
      else (g.next::ids,addNodeToGBA g n)) ([],G) l`
   >> fs[] >> Cases_on `inGBA r h` >> fs[]
   >> simp[SUBSET_DEF] >> rpt strip_tac >> fs[]
   >> simp[addNodeToGBA_def,addNode_def]
   >> fs[SUBSET_DEF,INSERT_UNION] >> Cases_on `r.next ∈ domain G.nodeInfo`
   >> fs[wfg_def] >> metis_tac[]
  );

(* val ADDNODE_GBA_DOM_FOLDR2 = store_thm *)
(*   ("ADDNODE_GBA_DOM_FOLDR2", *)

(* ) *)


val ADDNODE_GBA_LEMM = store_thm
  ("ADDNODE_GBA_LEMM",
   ``!g qs. suff_wfg g ==>
          ({ set x | inGBA (addNodeToGBA g qs) x } =
             { set x | inGBA g x } ∪ {set qs})``,
   rpt strip_tac
   >> `{set x | inGBA (addNodeToGBA g qs) x} ⊆ {set x | inGBA g x} ∪ {set qs}
     ∧ {set x | inGBA g x} ∪ {set qs} ⊆ {set x | inGBA (addNodeToGBA g qs) x}`
     suffices_by metis_tac[SET_EQ_SUBSET]
   >> simp[SUBSET_DEF] >> rpt strip_tac
   >> fs[addNodeToGBA_def] >> Cases_on `inGBA g qs`
   >> fs[] >> fs[inGBA_def]
   >- (fs[EXISTS_MEM,MEM_MAP] >> `?i. y = (i,n)` by (Cases_on `y` >> fs[])
       >> Cases_on `set x' = set qs` >> fs[] >> rw[] >> qexists_tac `n.frmls`
       >> fs[MEM_EQUAL_SET] >> qexists_tac `n` >> fs[] >> qexists_tac `(i,n)`
       >> fs[])
   >- (fs[EXISTS_MEM,MEM_MAP] >> `?i. y = (i,n)` by (Cases_on `y` >> fs[])
       >> Cases_on `set x' = set qs` >> fs[]
       >> `SOME n = lookup i (addNode (nodeLabelGBA qs) g).nodeInfo`
          by metis_tac[MEM_toAList]
       >> fs[addNode_def,lookup_insert] >> Cases_on `i = g.next`
       >> fs[MEM_toAList] >> fs[EVERY_MEM] >> rw[] >> fs[MEM_EQUAL_SET]
       >> qexists_tac `n.frmls` >> fs[] >> qexists_tac `n` >> fs[]
       >> qexists_tac `(i,n)` >> fs[MEM_toAList]
      )
   >- metis_tac[]
   >- (fs[EXISTS_MEM] >> qexists_tac `n.frmls` >> fs[MEM_EQUAL_SET]
       >> simp[addNode_def] >> qexists_tac `n` >> fs[]
       >> fs[MEM_MAP] >> qexists_tac `y`
       >> `?i. (i,n) = y` by (Cases_on `y` >> fs[])
       >> `~(i = g.next)` by (
            fs[suff_wfg_def] >> CCONTR_TAC >> `~(i ∈ domain g.nodeInfo)` by fs[]
            >> rw[] >> metis_tac[MEM_toAList,domain_lookup]
        )
       >> rw[] >> metis_tac[lookup_insert,MEM_toAList]
      )
   >- metis_tac[]
   >- (qexists_tac `qs` >> fs[EXISTS_MEM] >> qexists_tac `nodeLabelGBA qs`
       >> fs[MEM_EQUAL_SET,MEM_MAP] >> qexists_tac `(g.next,nodeLabelGBA qs)`
       >> fs[] >> simp[MEM_toAList] >> simp[addNode_def,lookup_insert]
      )
  );

val frml_ad_def = Define`
  frml_ad g =
       !i n. i ∈ (domain g.nodeInfo) ∧ (lookup i g.nodeInfo = SOME n)
          ==> ALL_DISTINCT n.frmls`;

val FRML_AD_NODEINFO = store_thm
  ("FRML_AD_NODEINFO",
   ``!g1 g2. (g1.nodeInfo = g2.nodeInfo) ==> (frml_ad g1 = frml_ad g2)``,
   rpt strip_tac >> simp[frml_ad_def]
  );

val ADDNODE_GBA_FOLDR = store_thm
  ("ADDNODE_GBA_FOLDR",
   ``!G l. suff_wfg G ==>
       (let G_WITH_IDS =
         FOLDR
           (λn (ids,g).
               if inGBA g n then (ids,g)
               else (g.next::ids,addNodeToGBA g n)) ([],G) l
       in
       (suff_wfg (SND G_WITH_IDS)
      ∧ ({ set x | inGBA (SND G_WITH_IDS) x } =
          { set x | inGBA G x } ∪ set (MAP set l))
      ∧ (!i. i ∈ domain G.nodeInfo
             ==> (lookup i G.nodeInfo = lookup i (SND G_WITH_IDS).nodeInfo)
               ∧ (lookup i G.followers = lookup i (SND G_WITH_IDS).followers)
        )
      ∧ (G.next <= (SND G_WITH_IDS).next)
      ∧ (domain G.nodeInfo ⊆ domain (SND G_WITH_IDS).nodeInfo)
      ∧ (!i. MEM i (FST G_WITH_IDS)
             ==> ?n. (lookup i (SND G_WITH_IDS).nodeInfo = SOME n)
                   ∧ (MEM n.frmls l)
                   ∧ lookup i (SND G_WITH_IDS).followers = SOME []
                   ∧ (G.next <= i)
        )
      ∧ (frml_ad G ∧ (!x. MEM x l ==> ALL_DISTINCT x)
                 ==> frml_ad (SND G_WITH_IDS))
       ))``,
   gen_tac >> Induct_on `l` >> rpt strip_tac >> fs[]
   >> Q.HO_MATCH_ABBREV_TAC `suff_wfg G2 ∧ A = B
                          ∧ (!i. i ∈ domain G.nodeInfo
                                 ==> (lookup i G1.nodeInfo
                                      = lookup i G2.nodeInfo)
                                 ∧ (lookup i G1.followers
                                    = lookup i G2.followers)
                            )
                          ∧ (G.next <= G2.next)
                          ∧ (domain G.nodeInfo ⊆ domain G2.nodeInfo)
                          ∧ C`
   >> Cases_on `FOLDR
                    (λn (ids,g).
                        if inGBA g n then (ids,g)
                        else (g.next::ids,addNodeToGBA g n)) ([],G) l`
   >> fs[]
   >> `suff_wfg G2 ∧ (A = B)
       ∧ (∀i.
           (i ∈ domain G.nodeInfo) ⇒
           (lookup i G1.nodeInfo = lookup i G2.nodeInfo)
           ∧ (lookup i G1.followers = lookup i G2.followers)
         )
       ∧ G.next ≤ G2.next
       ∧ domain G.nodeInfo ⊆ domain G2.nodeInfo
       ∧ ((A = B)
        ∧ (∀i.
            (i ∈ domain G.nodeInfo) ⇒
            (lookup i G1.nodeInfo = lookup i G2.nodeInfo)
            ∧ (lookup i G1.followers = lookup i G2.followers)) ==> C)`
       suffices_by fs[]
   >> rw[]
   >- (qunabbrev_tac `G1`
       >> Cases_on `inGBA r h` >> fs[] >> qunabbrev_tac `G2`
       >> fs[addNodeToGBA_def,suff_wfg_def] >> rpt strip_tac
       >> fs[addNode_def]
       >> metis_tac[DECIDE ``SUC r.next <= n ==> r.next <= n``]
      )
   >- (qunabbrev_tac `G1`
       >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> qunabbrev_tac `A`
       >> qunabbrev_tac `B`
       >> fs[] >> rpt strip_tac >> qunabbrev_tac `G2`
    >- (Cases_on `inGBA r h` >> fs[]
     >- (`x ∈ {set x | inGBA r x}` by (fs[] >> metis_tac[])
         >> `x ∈ {set x | inGBA G x} ∪ set (MAP set l)`
            by metis_tac[SET_EQ_SUBSET,SUBSET_DEF]
         >> fs[UNION_DEF] >> metis_tac[]
        )
     >- (`x ∈ {set a | inGBA (addNodeToGBA r h) a}` by (fs[] >> metis_tac[])
         >> `x ∈ {set a | inGBA r a} ∪ {set h}` by metis_tac[ADDNODE_GBA_LEMM]
         >> fs[UNION_DEF]
         >- (`x ∈ {set x | inGBA r x}` by (fs[] >> metis_tac[])
             >> `x ∈ {x'' | (∃x. x'' = set x ∧ inGBA G x)
                                ∨ MEM x'' (MAP set l)}`
                by metis_tac[SET_EQ_SUBSET,SUBSET_DEF]
             >> fs[] >> metis_tac[]
            )
         >- metis_tac[]
        )
       )
    >- (Cases_on `inGBA r h` >> fs[]
     >- (`x ∈ {set x | inGBA G x}` by (fs[] >> metis_tac[])
         >> `x ∈ {set x | inGBA r x}` by metis_tac[IN_UNION]
         >> fs[] >> metis_tac[]
        )
     >- (`x ∈ {set x | inGBA G x}` by (fs[] >> metis_tac[])
         >> `x ∈ {set x | inGBA r x}` by metis_tac[IN_UNION]
         >> `x ∈ {set x | inGBA (addNodeToGBA r h) x}`
            by metis_tac[IN_UNION,ADDNODE_GBA_LEMM]
         >> fs[] >> metis_tac[]
        )
       )
    >- (qexists_tac `h` >> Cases_on `inGBA r h` >> fs[]
        >> `x ∈ {set h}` by fs[]
        >> `x ∈ {set x | inGBA (addNodeToGBA r h) x}`
           by metis_tac[IN_UNION,ADDNODE_GBA_LEMM]
        >> fs[inGBA_def,EXISTS_MEM] >> metis_tac[MEM_EQUAL_SET]
       )
    >- (`x ∈ {set x | inGBA r x}` by metis_tac[IN_UNION]
        >> Cases_on `inGBA r h` >> fs[]
        >- metis_tac[]
        >- (`x ∈ {set x | inGBA r x}` by metis_tac[IN_UNION]
            >> `x ∈ {set x | inGBA (addNodeToGBA r h) x}`
                by metis_tac[IN_UNION,ADDNODE_GBA_LEMM]
            >> fs[] >> metis_tac[]
           )
       )
      )
   >- (fs[] >> rw[] >> Cases_on `inGBA G1 h` >> qunabbrev_tac `G2` >> fs[]
       >> simp[addNodeToGBA_def,addNode_def]
       >> `~(i = G1.next)` by (
            fs[suff_wfg_def] >> `~(G1.next <= i)` by metis_tac[SUBSET_DEF]
            >> fs[]
        )
       >> metis_tac[lookup_insert]
      )
   >- (fs[] >> rw[] >> Cases_on `inGBA G1 h` >> qunabbrev_tac `G2` >> fs[]
         >> simp[addNodeToGBA_def,addNode_def]
         >> `~(i = G1.next)` by (
            fs[suff_wfg_def] >> `~(G1.next <= i)` by metis_tac[SUBSET_DEF]
              >> fs[]
        )
         >> metis_tac[lookup_insert]
      )
   >- (fs[] >> rw[] >> Cases_on `inGBA G1 h` >> qunabbrev_tac `G2` >> fs[]
         >> simp[addNodeToGBA_def,addNode_def])
   >- (fs[] >> rw[] >> Cases_on `inGBA G1 h` >> qunabbrev_tac `G2` >> fs[]
       >> simp[addNodeToGBA_def,addNode_def,SUBSET_DEF] >> rpt strip_tac
       >> metis_tac[SUBSET_DEF]
      )
   >- (qunabbrev_tac `C` >> fs[] >> rpt strip_tac >> Cases_on `inGBA G1 h`
       >> fs[]
       >- metis_tac[]
       >- (qunabbrev_tac `G2` >> rw[] >> fs[addNodeToGBA_def,addNode_def])
       >- (qunabbrev_tac `G2` >> rw[] >> fs[addNodeToGBA_def,addNode_def]
           >> `~(i = G1.next)` by (
                fs[suff_wfg_def]
                >> `~(G1.next <= i)` by metis_tac[domain_lookup]
                >> fs[]
            )
           >> metis_tac[lookup_insert]
          )
       >- (fs[frml_ad_def] >> rpt strip_tac
           >> qunabbrev_tac `G2` >> fs[addNodeToGBA_def]
           >> Cases_on `inGBA G1 h` >> fs[addNode_def]
           >- (`n = nodeLabelGBA h` by metis_tac[lookup_insert,SOME_11]
               >> fs[]
              )
           >- (fs[suff_wfg_def] >> `~(G1.next <= i)` by metis_tac[]
               >> `~(G1.next = i)` by fs[]
               >> `lookup i G1.nodeInfo = SOME n`
                  by metis_tac[lookup_insert,SOME_11]
               >> metis_tac[]
              )
          )
      )
  );

val addEdgeToGBA_def = Define`
  addEdgeToGBA g id eL suc =
    case findNode (λ(i,q). MEM_EQUAL q.frmls suc) g of
      | SOME (i,q) =>  addEdge id (eL,i) g
      | NONE => NONE`;

val ADDEDGE_GBA_LEMM = store_thm
  ("ADDEDGE_GBA_LEMM",
   ``!g id eL suc.
     wfg g ∧ (id ∈ domain g.nodeInfo) ∧ (inGBA g suc)
     ==> (?g2. (addEdgeToGBA g id eL suc = SOME g2)
             ∧ (g.nodeInfo = g2.nodeInfo)
             ∧ wfg g2)``,
   rpt strip_tac >> simp[addEdgeToGBA_def]
   >> Cases_on `findNode (λ(i,q). MEM_EQUAL q.frmls suc) g` >> fs[]
   >- (
    fs[inGBA_def,EXISTS_MEM,findNode_def,MEM_MAP]
    >> `(λ(i,q). MEM_EQUAL q.frmls suc) y` by (Cases_on `y` >> fs[] >> rw[])
    >> metis_tac[FIND_LEMM,NOT_SOME_NONE]
   )
   >- (
    Cases_on `x` >> fs[] >>
    ‘∃g2. addEdge id (eL,q) g = SOME g2’ suffices_by
      metis_tac[addEdge_preserves_wfg, addEdge_preserves_nodeInfo] >>
    dsimp[addEdge_def] >> fs [findNode_def] >>
    drule_then strip_assume_tac FIND_LEMM2 >>
    metis_tac[wfg_def,domain_lookup, MEM_toAList]
  )
);

val ADDEDGE_GBA_FOLDR_LEMM = store_thm
  ("ADDEDGE_GBA_FOLDR_LEMM",
   ``!g id ls.
     wfg g ∧ (id ∈ domain g.nodeInfo) ∧ (!x. MEM x (MAP SND ls) ==> inGBA g x)
     ==>
     ?g2.
      (FOLDR
       (λ(eL,suc) g_opt.
         do g <- g_opt; addEdgeToGBA g id eL suc od)
       (SOME g) ls = SOME g2)
      ∧ (g.nodeInfo = g2.nodeInfo) ∧ wfg g2``,
   gen_tac >> gen_tac >> Induct_on `ls` >> fs[] >> rpt strip_tac >> fs[]
   >> Cases_on `h` >> fs[] >> HO_MATCH_MP_TAC ADDEDGE_GBA_LEMM
   >> fs[] >> rw[]
   >- metis_tac[]
   >- (`inGBA g r` by fs[]
       >> fs[inGBA_def] >> metis_tac[]
      )
  );

val extractGBATrans_def = Define`
  extractGBATrans aP g q =
     (set o OPTION_TO_LIST)
      (do (id,n) <- findNode (λ(i,n). ((set n.frmls) = q)) g ;
          fls <- lookup id g.followers ;
          SOME (
              (CAT_OPTIONS
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
          )
       od) `;

val concr2AbstrGBA_final_def = Define`
  concr2AbstrGBA_final final_forms graph aP =
    { {(set q1.frmls, transformLabel aP eL.pos_lab eL.neg_lab, set q2.frmls) |
         ?id1 id2 fls.
          (lookup id1 graph.nodeInfo = SOME q1)
        ∧ (lookup id1 graph.followers = SOME fls)
        ∧ (MEM (eL,id2) fls) ∧ (MEM f eL.acc_set)
        ∧ (lookup id2 graph.nodeInfo = SOME q2)
      } | f | (f ∈ final_forms)
    }`;

val concr2AbstrGBA_states_def = Define`
  concr2AbstrGBA_states graph =
    { set x.frmls | SOME x ∈
                   (IMAGE (\n. lookup n graph.nodeInfo)
                          (domain graph.nodeInfo))}`;

val concr2AbstrGBA_init_def = Define`
  concr2AbstrGBA_init concrInit graph =
    set (CAT_OPTIONS (MAP (\i. do n <- lookup i graph.nodeInfo ;
                                  SOME (set n.frmls)
                               od ) concrInit))`;

val concr2AbstrGBA_def = Define `
     concr2AbstrGBA (concrGBA graph init all_acc_frmls aP) =
       GBA
         (concr2AbstrGBA_states graph)
         (concr2AbstrGBA_init init graph)
         (extractGBATrans (set aP) graph)
         (concr2AbstrGBA_final (set all_acc_frmls) graph (set aP))
         (POW (set aP))`;

val _ = export_theory();
