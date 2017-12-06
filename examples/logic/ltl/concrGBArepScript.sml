open HolKernel Parse bossLib boolLib gfgTheory listTheory optionTheory pred_setTheory

open sptreeTheory ltlTheory generalHelpersTheory concrRepTheory concrltl2waaTheory

val _ = new_theory "concrGBARep"

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
   ``!x s. (ALL_DISTINCT s) ∧ MEM x (gba_trans_concr s)
        ==> ((!l. MEM l s
                 ==> (?cE. MEM cE l
                   ∧ (MEM_SUBSET cE.pos x.pos)
                   ∧ (MEM_SUBSET cE.neg x.neg)
                   ∧ (MEM_SUBSET cE.sucs x.sucs)
                     ))
        ∧ (?f. (x = FOLDR
                    (λsF e.
                     <|pos := sF.pos ⧺ e.pos; neg := sF.neg ⧺ e.neg;
                       sucs := sF.sucs ⧺ e.sucs|>)
                    (concrEdge [] [] []) (MAP f s))
            ∧ (!q. MEM q s ==> MEM (f q) q)))``,
   Q.HO_MATCH_ABBREV_TAC
    `!x s. AD s ∧ MEM x (gba_trans_concr s) ==> A x s ∧ B x s`
   >> `!x s. AD s ∧ MEM x (gba_trans_concr s) ==> A x s ∧ (A x s ==> B x s)`
      suffices_by fs[]
   >> qunabbrev_tac `A` >> qunabbrev_tac `B` >> qunabbrev_tac `AD`
   >> Induct_on `s` >> fs[gba_trans_concr_def] >> rpt strip_tac
   >- (fs[d_conj_concr_def,FOLDR_LEMM4] >> qexists_tac `e1` >> simp[]
       >> metis_tac[MEM_SUBSET_APPEND]
      )
   >- (fs[d_conj_concr_def,FOLDR_LEMM4]
       >> `∃cE.
            MEM cE l ∧ MEM_SUBSET cE.pos e2.pos ∧
            MEM_SUBSET cE.neg e2.neg ∧ MEM_SUBSET cE.sucs e2.sucs`
          by metis_tac[]
       >> metis_tac[MEM_SUBSET_APPEND,MEM_SUBSET_TRANS]
      )
   >- (fs[d_conj_concr_def,FOLDR_LEMM4]
       >> first_x_assum (qspec_then `e2` mp_tac) >> simp[] >> strip_tac
       >> `∃f.
           e2 =
            FOLDR
              (λsF e.
                 <|pos := sF.pos ⧺ e.pos; neg := sF.neg ⧺ e.neg;
                  sucs := sF.sucs ⧺ e.sucs|>) (concrEdge [] [] [])
              (MAP f s)
              ∧ (!q. MEM q s ==> MEM (f q) q)` by metis_tac[]
       >> qexists_tac `λq. if q = h then e1 else f q` >> simp[]
       >> `MAP (λq. if q = h then e1 else f q) s = MAP f s` by (
            metis_tac[MAP_LEMM]
        )
       >> rw[FOLDR_CONCR_EDGE]
      )
  );

val GBA_TRANS_LEMM2 = store_thm
  ("GBA_TRANS_LEMM2",
   ``!s f. (!q. MEM q s ==> MEM (f q) q)
  ==> MEM (FOLDR
                (λsF e.
                     <|pos := sF.pos ⧺ e.pos; neg := sF.neg ⧺ e.neg;
                 sucs := sF.sucs ⧺ e.sucs|>)
                (concrEdge [] [] []) (MAP f s)) (gba_trans_concr s)``,
   Induct_on `s` >> fs[gba_trans_concr_def]
   >> rw[FOLDR_CONCR_EDGE] >> first_x_assum (qspec_then `f` mp_tac) >> simp[]
   >> rpt strip_tac >> simp[d_conj_concr_def] >> rw[FOLDR_LEMM4]
   >> qexists_tac `f h` >> fs[]
   >> qexists_tac `(FOLDR
                        (λsF e.
                             <|pos := sF.pos ⧺ e.pos; neg := sF.neg ⧺ e.neg;
                         sucs := sF.sucs ⧺ e.sucs|>) (concrEdge [] [] [])
                        (MAP f s))`
   >> fs[FOLDR_CONCR_EDGE]
  );


val GBA_TRANS_LEMM = store_thm
  ("GBA_TRANS_LEMM",
   ``!aP trns_concr_list.
     ALL_DISTINCT (MAP SND trns_concr_list)
   ∧ ALL_DISTINCT (MAP FST trns_concr_list)
   (* ∧ (EVERY (ALL_DISTINCT o SND) trns_concr_list) *)
   ==>
     let concr_edgs_list = MAP SND trns_concr_list
     in let to_abstr l = MAP (concr2AbstractEdge aP) l
     in let abstr_trns_list = MAP to_abstr concr_edgs_list
     in let abstr_trns_set = set (MAP set abstr_trns_list)
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
       `?f. y =
          FOLDR
              (λsF e.
                   <|pos := sF.pos ⧺ e.pos; neg := sF.neg ⧺ e.neg;
                     sucs := sF.sucs ⧺ e.sucs|>) (concrEdge [] [] [])
              (MAP f (MAP SND trns_concr_list))
              ∧ (!q. MEM q (MAP SND trns_concr_list)
                     ==> MEM (f q) q)` by metis_tac[GBA_TRANS_LEMM1]
       >> qabbrev_tac
            `a_sel = λq.
              if ?d. MEM (q,d) trns_concr_list
              then (let d = @x. MEM (q,x) trns_concr_list
                    in transformLabel aP (f d).pos (f d).neg)
              else ARB`
       >> qabbrev_tac
           `e_sel = λq.
             if ?d. MEM (q,d) trns_concr_list
             then (let d = @x. MEM (q,x) trns_concr_list
                   in set ((f d).sucs))
             else ARB`
       >> `concr2AbstractEdge aP y =
            ((POW aP) ∩ BIGINTER {a_sel q | q ∈ IMAGE FST s},
             BIGUNION {e_sel q | q ∈ IMAGE FST s})` by (
            simp[concr2AbstractEdge_def,FOLDR_LEMM6]
            >> rw[FOLDR_CONCR_EDGE] >> simp[concr2AbstractEdge_def]
            >> rpt strip_tac
            >- (simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
             >- (qunabbrev_tac `A` >> metis_tac[TRANSFORMLABEL_AP,SUBSET_DEF])
             >- (`x ∈ a_sel q` suffices_by rw[]
                 >> qunabbrev_tac `s` >> qunabbrev_tac `a_sel` >> fs[]
                 >> `∃d. MEM (FST x',d) trns_concr_list` by (
                    fs[MEM_ZIP,MEM_EL]
                    >> qexists_tac `SND (EL n' trns_concr_list)`
                    >> qexists_tac `n'` >> fs[LENGTH_MAP,EL_MAP]
                    >> Cases_on `EL n' trns_concr_list` >> fs[]
                 )
                 >> `x ∈ transformLabel aP
                       (f (@x. MEM (FST x',x) trns_concr_list)).pos
                       (f (@x. MEM (FST x',x) trns_concr_list)).neg`
                  suffices_by metis_tac[]
               >> `d = (@x. MEM (FST x',x) trns_concr_list)` by (
                    `(λk. (k = d)) ($@ (λx. MEM (FST x',x) trns_concr_list))`
                      suffices_by fs[]
                    >> Q.HO_MATCH_ABBREV_TAC `Q ($@ M)`
                    >> HO_MATCH_MP_TAC SELECT_ELIM_THM >> qunabbrev_tac `Q`
                    >> rpt strip_tac >> fs[] >> qunabbrev_tac `M`
                    >- metis_tac[]
                    >- metis_tac[ALL_DISTINCT_PAIRS_LEMM]
               )
               >> `x ∈ transformLabel aP (f d).pos (f d).neg` suffices_by fs[]
               >> `MEM (FST x', d) trns_concr_list` by metis_tac[SELECT_THM]
               >> `MEM d (MAP SND trns_concr_list)` by (
                    simp[MEM_MAP] >> qexists_tac `(FST x',d)` >> fs[]
               )
               >> `MEM (f d) (MAP f (MAP SND trns_concr_list))` by (
                   simp[MEM_MAP] >> qexists_tac `d` >> fs[]
                   >> qexists_tac `(FST x',d)` >> fs[]
               )
               >> metis_tac[TRANSFORMLABEL_SUBSET,FOLDR_APPEND,SUBSET_DEF]
                )
             >- (`!q. MEM q (MAP FST trns_concr_list) ==> x ∈ a_sel q` by (
                   rpt strip_tac >> fs[MEM_MAP]
                   >> first_x_assum (qspec_then `a_sel q` mp_tac)
                   >> simp[] >> Q.HO_MATCH_ABBREV_TAC `(Q ==> B) ==> B`
                   >> `Q` suffices_by fs[] >> qunabbrev_tac `Q`
                   >> qexists_tac `q` >> rw[]
                   >> qunabbrev_tac `s` >> simp[MEM_MAP]
                   >> qexists_tac
                        `(λ(q,d). (q,set (MAP (concr2AbstractEdge aP) d))) y`
                   >> simp[] >> Cases_on `y` >> simp[] >> qexists_tac `(q,r)`
                   >> simp[]
                )
                >> `(∀e. MEM e (MAP f (MAP SND trns_concr_list))
                      ⇒ x ∈ transformLabel aP e.pos e.neg) ∧ x ∈ POW aP`
                   suffices_by metis_tac[TRANSFORMLABEL_FOLDR]
                >> rpt strip_tac >> fs[MEM_MAP]
                >> `x ∈ a_sel (FST y')` by metis_tac[]
                >> qunabbrev_tac `a_sel` >> fs[]
                >> `x ∈
                     transformLabel aP
                     (f (@x. MEM (FST y',x) trns_concr_list)).pos
                     (f (@x. MEM (FST y',x) trns_concr_list)).neg` by (
                    `∃d. MEM (FST y',d) trns_concr_list` suffices_by metis_tac[]
                    >> qexists_tac `SND y'` >> fs[]
                )
                >> `(@x. MEM (FST y',x) trns_concr_list) = SND y'` by (
                    `(λk. (k = SND y')) ($@ (λx. MEM (FST y',x) trns_concr_list))`
                      suffices_by fs[]
                    >> Q.HO_MATCH_ABBREV_TAC `Q ($@ M)`
                    >> HO_MATCH_MP_TAC SELECT_ELIM_THM >> qunabbrev_tac `Q`
                    >> rpt strip_tac >> fs[] >> qunabbrev_tac `M`
                    >- (qexists_tac `SND y'` >> fs[])
                    >- (Cases_on `y'` >> fs[]
                        >> metis_tac[ALL_DISTINCT_PAIRS_LEMM])
                )
                >> Cases_on `y'` >> rw[] >> fs[]
                )
               )
            >- (`BIGUNION {e_sel q | ?x. q = FST x ∧ x ∈ s} =
                 BIGUNION {set d.sucs | MEM d
                                          (MAP f (MAP SND trns_concr_list))}`
                 by (
                  `!q r. MEM (q,r) trns_concr_list
                      ==> ((?d. MEM (q,d) trns_concr_list)
                         ∧ (r = @x. MEM (q,x) trns_concr_list))` by (
                      rpt strip_tac
                      >- metis_tac[]
                      >- (`(λk. (k = r)) ($@ (λx. MEM (q,x)
                                                  trns_concr_list))`
                         suffices_by fs[]
                         >> Q.HO_MATCH_ABBREV_TAC `Q ($@ M)`
                         >> HO_MATCH_MP_TAC SELECT_ELIM_THM >> qunabbrev_tac `Q`
                         >> rpt strip_tac >> fs[] >> qunabbrev_tac `M`
                         >- metis_tac[]
                         >- metis_tac[ALL_DISTINCT_PAIRS_LEMM]
                         )
                  )
                  >> qunabbrev_tac `e_sel` >> simp[MEM_MAP] >> qunabbrev_tac `s`
                  >> simp[MEM_MAP,SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                  >- (Cases_on `y` >> fs[] >> rw[]
                      >> qexists_tac `set (f r).sucs` >> fs[] >> strip_tac
                      >- metis_tac[]
                      >- (qexists_tac `f r` >> fs[] >> qexists_tac `r` >> fs[]
                         >> qexists_tac `(q,r)` >> fs[])
                     )
                  >- (Cases_on `y'` >> fs[]
                      >> qexists_tac `set d.sucs` >> fs[]
                      >> qexists_tac `q` >> fs[] >> rpt strip_tac >> rw[]
                      >- metis_tac[]
                      >- metis_tac[]
                      >- metis_tac[]
                      >- (qexists_tac `(q,set (MAP (concr2AbstractEdge aP)r))`
                          >> fs[] >> qexists_tac `(q,r)` >> fs[]
                         )
                     )
                    )
                 >> metis_tac[FOLDR_APPEND,LIST_TO_SET,UNION_EMPTY]
               )
        )
       >> `(∀q d. (q,d) ∈ s ⇒ (a_sel q,e_sel q) ∈ d
             ∧ BIGINTER {a_sel q | q ∈ IMAGE FST s} ⊆ a_sel q)
           ∧ BIGINTER {a_sel q | q ∈ IMAGE FST s} ⊆ A`
           suffices_by metis_tac[FINITE_LIST_TO_SET,D_CONJ_SET_LEMM3]
       >> `!q r. (q,r) ∈ s
           ==> (?d. MEM (q,d) trns_concr_list
                 ∧ (r = set (MAP (concr2AbstractEdge aP) d))
                 ∧ ((@x. MEM (q,x) trns_concr_list) = d))` by (
            rpt strip_tac >> qunabbrev_tac `s` >> fs[MEM_MAP]
            >> Cases_on `y'` >> fs[]
            >> `r' = (@x. MEM (q',x) trns_concr_list)` by (
                `(λk. (k = r')) ($@ (λx. MEM (q',x)
                                        trns_concr_list))`
                  suffices_by fs[]
                >> Q.HO_MATCH_ABBREV_TAC `Q ($@ M)`
                >> HO_MATCH_MP_TAC SELECT_ELIM_THM >> qunabbrev_tac `Q`
                >> rpt strip_tac >> fs[] >> qunabbrev_tac `M`
                >- metis_tac[]
                >- metis_tac[ALL_DISTINCT_PAIRS_LEMM]
            )
            >> rw[]
        )
       >> rpt strip_tac
       >- (qunabbrev_tac `a_sel` >> qunabbrev_tac `e_sel`
           >> first_x_assum (qspec_then `q` mp_tac) >> rpt strip_tac
           >> first_x_assum (qspec_then `d` mp_tac) >> simp[] >> strip_tac
           >> simp[MEM_MAP] >> qabbrev_tac `D = @x. MEM (q,x) trns_concr_list`
           >> qexists_tac `f D` >> fs[]
           >> `(transformLabel aP (f D).pos (f D).neg, set (f D).sucs) =
                  concr2AbstractEdge aP (f D) ∧ MEM (f D) D`
              suffices_by metis_tac[]
           >> Cases_on `f D` >> simp[concr2AbstractEdge_def]
           >> `MEM D (MAP SND trns_concr_list)` suffices_by metis_tac[]
           >> fs[MEM_MAP] >> qexists_tac `(q,D)` >> fs[]
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
     >> `∀q d. (q,d) ∈ s ⇒ ∃a' e'. (a',e') ∈ d ∧ a ⊆ a' ∧ e' ⊆ e`
         by metis_tac[D_CONJ_SET_LEMM2,FINITE_LIST_TO_SET]
     >> `?f_a f_e.
          !q d. (q,d) ∈ s ==> ((f_a q d,f_e q d) ∈ d
                            ∧ (a ⊆ f_a q d) ∧ (f_e q d ⊆ e))`
          by metis_tac[SKOLEM_THM]
     >> qunabbrev_tac `s` >> fs[MEM_MAP]
     >> `?f. !y q d.
          ((q,d) = (λ(q,d). (q,set (MAP (concr2AbstractEdge aP) d))) y)
          ∧ (MEM y trns_concr_list)
          ==> (MEM (f y) (SND y)
             ∧ (concr2AbstractEdge aP (f y) = (f_a q d,f_e q d)))` by (
         qabbrev_tac `sel =
           λy.
            if MEM y trns_concr_list
            then
             let (q,d) = (λ(q,d). (q,set (MAP (concr2AbstractEdge aP) d))) y
             in @cE. MEM cE (SND y)
                   ∧ concr2AbstractEdge aP cE = (f_a q d,f_e q d)
            else ARB`
         >> qexists_tac `sel` >> fs[] >> rpt gen_tac >> strip_tac
         >> `sel y =
              (λ(q,d).
                @cE.
                  MEM cE (SND y)
                  ∧ concr2AbstractEdge aP cE = (f_a q d,f_e q d))
                  ((λ(q,d). (q,set (MAP (concr2AbstractEdge aP) d))) y)` by (
             qunabbrev_tac `sel` >> fs[]
         )
         >> `?q1 ce_list. y = (q1,ce_list)` by (Cases_on `y` >> fs[])
         >> fs[]
         >> Q.HO_MATCH_ABBREV_TAC
              `MEM ($@ P) ce_list
             ∧ concr2AbstractEdge aP ($@ P) = (A,E)`
         >> qabbrev_tac `Q =
                 λc. MEM c ce_list
                   ∧ concr2AbstractEdge aP c = (A,E)`
         >> `Q ($@ P)` suffices_by fs[] >> HO_MATCH_MP_TAC SELECT_ELIM_THM
         >> qunabbrev_tac `P` >> qunabbrev_tac `Q` >> fs[]
         >> first_x_assum (qspec_then `q` mp_tac) >> rpt strip_tac
         >> first_x_assum (qspec_then `d` mp_tac) >> rpt strip_tac
         >> `(f_a q d,f_e q d) ∈ d ∧ a ⊆ f_a q d ∧ f_e q d ⊆ e` by (
           `∃y.
            (q,d) = (λ(q,d). (q,set (MAP (concr2AbstractEdge aP) d))) y
                  ∧ MEM y trns_concr_list` suffices_by fs[]
           >> qexists_tac `y` >> rw[] >> fs[]
         )
         >> rw[] >> fs[MEM_MAP] >> metis_tac[]
     )
     >> GBA_TRANS_LEMM2
)
)


)



   gen_tac
   >> Induct_on `trns_concr_list`
   >> fs[d_conj_set_def,gba_trans_concr_def]
   >- (rw[ITSET_THM,ZIP_def]
       >> simp[concr2AbstractEdge_def,transformLabel_def]
      )
   >- (rpt strip_tac
       >> Q.HO_MATCH_ABBREV_TAC `
           set (MAP c2A (d_conj_concr (SND h) (R_L)))
            = ITSET (d_conj o SND)
                    (((FST h,set (MAP c2A (SND h)))) INSERT
                    R_R) {(POW aP,{})}`
       >> `set (MAP c2A (d_conj_concr (SND h) R_L)) =
           (d_conj o SND) (FST h,set (MAP c2A (SND h)))
              (ITSET (d_conj o SND) (R_R DELETE (FST h,set (MAP c2A (SND h))))
                     {(POW aP,{})})` suffices_by (
            Q.HO_MATCH_ABBREV_TAC `A = B ==> A = C`
            >> `C = B` suffices_by fs[] >> qunabbrev_tac `B`
            >> qunabbrev_tac `C`
            >> `FINITE R_R` suffices_by metis_tac[D_CONJ_SET_RECURSES]
            >> metis_tac[FINITE_LIST_TO_SET]
        )
       >> simp[d_conj_concr_def,SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
       >- (fs[MEM_MAP,FOLDR_LEMM4] 

)

       >> `R_R DELETE (FST h,set (MAP c2A (SND h))) = R_R` by (
            `~((FST h,set (MAP c2A (SND h))) ∈ R_R)`
               suffices_by metis_tac[DELETE_NON_ELEMENT]
            >> CCONTR_TAC >> qunabbrev_tac `R_R` >> fs[MEM_ZIP]
            >> `FST h = FST (EL n trns_concr_list)` by metis_tac[EL_MAP]
            >> fs[MAP_MAP_o]
            >> `set (MAP c2A (SND h)) =
                 (set o (λl. MAP c2A l) o SND) (EL n trns_concr_list)`
               by metis_tac[EL_MAP]
            >> fs[]
            >> `EL n trns_concr_list = h` by (
                Cases_on `EL n trns_concr_list` >> Cases_on `h` >> fs[] >> rw[]
                >> 
)
 
)

)




)




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

val addEdgeToGBA_def = Define`
  addEdgeToGBA g id eL suc =
    case findNode (λ(i,q). MEM_EQUAL q.frmls suc) g of
      | SOME (i,q) =>  addEdge id (eL,i) g
      | NONE => NONE`;

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
                             (concrEdge eL.pos_lab eL.neg_lab (f::MAP SND xs))
                 ) aa_edges_grpd)
        in do node <- lookup aa_id g_AA.nodeInfo ;
              true_edges <-
                SOME (MAP
                       (λeL. (concrEdge eL.pos_lab eL.neg_lab []))
                       node.true_labels) ;
              SOME (concr_edges ++ true_edges)
           od`;


(*TODO: prove termination*)
val expandGBA_def = Define`
   (expandGBA g_AA acc [] G = SOME G)
 ∧ (expandGBA g_AA acc (id::ids) G =
    case lookup id G.nodeInfo of
      | NONE => NONE
      | SOME current_node =>
       let aa_frml_ids =
            CAT_OPTIONS
              (MAP (λf. OPTION_MAP FST
                          (findNode (λ(i,l). l.frml = f) g_AA)
                   )
                  current_node.frmls)
       in let concr_edges =
               CAT_OPTIONS
                 (MAP (concr_extrTrans g_AA) aa_frml_ids)
       in let trans_unopt = gba_trans_concr concr_edges
       in let flws_with_acc_sets =
               MAP (λcE.
                     let acc_sets =
                      CAT_OPTIONS
                         (MAP (λ(f,f_trans).
                               if acc_cond_concr cE f f_trans
                               then (SOME f)
                               else NONE
                             ) acc
                         )
                     in (cE,acc_sets)
                   ) trans_unopt
       in let trans = ONLY_MINIMAL tlg_concr flws_with_acc_sets
       in let new_sucs =
                FILTER (λqs. ~inGBA G qs)
                   (MAP (λ(cE,fs). cE.sucs) trans)
       in let (new_ids, G1) =
                FOLDR (λn (ids,g). ((g.next::ids),addNodeToGBA g n))
                      ([],G) new_sucs
       in do G2 <-
              FOLDR
                (λ(eL,suc) g_opt. do g <- g_opt ;
                                     addEdgeToGBA g id eL suc
                                  od)
                (SOME G1)
                (MAP (λ(cE,f). (edgeLabelGBA cE.pos cE.neg f,cE.sucs)) trans) ;
             expandGBA g_AA acc (ids ++ new_ids) G2
          od
   )`;

val expandGBA_init_def = Define`
  expandGBA_init (concrAA g_AA initAA props) =
    let initNodes = MAP (λi_list.
                          let suc_nLabels = MAP (λn. lookup i g_AA.nodeInfo)
                          in MAP (λl. l.frml) (CAT_OPTIONS suc_nLabels)
                        ) initAA
    in let G0 = FOLDR addNodeToGraph empty initNodes
    in let initIds = MAP FST (toAList G0)
    in let acc_sets = FILTER is_until (graphStates g_AA)
    in let graph = expandGBA g_AA acc_sets initIds G0
    in concrGBA graph initIds props`;





