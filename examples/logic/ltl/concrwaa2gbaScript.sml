open HolKernel Parse bossLib boolLib gfgTheory listTheory optionTheory pred_setTheory relationTheory pairTheory prim_recTheory set_relationTheory arithmeticTheory rich_listTheory

open sptreeTheory ltlTheory generalHelpersTheory concrGBArepTheory concrRepTheory waa2baTheory buechiATheory gbaSimplTheory alterATheory ltl2waaTheory waaSimplTheory concrltl2waaTheory

val _ = new_theory "concrwaa2gba"
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = Cond_rewr.stack_limit := 2

val _ = monadsyntax.temp_add_monadsyntax();
val _ = overload_on("monad_bind",``OPTION_BIND``);


val get_acc_set_def = Define`
  get_acc_set acc ce =
    CAT_OPTIONS (MAP (λ(f,f_trans).
                   if acc_cond_concr ce f f_trans
                   then SOME f
                   else NONE
                 ) acc
            )`;

val GET_ACC_SET_LEMM = store_thm
  ("GET_ACC_SET_LEMM",
   ``!acc ce1 ce2.
        (MEM_EQUAL ce1.pos ce2.pos)
        ∧ (MEM_EQUAL ce1.neg ce2.neg)
        ∧ (MEM_EQUAL ce1.sucs ce2.sucs)
        ==> (get_acc_set acc ce1 = get_acc_set acc ce2)``,
   rpt strip_tac >> fs[get_acc_set_def]
   >> `!f f_tr. acc_cond_concr ce1 f f_tr = acc_cond_concr ce2 f f_tr`
       suffices_by metis_tac[]
   >> rpt strip_tac >> Cases_on `ce1` >> Cases_on `ce2`
   >> simp[acc_cond_concr_def,trns_is_empty_def]
   >> fs[concrEdge_component_equality]
   >> simp[MEM_SUBSET_SET_TO_LIST,MEM_EQUAL_SET,EXISTS_MEM]
   >> fs[MEM_EQUAL_SET] >> rw[]
  );

val _ = diminish_srw_ss ["ABBREV_CONG"]
val valid_acc_def = Define`
  valid_acc aP g_AA acc =
    ((!f f_trns. MEM (f,f_trns) acc ==>
        ?id nL. (findNode (λ(i,l). l.frml = f) g_AA = SOME (id,nL))
        ∧ (SOME f_trns = concr_extrTrans g_AA id)
        ∧ (!ce. MEM ce f_trns ==>
                (set ce.pos ⊆ set aP ∧ set ce.neg ⊆ set aP)
          )
        ∧ is_until f
    )
    ∧ (!f. (is_until f ∧ MEM f (graphStates g_AA))
           ==> ?f_trns. MEM (f,f_trns) acc))`;

val VALID_ACC_LEMM = store_thm
  ("VALID_ACC_LEMM",
   ``!aP acc g_AA. valid_acc aP g_AA acc ∧ until_iff_final g_AA
        ==> !f. MEM f (MAP FST acc) ⇔ f ∈ concr2Abstr_final g_AA``,
   simp[EQ_IMP_THM] >> fs[valid_acc_def,concr2Abstr_final_def] >> rpt strip_tac
   >> fs[MEM_MAP]
   >- (Cases_on `y` >> fs[] >> rw[] >> rename[`MEM (f,f_trns) acc`]
       >> `∃id nL.
             (findNode (λ(i,l). l.frml = f) g_AA = SOME (id,nL))
             ∧ (SOME f_trns = concr_extrTrans g_AA id)
             ∧ (∀ce.
                 MEM ce f_trns ⇒
                 set ce.pos ⊆ set aP ∧ set ce.neg ⊆ set aP)
             ∧ is_until f` by metis_tac[]
       >> qexists_tac `nL`
       >> `(MEM (id,nL) (toAList g_AA.nodeInfo))
         ∧ ((λ(i,l). l.frml = f) (id,nL))` by metis_tac[FIND_LEMM2,findNode_def]
       >> fs[until_iff_final_def]
       >> first_x_assum (qspec_then `id` mp_tac) >> strip_tac
       >> first_x_assum (qspec_then `nL` mp_tac)
       >> `lookup id g_AA.nodeInfo = SOME nL` by metis_tac[MEM_toAList,SOME_11]
       >> simp[]
       >> `(∃f1 f2. f = U f1 f2)` by (Cases_on `f` >> fs[is_until_def]) >> simp[]
       >> metis_tac[MEM_toAList,domain_lookup]
      )
   >- (`is_until f` by (
         simp[is_until_def] >> fs[until_iff_final_def]
         >> `∃f1 f2. x.frml = U f1 f2` by metis_tac[]
         >> Cases_on `x` >> simp[is_until_def]
      )
      >> `MEM f (graphStates g_AA)` by (
          simp[graphStates_def,MEM_MAP] >> qexists_tac `(n,x)` >> fs[]
          >> metis_tac[MEM_toAList]
      )
      >> first_x_assum (qspec_then `f` mp_tac) >> simp[] >> strip_tac
      >> metis_tac[FST]
      )
  );

val CONCR_ACC_SETS = store_thm
  ("CONCR_ACC_SETS",
   ``!h g_AA init acc aP abstrAA.
    (abstrAA = concr2AbstrAA (concrAA g_AA init aP))
    ∧ (abstrAA = removeStatesSimpl (ltl2vwaa h))
    ∧ valid_acc aP g_AA acc
    ∧ wfg g_AA ∧ flws_sorted g_AA ∧ unique_node_formula g_AA
     ==>
     !ce u aE.
      (aE = concr2AbstractEdge (set aP) ce)
      ∧ is_until u ∧ MEM u (graphStates g_AA)
      ∧ MEM_SUBSET ce.pos aP ∧ MEM_SUBSET ce.neg aP
      ∧ MEM_SUBSET ce.sucs (graphStates g_AA)
       ==>
       (!qs2. qs2 ∈ POW abstrAA.states
         ==> (MEM u (get_acc_set acc ce) =
              ((qs2,FST aE,SND aE) ∈ acc_cond abstrAA u)))``,
   fs[] >> rpt strip_tac >> simp[EQ_IMP_THM] >> rpt strip_tac
   >> fs[CAT_OPTIONS_MEM,MEM_MAP]
   >> qabbrev_tac `aa_red = removeStatesSimpl (ltl2vwaa h)`
   >> `(aa_red).alphabet = POW (set aP)`
       by fs[concr2AbstrAA_def,ALTER_A_component_equality]
   >> `isValidAlterA (aa_red)` by (
       metis_tac[LTL2WAA_ISVALID,REDUCE_STATE_IS_VALID]
   )
   >- (
    simp[acc_cond_def] >> qexists_tac `FST (concr2AbstractEdge (set aP) ce)`
    >> qexists_tac `SND (concr2AbstractEdge (set aP) ce)` >> fs[]
    >> rpt strip_tac
    >- (simp[IN_POW,SUBSET_DEF] >> rpt strip_tac >> fs[]
        >> Cases_on `ce` >> fs[concr2AbstractEdge_def]
        >> fs[concr2AbstrAA_def,ALTER_A_component_equality]
        >> fs[concr2Abstr_states_def,graphStates_def]
        >> `MEM x (MAP ((λl. l.frml) ∘ SND) (toAList g_AA.nodeInfo))`
           by metis_tac[MEM_SUBSET_SET_TO_LIST,SUBSET_DEF]
        >> `x ∈ {x.frml |
                   ∃n. (SOME x = lookup n g_AA.nodeInfo)
                    ∧ (n ∈ domain g_AA.nodeInfo)}` suffices_by metis_tac[]
        >> fs[MEM_MAP] >> qexists_tac `(SND y')` >> fs[]
        >> Cases_on `y'` >> fs[]
        >> metis_tac[MEM_toAList,domain_lookup]
       )
    >- (simp[IN_POW,SUBSET_DEF] >> rpt strip_tac
        >> Cases_on `ce` >> fs[concr2AbstractEdge_def]
        >> metis_tac[TRANSFORMLABEL_AP,IN_POW,SUBSET_DEF]
       )
    >- (Cases_on `u ∈ SND (concr2AbstractEdge (set aP) ce)`
        >> fs[get_acc_set_def,CAT_OPTIONS_MEM,MEM_MAP]
        >> Cases_on `y` >> fs[] >> rw[]
        >> rename[`MEM (f,f_trns) acc`] >> fs[acc_cond_concr_def]
        >- (Cases_on `ce` >> fs[concr2AbstractEdge_def])
        >- (fs[valid_acc_def]
            >> Cases_on `EXISTS (λp. MEM p ce.neg) ce.pos` >> fs[]
            >> `∃id nL.
                 (findNode (λ(i,l). l.frml = f) g_AA = SOME (id,nL))
                 ∧ (SOME f_trns = concr_extrTrans g_AA id)` by metis_tac[]
            >> `∃n cT.
                  (concr_extrTrans g_AA id = SOME cT)
                  ∧ (lookup id g_AA.nodeInfo = SOME n)
                  ∧ (set (MAP (concr2AbstractEdge (set aP)) cT)) =
                    concrTrans g_AA (set aP) n.frml` by (
                 `?fls. lookup id g_AA.followers = SOME fls` by (
                     `id ∈ domain g_AA.nodeInfo` by (
                         fs[findNode_def]
                         >> metis_tac[FIND_LEMM2,MEM_toAList,domain_lookup]
                     )
                     >> metis_tac[wfg_def,domain_lookup]
                 )
                 >> IMP_RES_TAC CONCR_EXTRTRANS_LEMM
                 >> first_x_assum (qspec_then `id` mp_tac) >> simp[]
             )
            >> fs[] >> simp[concr2AbstrAA_def]
            >> `(n = nL) ∧ (n.frml = f)` by (
                 fs[findNode_def]
                 >> `(n = nL) ∧ ((λ(i,l). l.frml = f) (id,n))` suffices_by fs[]
                 >> metis_tac[FIND_LEMM2,MEM_toAList,SOME_11]
             )
            >> rw[]
            >- (fs[EXISTS_MEM,trns_is_empty_def]
                >> `concr2AbstractEdge (set aP) cE1 ∈
                    concrTrans g_AA (set aP) n.frml` by (
                     metis_tac[MEM_MAP]
                 )
                >> Cases_on `concr2AbstractEdge (set aP) cE1` >> fs[]
                >> rename[`_ = (a,e)`]
                >> qexists_tac `a` >> qexists_tac `e` >> Cases_on `cE1`
                >> fs[concr2AbstractEdge_def] >> rpt strip_tac
                >- (`FST (concr2AbstractEdge (set aP) ce) = {}` suffices_by fs[]
                    >> Cases_on `ce` >> fs[concr2AbstractEdge_def]
                    >> rename[`transformLabel (set aP) pos neg`]
                    >> `set pos ∩ set neg ≠ ∅`
                         suffices_by metis_tac[TRANSFORMLABEL_EMPTY,
                                               MEM_SUBSET_SET_TO_LIST]
                    >> `?x. x ∈ set pos ∧ x ∈ set neg`
                         suffices_by metis_tac[IN_INTER,MEMBER_NOT_EMPTY]
                    >> metis_tac[MEM]
                   )
                >- (Cases_on `ce` >> fs[concr2AbstractEdge_def]
                    >> metis_tac[MEM_SUBSET_SET_TO_LIST])
               )
         >- (fs[trns_is_empty_def]
             >> `EXISTS
               (λcE1.
                    MEM_SUBSET cE1.pos ce.pos ∧ MEM_SUBSET cE1.neg ce.neg ∧
                    MEM_SUBSET cE1.sucs ce.sucs ∧ ¬MEM n.frml cE1.sucs) cT`
               by metis_tac[NOT_EXISTS]
            >> fs[EXISTS_MEM]
            >> `concr2AbstractEdge (set aP) cE1 ∈
                               concrTrans g_AA (set aP) n.frml` by (
                 metis_tac[MEM_MAP]
             )
            >> Cases_on `concr2AbstractEdge (set aP) cE1` >> fs[]
            >> rename[`_ = (a,e)`] >> qexists_tac `a` >> qexists_tac `e`
            >> fs[] >> rpt strip_tac >> Cases_on `ce` >> Cases_on `cE1`
            >> fs[concr2AbstractEdge_def]
            >- metis_tac[TRANSFORMLABEL_SUBSET]
            >- metis_tac[MEM_SUBSET_SET_TO_LIST]
            )
           )
       )
   )
   >- (simp[get_acc_set_def,CAT_OPTIONS_MEM,MEM_MAP]
       >> fs[valid_acc_def]
       >> `?u_trns. MEM (u,u_trns) acc` by metis_tac[]
       >> qexists_tac `(u,u_trns)` >> fs[] >> simp[acc_cond_concr_def]
       >> fs[acc_cond_def]
       >- (disj1_tac >> Cases_on `ce` >> fs[concr2AbstractEdge_def])
       >- (Cases_on `MEM u ce.sucs` >> fs[]
           >> Cases_on `EXISTS (λp. MEM p ce.neg) ce.pos` >> fs[]
           >> `∃id nL.
                (findNode (λ(i,l). l.frml = u) g_AA = SOME (id,nL))
                ∧ (SOME u_trns = concr_extrTrans g_AA id)` by metis_tac[]
           >> `∃n cT.
                (concr_extrTrans g_AA id = SOME cT)
                ∧ (lookup id g_AA.nodeInfo = SOME n)
                ∧ (set (MAP (concr2AbstractEdge (set aP)) cT)
                   = concrTrans g_AA (set aP) n.frml)` by (
               `?fls. lookup id g_AA.followers = SOME fls` by (
                 `id ∈ domain g_AA.nodeInfo` by (
                     fs[findNode_def]
                     >> metis_tac[FIND_LEMM2,MEM_toAList,domain_lookup]
                 )
                 >> metis_tac[wfg_def,domain_lookup]
               )
               >> IMP_RES_TAC CONCR_EXTRTRANS_LEMM
               >> first_x_assum (qspec_then `id` mp_tac) >> simp[]
            )
           >> fs[concr2AbstrAA_def,ALTER_A_component_equality]
           >> `(n = nL) ∧ (n.frml = u)` by (
                fs[findNode_def]
                  >> `(n = nL) ∧ ((λ(i,l). l.frml = u) (id,n))` suffices_by fs[]
                  >> metis_tac[FIND_LEMM2,MEM_toAList,SOME_11]
            )
           >> rw[] >> rename[`(α,sucs) ∈ aa_red.trans n.frml`]
           >> `(α,sucs) ∈ set (MAP (concr2AbstractEdge (set aP)) cT)`
                by metis_tac[]
           >> POP_ASSUM mp_tac >> simp[MEM_MAP] >> rpt strip_tac
           >> fs[EXISTS_MEM]
           >> `set y.pos ⊆ set aP ∧ set y.neg ⊆ set aP` by metis_tac[]
           >> qexists_tac `y` >> fs[] >> Cases_on `ce` >> Cases_on `y`
           >> fs[concr2AbstractEdge_def, MEM_SUBSET_SET_TO_LIST]
           >> `a ⊆ α` by rw[]
           >> `~(a = {})` by (
                fs[trns_is_empty_def,EVERY_MEM]
                >> `set l ∩ set l0 = {}` by (
                    PURE_REWRITE_TAC[SET_EQ_SUBSET,SUBSET_DEF,IN_INTER]
                    >> rpt strip_tac >> metis_tac[MEMBER_NOT_EMPTY]
                )
                >> metis_tac[TRANSFORMLABEL_EMPTY]
            )
           >> `MEM_SUBSET l' l ∧ MEM_SUBSET l0' l0`
                suffices_by metis_tac[MEM_SUBSET_SET_TO_LIST]
           >> rw[]
           >> `∀x. MEM x l ∨ MEM x l' ∨ MEM x l0 ∨ MEM x l0'
                ⇒ x ∈ set aP` suffices_by  metis_tac[TRANSFORMLABEL_SUBSET2]
           >> rpt strip_tac >> metis_tac[SUBSET_DEF,MEM]
          )
      )
  );

val TLG_CONCR_LEMM = store_thm
  ("TLG_CONCR_LEMM",
   ``!h g_AA init aP acc qs ce1 ce2 abstrAA.
  (abstrAA = concr2AbstrAA (concrAA g_AA init aP))
  ∧ (abstrAA = removeStatesSimpl (ltl2vwaa h))
  ∧ valid_acc aP g_AA acc
  ∧ wfg g_AA ∧ flws_sorted g_AA ∧ unique_node_formula g_AA
  ∧ (qs ∈ POW abstrAA.states)
  ∧ (!id cT. (concr_extrTrans g_AA id = SOME cT)
       ==> (!ce. MEM ce cT ==> (MEM_SUBSET ce.pos aP ∧ MEM_SUBSET ce.neg aP))
    )
     ==>
     !e1_lab e1_sucs e2_lab e2_sucs.
     MEM_SUBSET ce1.pos aP ∧ MEM_SUBSET ce1.neg aP
     ∧ MEM_SUBSET ce1.sucs (graphStates g_AA)
     ∧ MEM_SUBSET ce2.pos aP ∧ MEM_SUBSET ce2.neg aP
     ∧ MEM_SUBSET ce2.sucs (graphStates g_AA)
     ∧ ((e1_lab,e1_sucs) = concr2AbstractEdge (set aP) ce1)
     ∧ ((e2_lab,e2_sucs) = concr2AbstractEdge (set aP) ce2)
     ==>
     ((((e1_lab,e1_sucs),e2_lab,e2_sucs) ∈
          tr_less_general { acc_cond abstrAA f | MEM f (MAP FST acc) } qs) =
             (tlg_concr (ce1,get_acc_set acc ce1) (ce2,get_acc_set acc ce2)))``,
   rpt strip_tac >> fs[]
   >> simp[EQ_IMP_THM] >> rpt strip_tac
   >- (fs[tlg_concr_def,tr_less_general_def]
       >> `MEM_SUBSET ce1.sucs ce2.sucs` by (
        Cases_on `ce1` >> Cases_on `ce2`
        >> fs[concr2AbstractEdge_def] >> metis_tac[MEM_SUBSET_SET_TO_LIST]
      )
      >> fs[]
      >> `MEM_SUBSET (get_acc_set acc ce2) (get_acc_set acc ce1)` by (
         simp[MEM_SUBSET_SET_TO_LIST,SUBSET_DEF] >> rpt strip_tac
         >> `is_until x ∧ MEM x (graphStates g_AA)` by (
             fs[get_acc_set_def,CAT_OPTIONS_MEM,MEM_MAP]
             >> Cases_on `y` >> fs[valid_acc_def]
             >> `?id nL. (findNode (λ(i,l). l.frml = x) g_AA = SOME (id,nL))
                       ∧ (is_until x)`
                    by metis_tac[]
             >> fs[findNode_def]
             >> `(MEM (id,nL) (toAList g_AA.nodeInfo))
               ∧ (λ(i,l). l.frml = x) (id,nL)` by metis_tac[FIND_LEMM2]
             >> simp[graphStates_def,MEM_MAP] >> fs[]
             >> metis_tac[SND]
         )
         >> `(qs,FST (concr2AbstractEdge (set aP) ce2),
                 SND (concr2AbstractEdge (set aP) ce2)) ∈
               acc_cond (removeStatesSimpl (ltl2vwaa h)) x`
             by metis_tac[CONCR_ACC_SETS]
         >> fs[]
         >> `MEM x (MAP FST acc)` by (
             fs[valid_acc_def] >> simp[MEM_MAP]
             >> first_x_assum (qspec_then `x` mp_tac) >> simp[]
             >> rpt strip_tac >> qexists_tac `(x,f_trns)` >> simp[]
         )
         >> `(qs,concr2AbstractEdge (set aP) ce1) ∈
               acc_cond (removeStatesSimpl (ltl2vwaa h)) x` by metis_tac[]
         >> metis_tac[CONCR_ACC_SETS,FST,SND]
      )
      >> fs[]
      >> Cases_on `trns_is_empty ce2` >> fs[]
      >> `~(transformLabel (set aP) ce2.pos ce2.neg = ∅)`
         by metis_tac[TRNS_IS_EMPTY_LEMM,MEM_SUBSET_SET_TO_LIST]
      >> `∀x. MEM x ce1.pos ∨ MEM x ce2.pos ∨ MEM x ce1.neg ∨ MEM x ce2.neg
                 ⇒ x ∈ set aP` suffices_by (
          strip_tac
          >> Cases_on `ce2` >> Cases_on `ce1` >> fs[concr2AbstractEdge_def]
          >> metis_tac[TRANSFORMLABEL_SUBSET2]
      )
      >> rpt strip_tac >> metis_tac[SUBSET_DEF,MEM_SUBSET_SET_TO_LIST]
      )
   >- (`((MEM_SUBSET ce1.pos ce2.pos ∧ MEM_SUBSET ce1.neg ce2.neg
         ∧ ~trns_is_empty ce2) ∨ trns_is_empty ce2)
         ∧ MEM_SUBSET ce1.sucs ce2.sucs
         ∧ MEM_SUBSET (get_acc_set acc ce2) (get_acc_set acc ce1)`
         by metis_tac[tlg_concr_def]
       >> fs[tr_less_general_def]
       >> qexists_tac `e1_lab` >> qexists_tac `e1_sucs`
       >> qexists_tac `e2_lab` >> qexists_tac `e2_sucs` >> fs[]
       >> `e1_sucs ⊆ e2_sucs` by (
             Cases_on `ce1` >> Cases_on `ce2` >> fs[concr2AbstractEdge_def]
             >> rw[] >> fs[MEM_SUBSET_SET_TO_LIST]
       )
       >> `∀T'.
           (∃f.
             (T' = acc_cond (concr2AbstrAA (concrAA g_AA init aP)) f)
             ∧ MEM f (MAP FST acc)) ⇒
                ((qs,concr2AbstractEdge (set aP) ce2) ∈ T' ⇒
                (qs,concr2AbstractEdge (set aP) ce1) ∈ T')` by (
           fs[] >> rpt strip_tac
           >> `is_until f ∧ MEM f (graphStates g_AA)` by (
              fs[valid_acc_def,MEM_MAP]
              >> Cases_on `y` >> fs[]
              >> `?id nL. findNode (λ(i,l). l.frml = f) g_AA = SOME (id,nL)
                  ∧ is_until f` by metis_tac[FST]
              >> rw[] >> fs[findNode_def]
              >> `MEM (id,nL) (toAList g_AA.nodeInfo)
                  ∧ (λ(i,l). l.frml = f) (id,nL)` by metis_tac[FIND_LEMM2]
              >> fs[] >> simp[graphStates_def,MEM_MAP] >> qexists_tac `(id,nL)`
              >> fs[]
           )
           >> `(MEM f (get_acc_set acc ce1) ⇔
                    (qs,FST (e1_lab,e1_sucs),SND (e1_lab,e1_sucs)) ∈
                       acc_cond abstrAA f)` by metis_tac[CONCR_ACC_SETS]
           >> `MEM f (get_acc_set acc ce2)` by (
                simp[get_acc_set_def,CAT_OPTIONS_MEM,MEM_MAP]
                >> fs[MEM_MAP] >> qexists_tac `y` >> fs[] >> Cases_on `y`
                >> fs[] >> simp[acc_cond_concr_def] >> rw[]
                >> Cases_on `MEM f ce2.sucs` >> fs[]
                >> fs[acc_cond_def]
                >- (Cases_on `ce2` >> fs[concr2AbstractEdge_def] >> rw[]
                    >> metis_tac[]
                   )
                >- (simp[EXISTS_MEM]
                    >> `trns_is_empty ce2 \/
                        ~(transformLabel (set aP) ce2.pos ce2.neg = {})`
                       by metis_tac[TRNS_IS_EMPTY_LEMM,MEM_SUBSET_SET_TO_LIST]
                    >> Cases_on `ce2`
                    >> fs[concr2AbstractEdge_def] >> rw[]
                    >> fs[valid_acc_def] >> rename[`MEM (f,f_trns) acc`]
                    >> `∃id nL.
                         (findNode (λ(i,l). l.frml = f) g_AA = SOME (id,nL))
                         ∧ (SOME f_trns  = concr_extrTrans g_AA id)
                         ∧ (∀ce.
                             MEM ce f_trns ⇒
                             (set ce.pos ⊆ set aP) ∧ (set ce.neg ⊆ set aP))`
                         by metis_tac[]
                    >> rw[] >> fs[concr2AbstrAA_def] >> rw[]
                    >> `∃n cT.
                         (concr_extrTrans g_AA id = SOME cT)
                         ∧ (lookup id g_AA.nodeInfo = SOME n)
                         ∧ (set (MAP (concr2AbstractEdge (set aP)) cT) =
                             concrTrans g_AA (set aP) n.frml)` by (
                        `?flws. lookup id g_AA.followers = SOME flws` by (
                            fs[findNode_def]
                            >> `MEM (id,nL) (toAList g_AA.nodeInfo)`
                               by metis_tac[FIND_LEMM2]
                            >> fs[wfg_def]
                            >> metis_tac[MEM_toAList,domain_lookup]
                        )
                        >> IMP_RES_TAC CONCR_EXTRTRANS_LEMM
                        >> first_x_assum (qspec_then `id` mp_tac) >> simp[]
                     )
                    >> `(lookup id g_AA.nodeInfo = SOME nL)
                         ∧ (f = n.frml)` by (
                         fs[findNode_def]
                         >> `n = nL ∧ (λ(i,l). l.frml = f) (id,nL)`
                             by metis_tac[FIND_LEMM2,MEM_toAList,SOME_11]
                         >> fs[]
                     )
                    >> `cT = f_trns` by metis_tac[SOME_11] >> rw[]
                    >> rename[`(ce_lab,ce_sucs) ∈ concrTrans _ _ _`]
                    >> `MEM (ce_lab,ce_sucs)
                              (MAP (concr2AbstractEdge (set aP)) cT)`
                       by fs[]
                    >> fs[MEM_MAP] >> rename[`MEM ce cT`] >> rw[]
                    >> `MEM_SUBSET ce.pos aP ∧ MEM_SUBSET ce.neg aP`
                       by metis_tac[]
                    >> qexists_tac `ce` >> Cases_on `ce`
                    >> fs[concrEdge_component_equality,concr2AbstractEdge_def]
                    >> rename[`MEM (concrEdge ce_pos ce_neg ce_sucs) cT`]
                    >> `MEM_SUBSET ce_sucs l1` by fs[MEM_SUBSET_SET_TO_LIST]
                    >> fs[]
                    >> `∀x. ((MEM x ce_pos) ∨ (MEM x l)
                           ∨ (MEM x ce_neg) ∨ (MEM x l0))
                          ⇒ MEM x aP` suffices_by (
                         strip_tac >> IMP_RES_TAC TRANSFORMLABEL_SUBSET2
                         >> metis_tac[]
                     )
                    >> rpt strip_tac
                    >> metis_tac[MEM_SUBSET_SET_TO_LIST,SUBSET_DEF]
                   )
              )
              >> `MEM f (get_acc_set acc ce1)`
                 by metis_tac[MEM_SUBSET_SET_TO_LIST,SUBSET_DEF]
              >> fs[] >> rw[] >> metis_tac[]
           )
       >> fs[]
       >- (Cases_on `ce1` >> Cases_on `ce2` >> fs[concr2AbstractEdge_def]
           >> metis_tac[TRANSFORMLABEL_SUBSET]
           )
       >- (`e2_lab = {}` by (
              `transformLabel (set aP) ce2.pos ce2.neg = {}`
                by metis_tac[TRNS_IS_EMPTY_LEMM,MEM_SUBSET_SET_TO_LIST]
              >> Cases_on `ce2` >> fs[concr2AbstractEdge_def] >> rw[]
            )
            >> fs[]
          )
      )
  );

val possibleGBA_states_def = Define`
  possibleGBA_states g_AA =
     {set qs | !q. MEM q qs ==> MEM q (graphStates g_AA) ∧ ALL_DISTINCT qs }`;

val decr_expGBA_rel_def = Define `
  decr_expGBA_rel (g_AA1,acc1,ids1,G1) (g_AA2,acc2,ids2,G2) =
     let m =
      λg. {set x | inGBA g x } ∩ possibleGBA_states g_AA1
     in
      (g_AA1 = g_AA2)
    ∧ (NoNodeProcessedTwice
          (possibleGBA_states g_AA1) m (G1,ids1) (G2,ids2))`;

val DECR_EXPGBA_REL_WF = store_thm
  ("DECR_EXPGBA_REL_WF",
   ``WF decr_expGBA_rel``,
   qabbrev_tac `
      lifted_NNPT =
         λB:((α ltl_frml -> bool) -> bool)
          (j:(α nodeLabelAA, β) gfg,
           k:γ,
           l:δ list,
           m:(α nodeLabelGBA, ε) gfg)
          (j2:(α nodeLabelAA, β) gfg,
           k2:γ,
           l2:δ list,
           m2:(α nodeLabelGBA, ε) gfg).
            NoNodeProcessedTwice
                 B
                 (λg. {set x | inGBA g x } ∩ B)
                 (m,l) (m2,l2)`
   >> `!B. FINITE B ==> WF (lifted_NNPT B)` by (
        rpt strip_tac
        >> `lifted_NNPT B =
             inv_image
              (NoNodeProcessedTwice B (λg.{set x | inGBA g x} ∩ B))
              (λ(m,n,k,l). (l,k))` by (
          Q.HO_MATCH_ABBREV_TAC `Q = P`
          >> `!x1 x2. Q x1 x2 = P x1 x2` suffices_by metis_tac[]
          >> rpt strip_tac >> qunabbrev_tac `Q` >> qunabbrev_tac `P`
          >> fs[inv_image_def] >> qunabbrev_tac `lifted_NNPT`
          >> Cases_on `x1` >> Cases_on `x2` >> Cases_on `r` >> Cases_on `r'`
          >> Cases_on `r` >> Cases_on `r''` >> fs[EQ_IMP_THM]
        ) >> rw[]
        >> metis_tac[WF_inv_image,NNPT_WF]
   )
   >> IMP_RES_TAC WF_LEMM
   >> first_x_assum (qspec_then `λ(m,n,j,k). possibleGBA_states m` mp_tac)
   >> Q.HO_MATCH_ABBREV_TAC `(A ==> WF B) ==> WF C`
   >> `A` by (
       qunabbrev_tac `A`
       >> rpt strip_tac >> Cases_on `k` >> Cases_on `r` >> Cases_on `r'` >> fs[]
       >> simp[possibleGBA_states_def]
       >> `{set qs | ∀q'. MEM q' qs ⇒ MEM q' (graphStates q) ∧ ALL_DISTINCT qs} =
            {set qs | MEM_SUBSET qs (graphStates q) ∧ ALL_DISTINCT qs}` by (
           simp[SET_EQ_SUBSET,SUBSET_DEF,MEM_SUBSET_SET_TO_LIST]
           >> rpt strip_tac >> Cases_on `x` >> fs[ALL_DISTINCT]
           >> qexists_tac `qs` >> fs[] >> Cases_on `qs` >> fs[ALL_DISTINCT]
           >> metis_tac[]
       )
       >> `FINITE (IMAGE
                     set ({qs | MEM_SUBSET qs (graphStates q)
                                           ∧ ALL_DISTINCT qs}))` suffices_by (
           strip_tac >> fs[IMAGE_DEF,MEM_SUBSET_SET_TO_LIST]
       )
       >> rw[] >> metis_tac[SET_OF_SUBLISTS_FINITE,IMAGE_FINITE]
   )
   >> simp[] >> rpt strip_tac
   >> `!x y. C x y ==> B x y` suffices_by metis_tac[WF_SUBSET]
   >> qunabbrev_tac `B` >> qunabbrev_tac `C` >> rpt strip_tac >> fs[]
   >> Cases_on `x` >> Cases_on `y` >> qunabbrev_tac `lifted_NNPT` >> fs[]
   >> Cases_on `r` >> Cases_on `r'` >> fs[] >> Cases_on `r` >> Cases_on `r''`
   >> fs[] >> fs[decr_expGBA_rel_def]
  );

val towards_suff_wfg_def = Define
  `towards_suff_wfg (g_AA1,acc1,ids1,G1) (g_AA2,acc2,ids2,G2) =
      let max_elems = λd. maximal_elements d (rrestrict (rel_to_reln ($<)) d)
      in ((max_elems (domain G1.nodeInfo) =
           max_elems (domain G2.nodeInfo))
       ∧ ((G1.next > G2.next) \/
          (G1.next = G2.next ∧ (LENGTH ids1 < LENGTH ids2))))`

val TWDRS_SUFFWFG_WF = store_thm
  ("TWDRS_SUFFWFG_WF",
  ``let P = λ(g_AA,acc,ids,G). suff_wfg G
    in WF (λx y. ~P x ∧ ~P y ∧ towards_suff_wfg x y)``,
  fs[] >> simp[WF_IFF_WELLFOUNDED,wellfounded_def] >> rpt strip_tac
  >> CCONTR_TAC >> fs[towards_suff_wfg_def]
  >> qabbrev_tac `get_next =
       λ(g_AA :α),(acc :β),(ids :γ list),(G :(δ, ε) gfg).
        G.next`
  >> qabbrev_tac `get_ids =
       λ(g_AA :α),(acc :β),(ids :γ list),(G :(δ, ε) gfg).
        ids`
  >> qabbrev_tac `get_domain =
       λ(g_AA :α),(acc :β),(ids :γ list),(G :(δ, ε) gfg).
        domain G.nodeInfo`
  >> `!k. ?j. k <= j ∧ (get_next (f j) < get_next (f (SUC j)))` by (
      rpt strip_tac
      >> CCONTR_TAC >> fs[]
      >> `!a. k <= a
           ==> LENGTH (get_ids (f (SUC a))) < LENGTH (get_ids (f a))` by (
        rpt strip_tac
        >> first_x_assum (qspec_then `a` mp_tac) >> simp[] >> rpt strip_tac
        >> `towards_suff_wfg (f (SUC a)) (f a)` by fs[]
        >> qunabbrev_tac `get_ids` >> Cases_on `f (SUC a)` >> Cases_on `f a`
        >> fs[] >> Cases_on `r` >> Cases_on `r'` >> fs[]
        >> Cases_on `r` >> Cases_on `r''` >> fs[towards_suff_wfg_def]
        >> qunabbrev_tac `get_next` >> fs[]
      )
      >> `WF (measure (LENGTH o get_ids o f))` by fs[]
      >> POP_ASSUM mp_tac
      >> PURE_REWRITE_TAC[WF_IFF_WELLFOUNDED,wellfounded_def] >> fs[]
      >> qexists_tac `λx. x + k` >> rpt strip_tac >> fs[]
      >> metis_tac[DECIDE ``k <= k + n``,
                   DECIDE ``k + SUC n = SUC (k + n)``]
  )
  >> qabbrev_tac `D = get_domain (f 0)`
  >> qabbrev_tac `max_elems =
        λd. maximal_elements d (rrestrict (rel_to_reln ($<)) d)`
  >> `!a. max_elems (get_domain (f a)) = max_elems D` by (
      Induct_on `a` >> fs[] >> rw[]
      >> `towards_suff_wfg (f (SUC a)) (f a)` by fs[]
      >> qunabbrev_tac `get_domain` >> Cases_on `f (SUC a)` >> Cases_on `f a`
      >> fs[] >> Cases_on `r` >> Cases_on `r'` >> fs[]
      >> Cases_on `r` >> Cases_on `r''` >> fs[towards_suff_wfg_def]
      >> qunabbrev_tac `max_elems` >> fs[]
  )
  >> Cases_on `D = {}`
  >- (
   `¬(λ(g_AA,acc,ids,G). suff_wfg G) (f 0)` by fs[]
   >> Cases_on `f 0` >> fs[] >> Cases_on `r` >> fs[] >> Cases_on `r'` >> fs[]
   >> fs[suff_wfg_def] >> qunabbrev_tac `get_domain` >> fs[]
   >> metis_tac[MEMBER_NOT_EMPTY]
  )
  >- (
   `?x. x ∈ maximal_elements D (rrestrict (rel_to_reln ($<)) D)` by (
       HO_MATCH_MP_TAC finite_strict_linear_order_has_maximal
       >> rpt strip_tac >> qunabbrev_tac `D` >> fs[]
       >- (Cases_on `f 0` >> fs[] >> Cases_on `r` >> fs[] >> Cases_on `r'`
           >> fs[] >> qunabbrev_tac `get_domain`
           >> fs[FINITE_domain]
          )
       >- (simp[strict_linear_order_def,rrestrict_def,rel_to_reln_def]
           >> simp[set_relationTheory.domain_def,range_def,transitive_def,antisym_def]
           >> simp[SUBSET_DEF] >> rpt strip_tac
          )
   )
  >> `!b. ?n. b < get_next (f n)` by (
       `!n. get_next (f n) <= get_next (f (SUC n))` by (
         rpt strip_tac
         >> `towards_suff_wfg (f (SUC n)) (f n)` by fs[]
         >> qunabbrev_tac `get_ids` >> Cases_on `f (SUC n)` >> Cases_on `f n`
         >> fs[] >> Cases_on `r` >> Cases_on `r'` >> fs[]
         >> Cases_on `r` >> Cases_on `r''` >> fs[towards_suff_wfg_def]
         >> qunabbrev_tac `get_next` >> fs[]
       )
       >> Induct_on `b` >> fs[]
       >- (`∃j. get_next (f j) < get_next (f (SUC j))` by metis_tac[]
           >> qexists_tac `SUC j` >> fs[]
          )
       >- (`!a. (n <= a) ==> (get_next (f n) <= get_next (f a))` by (
             Induct_on `a` >> fs[] >> rpt strip_tac >> Cases_on `n = SUC a`
             >> fs[] >> `get_next (f a) <= get_next (f (SUC a))` by fs[]
             >> fs[]
          )
          >> `∃j. n ≤ j ∧ get_next (f j) < get_next (f (SUC j))` by metis_tac[]
          >> qexists_tac `SUC j` >> fs[]
          >> `get_next (f n) <= get_next (f j)` by fs[] >> fs[]
          )
   )
  >> `?n. x < get_next (f n)` by fs[]
  >> `¬(λ(g_AA,acc,ids,G). suff_wfg G) (f n)` by metis_tac[]
  >> `max_elems (get_domain (f n)) = max_elems D` by fs[]
  >> `x ∈ max_elems (get_domain (f n))` by (
       qunabbrev_tac `max_elems` >> fs[]
   )
  >> Cases_on `f n` >> fs[] >> Cases_on `r` >> fs[] >> Cases_on `r'`
  >> fs[suff_wfg_def] >> qunabbrev_tac `get_next` >> fs[]
  >> rw[]
  >> qunabbrev_tac `get_domain` >> qunabbrev_tac `max_elems` >> fs[]
  >> rw[] >> fs[maximal_elements_def] >> rw[] >> fs[] >> rw[]
  >> `n' ∈ domain r.nodeInfo
       ∧ (x,n') ∈ rrestrict (rel_to_reln $<) (domain r.nodeInfo) ⇒
       x = n'` by metis_tac[]
  >> `x = n'` by (
       `(x,n') ∈ rrestrict (rel_to_reln $<) (domain r.nodeInfo)`
         suffices_by metis_tac[]
       >> PURE_REWRITE_TAC[rrestrict_def,rel_to_reln_def] >> simp[]
   )
  >> fs[]
  )
  );

val decr_expGBA_strong_def = Define `
  decr_expGBA_strong (g_AA1,acc1,ids1,G1) (g_AA2,acc2,ids2,G2) =
  ((decr_expGBA_rel (g_AA1,acc1,ids1,G1) (g_AA2,acc2,ids2,G2))
 ∧ (suff_wfg G2 ==> suff_wfg G1))`;

val DECR_EXPGBA_STRONG_WF = store_thm
  ("DECR_EXPGBA_STRONG_WF",
   ``WF decr_expGBA_strong``,
   HO_MATCH_MP_TAC WF_SUBSET
   >> qexists_tac `decr_expGBA_rel` >> rpt strip_tac
   >- metis_tac[DECR_EXPGBA_REL_WF]
   >- (Cases_on `x` >> Cases_on `y` >> Cases_on `r` >> Cases_on `r'`
       >> Cases_on `r` >> Cases_on `r''` >> fs[decr_expGBA_strong_def]
      )
  );

val concr_min_rel_def = Define`
  concr_min_rel (t1,acc1) (t2,acc2) =
           (tlg_concr (t1,acc1) (t2,acc2)
           ∧ ~((MEM_EQUAL t1.pos t2.pos)
                   ∧ (MEM_EQUAL t1.neg t2.neg)
                   ∧ (MEM_EQUAL t1.sucs t2.sucs))
           ∧ ~(trns_is_empty t1 ∧ trns_is_empty t2
             ∧ MEM_EQUAL t1.sucs t2.sucs))`;


val expandGBA_def = tDefine ("expandGBA")
   `(expandGBA g_AA acc [] G = SOME G)
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
                MAP (λcE. (cE,get_acc_set acc cE)) trans_unopt
       in let trans =
              ONLY_MINIMAL
                  concr_min_rel
                  flws_with_acc_sets
       in let new_sucs =
                FILTER (λqs. ~inGBA G qs)
                   (MAP (λ(cE,fs). cE.sucs) trans)
       in let (new_ids, G1) =
              FOLDR (λn (ids,g).
                        if inGBA g n
                        then (ids,g)
                        else ((g.next::ids),addNodeToGBA g n))
                      ([],G) new_sucs
       in do G2 <-
              FOLDR
                (λ(eL,suc) g_opt. do g <- g_opt ;
                                     addEdgeToGBA g id eL suc
                                  od)
                (SOME G1)
                (MAP (λ(cE,f). (edgeLabelGBA cE.pos cE.neg f,cE.sucs)) trans) ;
             expandGBA g_AA acc (nub (ids ++ new_ids)) G2
          od
   )`
   (qabbrev_tac `P = λ(g_AA:(α nodeLabelAA, α edgeLabelAA) gfg,
                       acc:(α ltl_frml, α concrEdge list) alist,
                       ids:num list,
                       G:(α nodeLabelGBA, α edgeLabelGBA) gfg). suff_wfg G`
   >> WF_REL_TAC `λx y. (~P y ∧ ~P x ==> towards_suff_wfg x y)
                      ∧ (P y ==> decr_expGBA_strong x y)`
   >- (HO_MATCH_MP_TAC P_DIVIDED_WF_LEMM >> rpt strip_tac
       >- metis_tac[TWDRS_SUFFWFG_WF]
       >- metis_tac[DECR_EXPGBA_STRONG_WF]
       >- (Cases_on `x` >> Cases_on `y` >> Cases_on `r` >> Cases_on `r'`
           >> Cases_on `r` >> Cases_on `r''`
           >> rename[`P (g_AA1,acc1,ids1,G1)`]
           >> rename[`decr_expGBA_strong _ (g_AA2,acc2,ids2,G2)`]
           >> qunabbrev_tac `P` >> fs[decr_expGBA_strong_def,suff_wfg_def]
          )
      )
   >- (rpt strip_tac >> fs[]
       >> simp[decr_expGBA_rel_def,NoNodeProcessedTwice_def] >> fs[]
       >> qabbrev_tac `t =
           gba_trans_concr
              (CAT_OPTIONS
                   (MAP (concr_extrTrans g_AA)
                        (CAT_OPTIONS
                             (MAP
                                  (λf.
                                       OPTION_MAP FST
                                       (findNode (λ(i,l). l.frml = f)
                                                 g_AA))
                                  current_node.frmls))))`
      >> qabbrev_tac `t_with_acc = MAP (λcE. (cE,get_acc_set acc cE)) t`
       >> `!l n_G.
             (FOLDR
              (λ(eL,suc) g_opt. do g <- g_opt; addEdgeToGBA g id eL suc od)
              (SOME G1) l = SOME n_G)
             ==> ((G1.nodeInfo = n_G.nodeInfo) ∧ (G1.next = n_G.next))` by (
            Induct_on `l` >> fs[] >> rpt strip_tac >> fs[]
            >> Cases_on `h` >> fs[]
            >> `G1.nodeInfo = g.nodeInfo ∧ G1.next = g.next` by metis_tac[]
            >> fs[addEdgeToGBA_def]
            >> Cases_on `findNode (λ(i,q). MEM_EQUAL q.frmls r) g` >> fs[]
            >> Cases_on `x` >> fs[]
            >- metis_tac[addEdge_preserves_nodeInfo]
            >- (fs[addEdge_def] >> rw[])
        )
      >> `!l n_ids n_G.
              (n_ids,n_G) =
                 FOLDR (λn (ids,g).
                           if inGBA g n then (ids,g)
                           else (g.next::ids,addNodeToGBA g n)) ([],G) l
              ==> ((!n. n ∈ domain n_G.nodeInfo
                       ==> ((n ∈ domain G.nodeInfo) \/ n < n_G.next))
                ∧ (!n. n ∈ domain G.nodeInfo ==> n ∈ domain n_G.nodeInfo)
                ∧ (G.next <= n_G.next)
                ∧ ((G.next = n_G.next)
                       ==> ((G.nodeInfo = n_G.nodeInfo)
                          ∧ (n_ids = []))))` by (
           Induct_on `l` >> fs[] >> rpt strip_tac
           >> Cases_on `(FOLDR (λn (ids,g).
                                   if inGBA g n then (ids,g)
                                   else (g.next::ids,addNodeToGBA g n)) ([],G) l)`
           >> fs[] >> Cases_on `inGBA r h` >> fs[] >> rw[]
           >> fs[addNodeToGBA_def] >> fs[addNode_def]
           >> metis_tac[DECIDE ``n < r.next ==> n < SUC r.next``]
        )
       >- (
        simp[towards_suff_wfg_def] >> qunabbrev_tac `P` >> fs[suff_wfg_def]
        >> strip_tac
        >- (
         `!n. n ∈ domain G2.nodeInfo ==> n ∈ domain G.nodeInfo \/ n < G2.next`
           by metis_tac[]
         >> simp[maximal_elements_def,rrestrict_def,rel_to_reln_def,
                 SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
         >- (fs[] >> `x ∈ domain G.nodeInfo \/ x < G2.next` by metis_tac[]
             >> first_x_assum (qspec_then `n'` mp_tac) >> fs[]
            )
         >- (fs[] >> `x ∈ domain G.nodeInfo \/ x < G2.next` by metis_tac[]
             >> fs[]
             >- (Cases_on `x'' ∈ domain G.nodeInfo` >> fs[]
                 >> `x'' ∈ domain G2.nodeInfo` by metis_tac[]
                 >> metis_tac[]
                )
             >- (metis_tac[])
            )
         >- metis_tac[]
         >- (Cases_on `x'' ∈ domain G2.nodeInfo` >> fs[]
             >> `x'' ∈ domain G.nodeInfo \/ x'' < G2.next` by metis_tac[]
             >- (disj1_tac >> fs[] >> metis_tac[])
             >- (`x ∈ domain G2.nodeInfo` by metis_tac[] >> fs[]
                 >> `x'' ∈ domain G.nodeInfo \/ x'' < G2.next` by metis_tac[]
                 >- metis_tac[]
                 >- (`n' ∈ domain G.nodeInfo \/ n' < G2.next` by metis_tac[]
                  >- (`~(x < n')` by metis_tac[]
                      >> fs[])
                  >- fs[]
                    )
                )
            )
        )
        >- (
         `(∀n.
            n ∈ domain G2.nodeInfo ⇒
               n ∈ domain G.nodeInfo ∨ n < G2.next)
        ∧ (∀n. n ∈ domain G.nodeInfo ⇒ n ∈ domain G2.nodeInfo)
        ∧ (G.next ≤ G2.next)
        ∧ ((G.next = G2.next)
               ==> ((G.nodeInfo = G2.nodeInfo)
                   ∧ (new_ids = [])))` by metis_tac[]
         >> Cases_on `G2.next > G.next` >> fs[]
         >> `!(l:num list). LENGTH (nub l) <= LENGTH l` by (
             Induct_on `l` >> fs[nub_def] >> rpt strip_tac
             >> Cases_on `MEM h l` >> fs[]
         )
         >> `G.next = G2.next` by fs[]
         >> `G.nodeInfo = G2.nodeInfo ∧ new_ids = []` by metis_tac[]
         >> rw[] >> fs[]
         >> `LENGTH (nub ids) <= LENGTH ids` by metis_tac[]
         >> rw[]
        )
        )
       >- (
       `!l n_ids n_G.
         (n_ids,n_G) =
           FOLDR (λn (ids,g).
                 if inGBA g n then (ids,g)
                 else (g.next::ids,addNodeToGBA g n)) ([],G) l
             ==> (!x id. lookup id G.nodeInfo = SOME x
                           ==> lookup id n_G.nodeInfo = SOME x)` by (
           Induct_on `l` >> fs[] >> rpt strip_tac
           >> Cases_on `(FOLDR (λn (ids,g).
                           if inGBA g n then (ids,g)
                           else (g.next::ids,addNodeToGBA g n)) ([],G) l)`
           >> fs[] >> Cases_on `inGBA r h` >> fs[] >> rw[]
           >> fs[addNodeToGBA_def] >> fs[addNode_def]
           >> qunabbrev_tac `P` >> fs[suff_wfg_def]
           >> `G.next <= r.next` by metis_tac[]
           >> `lookup id' r.nodeInfo = SOME x` by fs[]
           >> `~(id' = r.next)` by (
               `id' ∈ domain G.nodeInfo` by metis_tac[domain_lookup]
               >> `~(G.next <= id')` by metis_tac[]
               >> fs[]
           )
           >> metis_tac[lookup_insert]
       )
        >> simp[decr_expGBA_strong_def,decr_expGBA_rel_def]
        >> simp[NoNodeProcessedTwice_def] >> qunabbrev_tac `P` >> fs[]
        >> Q.HO_MATCH_ABBREV_TAC
            `((M G2 ⊂ M G) \/ (M G2 = M G ∧ EQ_LENGTH)) ∧ suff_wfg G2`
        >> `M G2 ⊆ M G` by (
            qunabbrev_tac `M` >> fs[]
            >> `{x | inGBA G x} ⊆ {x | inGBA G2 x}` suffices_by (
                simp[SUBSET_DEF] >> rpt strip_tac >> fs[]
                >> metis_tac[]
            )
            >> simp[SUBSET_DEF] >> rpt strip_tac >> fs[inGBA_def]
            >> fs[EXISTS_MEM,MEM_MAP] >> Cases_on `y` >> fs[] >> rw[]
            >> rename[`MEM (id,n) (toAList G.nodeInfo)`]
            >> `lookup id G2.nodeInfo = SOME n` by metis_tac[MEM_toAList]
            >> qexists_tac `n` >> fs[] >> qexists_tac `(id,n)` >> fs[MEM_toAList]
       )
        >> `suff_wfg G2` by (
           `suff_wfg (SND (new_ids,G1))` by metis_tac[ADDNODE_GBA_FOLDR]
           >> `G1.nodeInfo = G2.nodeInfo ∧ G1.next = G2.next` by metis_tac[]
           >> fs[suff_wfg_def]
       )
        >> Cases_on `M G2 = M G` >> fs[PSUBSET_DEF]
        >> qabbrev_tac `QS =
               FILTER (λqs. ¬inGBA G qs)
                  (MAP (λ(cE,fs). cE.sucs)
                    (ONLY_MINIMAL concr_min_rel t_with_acc))`
        >> `suff_wfg (SND (new_ids,G1))
               ∧ {set x | inGBA (SND (new_ids,G1)) x} =
                   {set x | inGBA G x} ∪ set (MAP set QS)`
             by metis_tac[ADDNODE_GBA_FOLDR]
        >> fs[]
        >> `{set x | inGBA G1 x} = {set x | inGBA G2 x}` by (
               `G1.nodeInfo = G2.nodeInfo` by metis_tac[]
               >> PURE_REWRITE_TAC[inGBA_def] >> metis_tac[]
           )
        >> `!x. MEM x QS ==> (set x ∈ possibleGBA_states g_AA)` by (
           rpt strip_tac >> qunabbrev_tac `QS` >> fs[MEM_FILTER,MEM_MAP]
           >> `MEM y t_with_acc` by metis_tac[ONLY_MINIMAL_SUBSET,
                                              MEM_SUBSET_SET_TO_LIST,SUBSET_DEF]
           >> rename[`MEM ce_with_acc t_with_acc`] >> Cases_on `ce_with_acc`
           >> fs[]
           >> `MEM q t` by (qunabbrev_tac `t_with_acc` >> fs[MEM_MAP])
           >> qunabbrev_tac `t`
           >> qabbrev_tac `c_trns =
                   CAT_OPTIONS
                      (MAP (concr_extrTrans g_AA)
                          (CAT_OPTIONS
                               (MAP
                                    (λf.
                                         OPTION_MAP FST
                                         (findNode (λ(i,l). l.frml = f) g_AA))
                                    current_node.frmls)))`
           >> `!x. MEM x q.sucs
                 ==> ?l ce. MEM l c_trns ∧ MEM ce l ∧ MEM x ce.sucs` by (
               rpt strip_tac >> metis_tac[GBA_TRANS_LEMM3]
           )
           >> simp[possibleGBA_states_def] >> qexists_tac `q.sucs` >> fs[]
           >> strip_tac >> strip_tac
           >> first_x_assum (qspec_then `q'` mp_tac) >> simp[] >> strip_tac
           >> qunabbrev_tac `c_trns` >> fs[CAT_OPTIONS_MEM,MEM_MAP]
           >> strip_tac
           >- metis_tac[CONCR_EXTRTRANS_NODES]
           >- metis_tac[GBA_TRANS_LEMM1]
       )
        >> `!x. MEM x QS ==> set x ∈ {set x | inGBA G x}` by (
           qabbrev_tac `PS = possibleGBA_states g_AA`
           >> qunabbrev_tac `M` >> fs[] >> rw[]
           >> fs[DIFF_INTER2,DIFF_UNION] >> qexists_tac `x`
           >> fs[] >> CCONTR_TAC >> `set x ∈ PS` by fs[]
           >> `~(set x ∈ (PS DIFF {set x | inGBA G x} DIFF set (MAP set QS)))`
              by (
               simp[IN_DIFF,MEM_MAP] >> rpt strip_tac
               >> disj2_tac >> metis_tac[]
           )
           >> `set x ∈ PS DIFF {set x | inGBA G x}` by (
               simp[IN_DIFF] >> rpt strip_tac >> Cases_on `set x = set x'`
               >> fs[] >> metis_tac[IN_GBA_MEM_EQUAL,MEM_EQUAL_SET]
           )
           >> metis_tac[SET_EQ_SUBSET,SUBSET_DEF]
       )
        >> `QS = []` by (
           `set QS = {}` suffices_by fs[]
           >> `!x. ~MEM x QS` suffices_by metis_tac[MEM,MEMBER_NOT_EMPTY]
           >> rpt strip_tac >> `set x ∈ {set x | inGBA G x}` by fs[]
           >> qunabbrev_tac `QS` >> fs[MEM_FILTER]
           >> `MEM_EQUAL x' x` by fs[MEM_EQUAL_SET]
           >> metis_tac[IN_GBA_MEM_EQUAL]
       )
        >> rw[] >> `new_ids = []` by fs[]
        >> qunabbrev_tac `EQ_LENGTH` >> fs[]
        >> `!(l:num list). LENGTH (nub l) <= LENGTH l` by (
           Induct_on `l` >> fs[nub_def] >> rpt strip_tac
                     >> Cases_on `MEM h l` >> fs[]
       )
        >> `LENGTH (nub ids) <= (LENGTH ids)` by metis_tac[]
        >> rw[]
        )
      )
   );

val expandGBA_init_def = Define`
  expandGBA_init (concrAA g_AA initAA props) =
    let initNodes = MAP (λi_list.
                          let suc_nLabels = MAP (λi. lookup i g_AA.nodeInfo)
                                                (nub i_list)
                          in MAP (λl. l.frml) (CAT_OPTIONS suc_nLabels)
                        ) initAA
    in let G0 = FOLDR (λn g. addNodeToGBA g n) empty initNodes
    in let initIds = MAP FST (toAList G0.nodeInfo)
    in let acc_sets =
           FOLDR (λ(id,x) sF.
                   case (is_until x, concr_extrTrans g_AA id) of
                     | (T,SOME c_t) => (x,c_t)::sF
                     | _ => sF
                 )
           [] (graphStatesWithId g_AA)
    in let o_graph = expandGBA g_AA acc_sets initIds G0
    in case o_graph of
         | SOME graph => SOME (concrGBA graph initIds (MAP FST acc_sets) props)
         | NONE => NONE `;


val EXPGBA_SOME_WFG = store_thm
  ("EXPGBA_SOME_WFG",
   ``!g_AA acc ids G.
        wfg G
        ∧ (!i. MEM i ids ==> i ∈ (domain G.nodeInfo))
        ==> (?gba. (expandGBA g_AA acc ids G = SOME gba)
              ∧ wfg gba
              ∧ (!i. i ∈ domain G.nodeInfo
                     ==> lookup i G.nodeInfo = lookup i gba.nodeInfo
                )
              ∧ (frml_ad G ==> frml_ad gba))``,
   HO_MATCH_MP_TAC (theorem "expandGBA_ind")
   >> rpt strip_tac >> fs[expandGBA_def]
   >> Q.HO_MATCH_ABBREV_TAC
      `?gba. ((case lookup id G.nodeInfo of
          | NONE => NONE
          | SOME current_node =>
            (λ(new_ids,G1).
              do G2 <- FOLDR ADDE (SOME G1) (MAP toEL (TRNS current_node)) ;
                 expandGBA g_AA acc (nub (ids ++ new_ids)) G2
              od)
             (FOLDR ADDN ([],G)
                 (FILTER (λqs. ~inGBA G qs)
                    (MAP (λ(cE,fs). cE.sucs) (TRNS current_node))))) = SOME gba)
          ∧ wfg gba
          ∧ (∀i.
             i ∈ domain G.nodeInfo
             ⇒ (lookup i G.nodeInfo = lookup i gba.nodeInfo))
          ∧ (frml_ad G ==> frml_ad gba)`
    >> fs[]
    >> `?node. lookup id G.nodeInfo = SOME node` by metis_tac[domain_lookup]
    >> Cases_on `lookup id G.nodeInfo` >> fs[]
    >> Cases_on
         `FOLDR ADDN ([],G)
          (FILTER (λqs. ¬inGBA G qs)
             (MAP (λ(cE,fs). cE.sucs) (TRNS node)))`
    >> rename[`_ = (new_ids,addedNodesGBA)`]
    >> fs[]
    >> qabbrev_tac `NEW_NODES =
                      FILTER (λqs. ¬inGBA G qs)
                              (MAP (λ(cE,fs). cE.sucs) (TRNS node))`
    >> `wfg addedNodesGBA` by (
        `addedNodesGBA = SND (new_ids,addedNodesGBA)` by fs[]
        >> qunabbrev_tac `ADDN`
        >> metis_tac[ADDNODE_GBA_WFG_FOLDR]
   )
    >> `{set x | inGBA addedNodesGBA x} =
           {set x | inGBA G x} ∪ set (MAP set NEW_NODES)` by (
       `suff_wfg G` by metis_tac[WF_IMP_SUFFWFG]
       >> `addedNodesGBA = SND (new_ids,addedNodesGBA)` by fs[]
       >> qunabbrev_tac `ADDN` >> metis_tac[ADDNODE_GBA_FOLDR]
   )
    >> `set new_ids ∪ domain G.nodeInfo =
            domain addedNodesGBA.nodeInfo` by (
        `addedNodesGBA = SND (new_ids,addedNodesGBA)` by fs[]
        >> `new_ids = FST (new_ids,addedNodesGBA)` by fs[]
        >> qunabbrev_tac `ADDN`
        >> metis_tac[ADDNODE_GBA_DOM_FOLDR,SUBSET_DEF,IN_UNION]
   )
    >> `!ls. (!suc. MEM suc (MAP SND ls) ==> inGBA addedNodesGBA suc)
          ==> (?G2. (FOLDR ADDE (SOME addedNodesGBA) ls = SOME G2)
                ∧ (addedNodesGBA.nodeInfo = G2.nodeInfo) ∧ wfg G2)` by (
       qunabbrev_tac `ADDE` >> rpt strip_tac
       >> HO_MATCH_MP_TAC ADDEDGE_GBA_FOLDR_LEMM >> fs[]
       >> `addedNodesGBA = SND (new_ids,addedNodesGBA)` by fs[]
       >> qunabbrev_tac `ADDN`
       >> metis_tac[ADDNODE_GBA_DOM_FOLDR,SUBSET_DEF,IN_UNION]
   )
   >> first_x_assum (qspec_then `MAP toEL (TRNS node)` mp_tac) >> fs[]
   >> `∀suc.
         MEM suc (MAP SND (MAP toEL (TRNS node))) ⇒
         inGBA addedNodesGBA suc` by (
       rpt strip_tac >> fs[MEM_MAP]
       >> rename[`MEM trns_cel (TRNS node)`,`trns_el = toEL trns_cel` ]
       >> fs[]
       >> `(MEM (FST trns_cel).sucs NEW_NODES)
            \/ (inGBA G (FST trns_cel).sucs)` by (
           qunabbrev_tac `NEW_NODES` >> fs[MEM_FILTER]
           >> Cases_on `inGBA G (FST trns_cel).sucs` >> fs[]
           >> simp[MEM_MAP] >> Cases_on `trns_cel` >> fs[]
           >> qexists_tac `(q,r)` >> fs[]
       )
       >- (
        qunabbrev_tac `toEL` >> Cases_on `trns_cel` >> fs[]
        >> `MEM (set q.sucs) (MAP set NEW_NODES)` by (
            fs[MEM_MAP] >> metis_tac[]
        )
        >> `set (q.sucs) ∈ {set x | inGBA addedNodesGBA x}` by (
            metis_tac[IN_UNION]
        )
        >> fs[] >> metis_tac[IN_GBA_MEM_EQUAL,MEM_EQUAL_SET]
       )
       >- (
        qunabbrev_tac `toEL` >> Cases_on `trns_cel` >> fs[]
        >> `set q.sucs ∈ {set x | inGBA addedNodesGBA x}` by (
           `set q.sucs ∈ {set x | inGBA G x}` by (fs[] >> metis_tac[])
           >> metis_tac[IN_UNION]
        )
        >> fs[]
        >> metis_tac[IN_GBA_MEM_EQUAL,MEM_EQUAL_SET]
       )
   )
   >> fs[] >> rpt strip_tac >> first_x_assum (qspec_then `G2` mp_tac) >> fs[]
   >> `∀i. MEM i ids ∨ MEM i new_ids ⇒ i ∈ domain G2.nodeInfo` by (
       rpt strip_tac >> fs[]
       >- metis_tac[IN_UNION]
       >- metis_tac[IN_UNION,MEM]
   )
   >> fs[] >> rpt strip_tac
   >> `∃gba. expandGBA g_AA acc (nub (ids ⧺ new_ids)) G2 = SOME gba
       ∧ wfg gba
       ∧ (∀i.
           i ∈ domain G2.nodeInfo ⇒
           lookup i G2.nodeInfo = lookup i gba.nodeInfo)
       ∧ (frml_ad G2 ==> frml_ad gba)`
       by metis_tac[]
   >> qexists_tac `gba` >> fs[] >> rpt strip_tac
   >- (`i ∈ domain G2.nodeInfo` by metis_tac[UNION_SUBSET,SUBSET_DEF]
       >> `lookup i addedNodesGBA.nodeInfo = lookup i G.nodeInfo`
          suffices_by metis_tac[]
       >> `suff_wfg G` by metis_tac[WF_IMP_SUFFWFG]
       >> IMP_RES_TAC ADDNODE_GBA_FOLDR
       >> first_x_assum (qspec_then `NEW_NODES` mp_tac) >> simp[]
      )
   >- (`frml_ad G2` suffices_by metis_tac[]
       >> `(∀n. MEM n NEW_NODES ⇒ ALL_DISTINCT n)` suffices_by (
          `suff_wfg G` by metis_tac[WF_IMP_SUFFWFG]
          >> IMP_RES_TAC ADDNODE_GBA_FOLDR
          >> first_x_assum (qspec_then `NEW_NODES` mp_tac) >> simp[]
          >> rpt strip_tac
          >> metis_tac[FRML_AD_NODEINFO]
       )
       >> rpt strip_tac >> qunabbrev_tac `NEW_NODES` >> fs[MEM_FILTER,MEM_MAP]
       >> rename[`MEM t (TRNS node)`] >> Cases_on `t` >> fs[]
       >> `?s. MEM q (gba_trans_concr s)` by (
             qunabbrev_tac `TRNS` >> fs[ONLY_MINIMAL_MEM,MEM_MAP]
             >> metis_tac[]
       )
       >> metis_tac[GBA_TRANS_LEMM1]
      )
  );

val trns_correct_def = Define `
  trns_correct l abstrAA gba aP =
       (!id nL fls.
            (lookup id gba.nodeInfo = SOME nL)
            ∧ (lookup id gba.followers = SOME fls)
            ∧ (set nL.frmls ∈ POW abstrAA.states)
            ∧ ~(MEM id l)
            ==>
            (set (CAT_OPTIONS
                  (MAP
                       (λ(eL,i).
                         do
                         s_nL <- lookup i gba.nodeInfo;
                        SOME
                            (transformLabel aP eL.pos_lab eL.neg_lab,
                             set s_nL.frmls)
                            od) fls)) =
             (gba_trans abstrAA (set nL.frmls)))
       )`;

val final_correct_def = Define `
 final_correct (abstrAA:(α -> bool, α ltl_frml) ALTER_A) gba acc =
  (!id fls nL eL s_id s_nL.
       (lookup id gba.nodeInfo = SOME nL)
       ∧ (lookup id gba.followers = SOME fls)
       ∧ (MEM (eL,s_id) fls)
       ∧ (lookup s_id gba.nodeInfo = SOME s_nL)
       ∧ (set nL.frmls ∈ POW abstrAA.states)
       ==> (!u. MEM u eL.acc_set
                 = MEM u (get_acc_set acc
                           (concrEdge eL.pos_lab
                                      eL.neg_lab
                                      s_nL.frmls)))
  )`;

val aP_correct_def = Define `
  aP_correct (abstrAA:(α -> bool, α ltl_frml) ALTER_A) gba aP =
   (!id fls nL eL s_id.
       (lookup id gba.nodeInfo = SOME nL)
       ∧ (lookup id gba.followers = SOME fls)
       ∧ (MEM (eL,s_id) fls)
       ∧ (set nL.frmls ∈ POW abstrAA.states)
       ==> ((MEM_SUBSET eL.pos_lab aP)
          ∧ (MEM_SUBSET eL.neg_lab aP))
   )`;

val EXPGBA_GRAPH_REACHABLE = store_thm
  ("EXPGBA_GRAPH_REACHABLE",
   ``!abstrAA f init aP g_AA acc ids g g2.
      (abstrAA = concr2AbstrAA (concrAA g_AA init aP))
      ∧ (abstrAA = removeStatesSimpl (ltl2vwaa f))
      ∧ (wfg g_AA)
      ∧ (until_iff_final g_AA)
      ∧ (!id cT. (concr_extrTrans g_AA id = SOME cT)
              ==> (!ce. MEM ce cT
                        ==> (MEM_SUBSET ce.pos aP ∧ MEM_SUBSET ce.neg aP))
        )
      ∧ (valid_acc aP g_AA acc)
      ∧ (unique_node_formula g_AA) ∧ (flws_sorted g_AA)
      ∧ (!x. inGBA g x
              ==> set x ∈ reachableFromSetGBA
                       (vwaa2gba abstrAA) (vwaa2gba abstrAA).initial)
       ∧ (!i. MEM i ids ==> i ∈ domain g.nodeInfo)
       ∧ (expandGBA g_AA acc ids g = SOME g2)
       ∧ (wfg g)
       ∧ (!x. inGBA g x ==> (set x ∈ POW abstrAA.states))
       ∧ frml_ad g
       ==> ((!x. inGBA g2 x
                ==> ((set x ∈ reachableFromSetGBA (vwaa2gba abstrAA)
                        (vwaa2gba abstrAA).initial)
                         ∧ (set x ∈ (vwaa2gba abstrAA).states)))
                )``,
    gen_tac >> gen_tac >> gen_tac >> gen_tac
    >> HO_MATCH_MP_TAC (theorem "expandGBA_ind") >> strip_tac
    >- (fs[] >> rpt strip_tac >> fs[expandGBA_def]
        >> first_x_assum (qspec_then `x` mp_tac) >> simp[] >> rpt strip_tac
        >> `isVeryWeakAlterA (concr2AbstrAA (concrAA g_AA init aP))`
           by metis_tac[REDUCE_STATE_IS_WEAK, LTL2WAA_ISWEAK,
                        LTL2WAA_ISVALID]
        >> fs[vwaa2gba_def] >> first_x_assum (qspec_then `x` mp_tac) >> simp[]
        >> metis_tac[]
       )
    >- (strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac
        >> strip_tac >> strip_tac >> strip_tac >> strip_tac
        >> strip_tac
        >> fs[]
        >> `?node. lookup id g.nodeInfo = SOME node` by metis_tac[domain_lookup]
        >> first_x_assum (qspec_then `node` mp_tac) >> simp[]
        >> strip_tac
        >> qabbrev_tac `TRNS =
             ONLY_MINIMAL
                 concr_min_rel
                 (MAP (λcE. (cE,get_acc_set acc cE))
                    (gba_trans_concr
                        (CAT_OPTIONS
                            (MAP (concr_extrTrans g_AA)
                                 (CAT_OPTIONS
                                      (MAP
                                        (λf.
                                           OPTION_MAP FST
                                            (findNode (λ(i,l). l.frml = f)
                                                      g_AA)) node.frmls))))))`
        >> Cases_on `FOLDR
              (λn (ids,g).
                  if inGBA g n then (ids,g)
                  else (g.next::ids,addNodeToGBA g n)) ([],g)
              (FILTER (λqs. ¬inGBA g qs) (MAP (λ(cE,fs). cE.sucs) TRNS))`
        >> fs[] >> rename[`_ = (new_ids,G1)`]
        >> `wfg G1` by (
             `G1 = SND (new_ids,G1)` by fs[]
             >> metis_tac[ADDNODE_GBA_WFG_FOLDR]
         )
        >> qabbrev_tac `NEW_NODES =
             FILTER (λqs. ¬inGBA g qs) (MAP (λ(cE,fs). cE.sucs) TRNS)`
        >> `{set x | inGBA G1 x} =
               {set x | inGBA g x} ∪ set (MAP set NEW_NODES)` by (
             `G1 = SND (new_ids,G1)` by fs[]
             >> metis_tac[ADDNODE_GBA_FOLDR,WF_IMP_SUFFWFG]
         )
        >> `∀x. MEM x (MAP FST TRNS) ⇒ inGBA G1 x.sucs` by (
             rpt strip_tac >> rename[`MEM qs (MAP FST TRNS)`]
             >> fs[MEM_MAP] >> rename[`MEM t TRNS`] >> Cases_on `t` >> fs[]
             >> rw[]
             >> `(MEM q.sucs NEW_NODES) \/ (inGBA g q.sucs)` by (
                 qunabbrev_tac `NEW_NODES` >> fs[MEM_FILTER]
                 >> Cases_on `inGBA g q.sucs` >> fs[]
                 >> simp[MEM_MAP]
                 >> qexists_tac `(q,r)` >> fs[]
             )
             >- (`MEM ((set q.sucs) ) (MAP set NEW_NODES)`
                  by (fs[MEM_MAP] >> metis_tac[])
                 >> `(set q.sucs) ∈ {set x | inGBA G1 x }`
                    by metis_tac[IN_UNION]
                 >> fs[]
                 >> metis_tac[IN_GBA_MEM_EQUAL,MEM,MEM_EQUAL_SET]
                )
             >- (`(set q.sucs) ∈{set x | inGBA g x}`
                   by (fs[MEM_MAP] >> metis_tac[])
                  >> `(set q.sucs) ∈ {set x | inGBA G1 x}`
                   by metis_tac[IN_UNION]
                  >> fs[] >> metis_tac[IN_GBA_MEM_EQUAL,MEM_EQUAL_SET]
                )
         )
        >> `!x. MEM x
                 (MAP SND (MAP
                        (λ(cE,f). (edgeLabelGBA cE.pos cE.neg f,cE.sucs))
                        TRNS)) ==> inGBA G1 x` by (
             rpt strip_tac >> fs[MEM_MAP] >> rename[`MEM t TRNS`]
             >> Cases_on `t` >> fs[]
             >> `FST (q,r) = q` by fs[] >> metis_tac[]
         )
        >> `(set new_ids ∪ domain g.nodeInfo = domain G1.nodeInfo)
           ∧ g.next ≤ G1.next` by metis_tac[FST,SND,ADDNODE_GBA_DOM_FOLDR]
        >> `∃g2.
             (FOLDR
             (λ(eL,suc) g_opt. do g <- g_opt; addEdgeToGBA g id eL suc od)
             (SOME G1)
             (MAP (λ(cE,f). (edgeLabelGBA cE.pos cE.neg f,cE.sucs)) TRNS) =
              SOME g2) ∧ G1.nodeInfo = g2.nodeInfo ∧ wfg g2` by (
             HO_MATCH_MP_TAC ADDEDGE_GBA_FOLDR_LEMM
             >> rpt conj_tac
             >- metis_tac[]
             >- metis_tac[domain_lookup,IN_UNION]
             >- metis_tac[]
         )
        >> rename[`wfg G2`] >> first_x_assum (qspec_then `G2` mp_tac) >> fs[]
        >> `(∀id cT.
              (concr_extrTrans g_AA id = SOME cT) ⇒
              ∀ce. MEM ce cT ⇒ MEM_SUBSET ce.pos aP ∧ MEM_SUBSET ce.neg aP)`
             by (rpt strip_tac >> rw[] >> fs[] >> metis_tac[])
        >> simp[]
        >> Q.HO_MATCH_ABBREV_TAC `(!g2. A g2 ==> B g2) ==> C`
        >> `B g2 ==> C` by metis_tac[]
        >> `A g2` suffices_by fs[] >> qunabbrev_tac `A` >> fs[]
        >> qabbrev_tac `abstr_gba =
             vwaa2gba (concr2AbstrAA (concrAA g_AA init aP))`
        >> `!x. inGBA G1 x = inGBA G2 x` by (
             simp[inGBA_def]
         )
        >> `!x. set x ∈ reachableFromSetGBA abstr_gba {set q | inGBA g q }
                  ==> (set x ∈ reachableFromSetGBA abstr_gba
                                 {set q | inGBA G2 q })` by (
             simp[reachableFromSetGBA_def] >> rpt strip_tac
             >> `set q ∈ {set x | inGBA g x}` by (simp[] >> metis_tac[])
             >> `set q ∈ {set x | inGBA G1 x}` by metis_tac[IN_UNION]
             >> fs[] >> metis_tac[]
         )
        >> `(∀i.
              i ∈ domain g.nodeInfo ⇒
              lookup i g.nodeInfo = lookup i G1.nodeInfo)
          ∧ (∀i.
              MEM i new_ids ⇒
              ∃n.
              lookup i G1.nodeInfo = SOME n ∧ MEM n.frmls NEW_NODES)`
         by metis_tac[WF_IMP_SUFFWFG,ADDNODE_GBA_FOLDR,SND,FST]
         >> `isVeryWeakAlterA abstrAA ∧ isValidAlterA abstrAA
             ∧ (FINITE abstrAA.states)
             ∧ (abstrAA.alphabet = POW (set aP))` by (
             fs[] >> rpt strip_tac
             >- metis_tac[REDUCE_STATE_IS_WEAK,LTL2WAA_ISWEAK,
                           LTL2WAA_ISVALID]
             >- metis_tac[REDUCE_STATE_IS_VALID,LTL2WAA_ISVALID]
             >- (simp[concr2AbstrAA_def,concr2Abstr_states_def]
                 >> `FINITE {x.frml | ?n. MEM (n,x) (toAList g_AA.nodeInfo)}`
                     suffices_by (
                      Q.HO_MATCH_ABBREV_TAC `FINITE S1 ==> FINITE S2`
                      >> `S1 = S2` suffices_by fs[]
                      >> qunabbrev_tac `S1` >> qunabbrev_tac `S2`
                      >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                      >> metis_tac[MEM_toAList,domain_lookup]
                  )
                 >> `{x.frml | ∃n. MEM (n,x) (toAList g_AA.nodeInfo)} =
                      IMAGE (λ(i,n). n.frml) (set (toAList g_AA.nodeInfo))` by (
                      simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                      >- (qexists_tac `(n,x'')` >> fs[])
                      >- (fs[] >> Cases_on `x''` >> fs[] >> metis_tac[])
                  )
                 >> metis_tac[FINITE_LIST_TO_SET,IMAGE_FINITE]
                )
             >- simp[concr2AbstrAA_def]
         )
        >> `!i x. (MEM i ids ∧ lookup i G2.nodeInfo = SOME x) ==>
             (set x.frmls ∈ reachableFromSetGBA abstr_gba {set q | inGBA g q})`
           by (rpt strip_tac >> `i ∈ domain g.nodeInfo` by fs[]
               >> simp[reachableFromSetGBA_def,reachableFromGBA_def]
               >> `lookup i g.nodeInfo = lookup i G2.nodeInfo` by fs[]
               >> qexists_tac `set (x'.frmls)` >> simp[RTC_REFL]
               >> `inGBA g x'.frmls` by (
                simp[inGBA_def,EXISTS_MEM,MEM_MAP]
                >> qexists_tac `x'` >> fs[MEM_EQUAL_SET]
                >> metis_tac[SND,MEM_toAList]
                )
               >> metis_tac[]
              )
        >> `(∀i x. MEM i new_ids
              ∧ (lookup i G2.nodeInfo = SOME x)
            ⇒ ((set x.frmls ∈ reachableFromSetGBA abstr_gba {set q | inGBA g q})
            ))`
          by (
             rpt gen_tac >> strip_tac
             >> rename[`lookup i G2.nodeInfo = SOME n`]
                >> `MEM n.frmls NEW_NODES` by metis_tac[SOME_11]
                >> qunabbrev_tac `NEW_NODES` >> fs[MEM_FILTER]
                >> qunabbrev_tac `TRNS` >> fs[MEM_MAP,ONLY_MINIMAL_MEM]
                >> qabbrev_tac `TRNS =
                    gba_trans_concr
                      (CAT_OPTIONS
                         (MAP (concr_extrTrans g_AA)
                           (CAT_OPTIONS
                                (MAP
                                     (λf.
                                          OPTION_MAP FST
                                          (findNode (λ(i,l). l.frml = f)
                                                    g_AA)) node.frmls))))`
                >> qabbrev_tac `TO_SUCS =
                                 λ(cE,f).
                                   (edgeLabelGBA cE.pos cE.neg f,cE.sucs)`
                >> qabbrev_tac `W_FINAL = λcE. (cE,get_acc_set acc cE)`
                >> qabbrev_tac `abstr_ce = concr2AbstractEdge (set aP) cE`
                >> `abstr_ce ∈
                      set (MAP (concr2AbstractEdge (set aP)) TRNS)` by (
                     simp[MEM_MAP] >> qunabbrev_tac `abstr_ce` >> fs[]
                      >> metis_tac[]
                 )
                >> qabbrev_tac `ce_lists =
                      CAT_OPTIONS
                       (MAP (concr_extrTrans g_AA)
                         (CAT_OPTIONS
                           (MAP
                             (λf.
                               OPTION_MAP FST
                               (findNode (λ(i,l). l.frml = f) g_AA))
                             node.frmls)))`
                >> qabbrev_tac `zpd = ZIP (node.frmls,ce_lists)`
                >> qabbrev_tac `L =
                      MAP
                       (λf.
                         OPTION_MAP FST
                         (findNode (λ(i,l). l.frml = f) g_AA))
                       node.frmls`
                >> `EVERY IS_SOME L` by (
                       qunabbrev_tac `L` >> fs[] >> simp[EVERY_MEM]
                       >> rpt strip_tac >> fs[MEM_MAP]
                       >> Cases_on `e` >> fs[IS_SOME_DEF]
                       >> `inGBA g node.frmls` by (
                           simp[inGBA_def,EXISTS_MEM] >> qexists_tac `node`
                           >> simp[MEM_MAP,MEM_EQUAL_SET]
                           >> metis_tac[MEM_toAList,SND]
                       )
                       >> `set node.frmls ∈
                            POW (removeStatesSimpl (ltl2vwaa f)).states`
                           by metis_tac[]
                       >> fs[concr2AbstrAA_def]
                       >> `f' ∈ (removeStatesSimpl (ltl2vwaa f)).states`
                          by metis_tac[MEM,IN_POW,SUBSET_DEF]
                       >> `f' ∈ concr2Abstr_states g_AA`
                          by (fs[ALTER_A_component_equality] >> metis_tac[])
                       >> fs[concr2Abstr_states_def,findNode_def]
                       >> rename[`f1 = x1.frml`,`n1 ∈ domain g_AA.nodeInfo`]
                       >> `(λ(i,l). l.frml = f1) (n1,x1)` by fs[]
                       >> metis_tac[FIND_LEMM,NOT_SOME_NONE,MEM_toAList]
                   )
                >> `EVERY IS_SOME
                              (MAP (concr_extrTrans g_AA) (CAT_OPTIONS L))` by (
                       simp[EVERY_MEM] >> rpt strip_tac >> fs[MEM_MAP]
                       >> rename[`MEM some_id (CAT_OPTIONS L)`]
                       >> simp[concr_extrTrans_def]
                       >> Cases_on `lookup some_id g_AA.followers` >> fs[]
                       >-(qunabbrev_tac `L` >> fs[CAT_OPTIONS_MEM,MEM_MAP]
                        >> fs[findNode_def]
                        >> `MEM z (toAList g_AA.nodeInfo)`
                              by metis_tac[FIND_LEMM2]
                        >> Cases_on `z` >> fs[wfg_def]
                        >> rw[]
                        >> metis_tac[MEM_toAList,domain_lookup,wfg_def,
                                     NOT_SOME_NONE]
                         )
                       >- (
                         fs[] >> rpt strip_tac
                         >> Q.HO_MATCH_ABBREV_TAC `IS_SOME H` >> Cases_on `H`
                         >> fs[IS_SOME_DEF]
                         >> `some_id ∈ (domain g_AA.nodeInfo)`
                               by metis_tac[domain_lookup,wfg_def]
                         >> metis_tac[domain_lookup,NOT_SOME_NONE]
                         )
                       )
                >> `LENGTH node.frmls = LENGTH ce_lists` by (
                   qunabbrev_tac `ce_lists`
                   >> qunabbrev_tac `L`
                   >> metis_tac[LENGTH_MAP,CAT_OPTIONS_LENGTH]
                 )
                >> `MAP FST zpd = node.frmls` by (
                     qunabbrev_tac `zpd` >> fs[]
                     >> metis_tac[MAP_ZIP]
                 )
                >> `ALL_DISTINCT (MAP FST zpd)`
                    by metis_tac[frml_ad_def]
                >> `abstr_ce ∈
                    d_conj_set
                     (set (MAP (λ(q,d).
                              (q,set (MAP
                                       (concr2AbstractEdge (set aP)) d))) zpd))
                       (POW (set aP))`
                     by metis_tac[MAP_ZIP,LENGTH_COUNT_LIST,GBA_TRANS_LEMM]
                >> simp[reachableFromSetGBA_def,reachableFromGBA_def,
                        stepGBA_def]
                >> qunabbrev_tac `abstr_gba` >> simp[vwaa2gba_def]
                >> `isVeryWeakAlterA (concr2AbstrAA (concrAA g_AA init aP))`
                      by metis_tac[]
                >> simp[gba_trans_def]
                >> simp[d_gen_def,removeStatesSimpl_def]
                >> qexists_tac `set node.frmls` >> simp[] >> strip_tac
                >- (
                  Q.HO_MATCH_ABBREV_TAC `Q^* (set node.frmls) (set cE.sucs)`
                 >> `Q (set node.frmls) (set cE.sucs)`
                       suffices_by metis_tac[RTC_SUBSET]
                 >> qunabbrev_tac `Q` >> simp[] >> qexists_tac `FST abstr_ce`
                 >> simp[minimal_elements_rrestrict]
                 >> simp[minimal_elements_def]
                 >> `!q_i q_nL q q_trns.
                      (findNode (λ(i,l). l.frml = q) g_AA = SOME (q_i,q_nL))
                      ∧ (q_nL.frml = q) ∧ MEM q node.frmls
                      ∧ concr_extrTrans g_AA q_i = SOME q_trns
                      ==> MEM (q_nL.frml,q_trns) zpd` by (
                        qunabbrev_tac `zpd` >> simp[MEM_ZIP] >> rpt strip_tac
                        >> `?ind_q. EL ind_q node.frmls = q_nL.frml
                                  ∧ ind_q < LENGTH node.frmls`
                           by metis_tac[MEM_EL]
                        >> qexists_tac `ind_q` >> fs[]
                        >> qunabbrev_tac `ce_lists` >> rw[]
                        >> `LENGTH node.frmls =
                             LENGTH (MAP (concr_extrTrans g_AA)
                                         (CAT_OPTIONS L))` by (
                            fs[CAT_OPTIONS_LENGTH]
                        )
                        >> `SOME
                             (EL ind_q (CAT_OPTIONS (MAP (concr_extrTrans g_AA)
                                                        (CAT_OPTIONS L)))) =
                            (EL ind_q (MAP (concr_extrTrans g_AA)
                                          (CAT_OPTIONS L)))` by
                         metis_tac[CAT_OPTIONS_EL]
                        >> `EL ind_q (MAP (concr_extrTrans g_AA)
                                     (CAT_OPTIONS L)) =
                            (concr_extrTrans g_AA (EL ind_q (CAT_OPTIONS L)))`
                            by fs[EL_MAP,LENGTH_MAP]
                        >> `LENGTH L = LENGTH node.frmls` by (
                            qunabbrev_tac `L`
                            >> fs[LENGTH_MAP]
                        )
                        >> `SOME (EL ind_q (CAT_OPTIONS L)) =
                              EL ind_q L` by metis_tac[CAT_OPTIONS_EL]
                        >> `EL ind_q L = SOME q_i` by (
                            qunabbrev_tac `L` >> simp[EL_MAP]
                        )
                        >> rw[] >> `EL ind_q (CAT_OPTIONS L) = q_i` by fs[]
                        >> metis_tac[SOME_11]
                 )
                 >> `{(q,(removeStatesSimpl (ltl2vwaa f)).trans q) |
                         MEM q node.frmls} =
                      set
                       (MAP (λ(q,d).
                              (q,set (MAP (concr2AbstractEdge (set aP)) d)))
                            zpd)` by (
                     simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                      >- (
                       simp[MEM_MAP]
                       >> `?i nL. findNode (λ(i,l). l.frml = q) g_AA = SOME (i,nL)`
                          by (
                          fs[findNode_def,concr2AbstrAA_def,
                               ALTER_A_component_equality]
                          >> `inGBA g node.frmls` by (
                              simp[inGBA_def,EXISTS_MEM] >> qexists_tac `node`
                              >> simp[MEM_MAP,MEM_EQUAL_SET]
                              >> metis_tac[MEM_toAList,SND]
                          )
                          >> `set node.frmls ∈
                                 POW (concr2Abstr_states g_AA)`
                               by metis_tac[]
                          >> `q ∈ concr2Abstr_states g_AA`
                               by metis_tac[IN_POW,SUBSET_DEF]
                          >> fs[concr2Abstr_states_def]
                          >> rename[`SOME x2 = lookup n1 g_AA.nodeInfo` ]
                          >> rw[]
                          >> `(λ(i,l). l.frml = x2.frml) (n1,x2)` by fs[]
                          >> `∃y. FIND (λ(i,l). l.frml = x2.frml)
                                          (toAList g_AA.nodeInfo) = SOME y`
                              by metis_tac[FIND_LEMM,MEM_toAList]
                          >> qexists_tac `FST y` >> qexists_tac `SND y` >> fs[]
                       )
                       >> rename[`findNode _ g_AA = SOME (q_i,q_nL)`]
                       >> `?q_trns. SOME q_trns = concr_extrTrans g_AA q_i
                             ∧ MEM (q_i,q_nL) (toAList g_AA.nodeInfo)
                             ∧ (q_nL.frml = q)` by (
                           fs[findNode_def]
                           >> `MEM (q_i,q_nL) (toAList g_AA.nodeInfo)
                              ∧ ((λ(i,l). l.frml = q) (q_i,q_nL))`
                              by metis_tac[FIND_LEMM2]
                           >> `IS_SOME (lookup q_i g_AA.followers)` suffices_by (
                               rpt strip_tac >> simp[concr_extrTrans_def] >> fs[]
                               >> Cases_on `lookup q_i g_AA.followers`
                               >> fs[IS_SOME_DEF]
                               >> metis_tac[wfg_def,domain_lookup]
                           )
                           >> Cases_on `lookup q_i g_AA.followers`
                           >> fs[IS_SOME_DEF]
                           >> metis_tac[wfg_def,domain_lookup,MEM_toAList,
                                        NOT_SOME_NONE]
                       )
                       >> qexists_tac `(q,q_trns)` >> simp[]
                       >> fs[concr2AbstrAA_def,ALTER_A_component_equality]
                       >> `?fls. lookup q_i g_AA.followers = SOME fls` by (
                           metis_tac[domain_lookup,MEM_toAList,wfg_def,SOME_11]
                       )
                       >> `∃n cT.
                             concr_extrTrans g_AA q_i = SOME cT
                             ∧ lookup q_i g_AA.nodeInfo = SOME n
                             ∧ set (MAP (concr2AbstractEdge (set aP)) cT) =
                                    concrTrans g_AA (set aP) n.frml`
                         by (IMP_RES_TAC CONCR_EXTRTRANS_LEMM
                             >> first_x_assum (qspec_then `q_i` mp_tac)
                             >> simp[])
                        >> fs[] >> `q_nL = n'` by metis_tac[MEM_toAList,SOME_11]
                        >> rw[]
                     )
                      >- (
                       rename[`MEM edge _`] >> fs[MEM_MAP]
                       >> rename[`MEM cE zpd`] >> Cases_on `cE`
                       >> fs[] >> qunabbrev_tac `zpd`
                       >> rename[`MEM (q,q_trans) _`] >> POP_ASSUM mp_tac
                       >> simp[MEM_ZIP] >> rpt strip_tac
                       >- (
                         `inGBA g node.frmls` by (
                            simp[inGBA_def,EXISTS_MEM] >> qexists_tac `node`
                            >> simp[MEM_MAP,MEM_EQUAL_SET]
                            >> metis_tac[MEM_toAList,SND]
                         )
                         >> fs[concr2AbstrAA_def,ALTER_A_component_equality]
                         >> `set node.frmls ∈
                              POW (concr2Abstr_states g_AA)`
                            by metis_tac[]
                         >> `q ∈ concr2Abstr_states g_AA`
                           by metis_tac[IN_POW,SUBSET_DEF,EL_MEM]
                         >> fs[concr2Abstr_states_def]
                         >> rename[`q_i ∈ domain _`,`q = q_nL.frml`]
                         >> `findNode (λ(n,l). l.frml = q) g_AA
                                = SOME (q_i,q_nL)`
                            by metis_tac[UNIQUE_NODE_FIND_LEMM]
                         >> `?q_trns. concr_extrTrans g_AA q_i = SOME q_trns`
                            by (
                             simp[concr_extrTrans_def]
                             >> Cases_on `lookup q_i g_AA.followers` >> fs[]
                             >- metis_tac[wfg_def,NOT_SOME_NONE,domain_lookup]
                             >- metis_tac[]
                         )
                         >> rw[]
                         >> `MEM (q_nL.frml,q_trns) (ZIP (node.frmls,ce_lists))`
                             by metis_tac[EL_MEM]
                         >> `∃k. k < LENGTH node.frmls
                               ∧ (q_nL.frml,q_trns) = (EL k node.frmls,EL k ce_lists)`
                             by metis_tac[MEM_ZIP]
                         >> `EL k node.frmls = q_nL.frml` by fs[]
                         >> `k = n'` by metis_tac[ALL_DISTINCT_EL_IMP]
                         >> fs[]
                         >> `?fls. lookup q_i g_AA.followers = SOME fls`
                            by metis_tac[wfg_def,domain_lookup]
                         >> `∃n cT.
                              concr_extrTrans g_AA q_i = SOME cT
                            ∧ lookup q_i g_AA.nodeInfo = SOME n
                            ∧ set (MAP (concr2AbstractEdge (set aP)) cT) =
                                    concrTrans g_AA (set aP) n.frml`
                           by (IMP_RES_TAC CONCR_EXTRTRANS_LEMM
                               >> first_x_assum (qspec_then `q_i` mp_tac)
                               >> simp[] >> rpt strip_tac
                               >> first_x_assum (qspec_then `set aP` mp_tac)
                               >> fs[]
                              )
                         >> metis_tac[SOME_11]
                       )
                       >- metis_tac[EL_MEM]
                     )
                 )
                 >> `set node.frmls ∈
                       POW (concr2AbstrAA (concrAA g_AA init aP)).states` by (
                     `inGBA g node.frmls` suffices_by (
                         fs[vwaa2gba_def,concr2AbstrAA_def,ALTER_A_component_equality]
                         >> metis_tac[]
                     )
                     >> simp[inGBA_def,EXISTS_MEM,MEM_MAP]
                     >> qexists_tac `node` >> fs[MEM_EQUAL_SET]
                     >> qexists_tac `(id,node)` >> fs[]
                     >> metis_tac[MEM_toAList]
                 )
                 >> fs[]
                 >> `abstr_ce ∈
                       d_conj_set
                       {(q,(concr2AbstrAA (concrAA g_AA init aP)).trans q) |
                        MEM q node.frmls} (POW (set aP))` by (
                     fs[concr2AbstrAA_def,ALTER_A_component_equality]
                       >> metis_tac[]
                 )
                 >> `(FST abstr_ce,set cE.sucs) = abstr_ce` by (
                     qunabbrev_tac `abstr_ce`
                     >> Cases_on `cE` >> fs[concr2AbstractEdge_def]
                 )
                 >> fs[]
                 >> `(concr2AbstrAA (concrAA g_AA init aP)).alphabet =
                       POW (set aP)` by fs[concr2AbstrAA_def]
                 >> rpt strip_tac >> fs[] >> rename[`abstr_ce = abstr_ce2`]
                 >> `abstr_ce2 ∈
                       set (MAP (concr2AbstractEdge (set aP)) TRNS)` by (
                     IMP_RES_TAC GBA_TRANS_LEMM
                     >> first_x_assum (qspec_then `set aP` mp_tac) >> fs[]
                     >> rpt strip_tac >> qunabbrev_tac `TRNS` >> fs[]
                     >> metis_tac[MAP_ZIP]
                 )
                 >> POP_ASSUM mp_tac >> simp[MEM_MAP] >> strip_tac
                 >> rename[`MEM ce2 TRNS`] >> fs[]
                 >> `ce2 = cE \/ ~concr_min_rel (W_FINAL ce2) y`
                    by (
                       first_x_assum (qspec_then `W_FINAL ce2` mp_tac)
                       >> strip_tac
                       >> qunabbrev_tac `W_FINAL` >> fs[]
                       >> Cases_on `ce2 = cE` >> fs[] >> Cases_on `y` >> fs[]
                       >> rw[]
                 )
                 >> fs[]
                 >> `∀e1_lab e1_sucs e2_lab e2_sucs.
                   MEM_SUBSET ce2.pos aP ∧ MEM_SUBSET ce2.neg aP ∧
                   MEM_SUBSET ce2.sucs (graphStates g_AA) ∧ MEM_SUBSET cE.pos aP ∧
                   MEM_SUBSET cE.neg aP ∧ MEM_SUBSET cE.sucs (graphStates g_AA) ∧
                   ((e1_lab,e1_sucs) = concr2AbstractEdge (set aP) ce2) ∧
                   ((e2_lab,e2_sucs) = concr2AbstractEdge (set aP) cE)
                   ⇒ (((e1_lab,e1_sucs),e2_lab,e2_sucs) ∈
                        tr_less_general {acc_cond abstrAA f | MEM f (MAP FST acc)} (set node.frmls) ⇔
                        tlg_concr (ce2,get_acc_set acc ce2) (cE,get_acc_set acc cE))` by (
                        HO_MATCH_MP_TAC TLG_CONCR_LEMM >> qexists_tac `f`
                        >> qexists_tac `init` >> fs[] >> metis_tac[]
                        )
                 >> fs[]
                 >> first_x_assum (qspec_then `FST abstr_ce2` mp_tac)
                 >> rpt strip_tac
                 >> first_x_assum (qspec_then `SND abstr_ce2` mp_tac)
                 >> rpt strip_tac
                 >> first_x_assum (qspec_then `FST abstr_ce` mp_tac)
                 >> rpt strip_tac
                 >> first_x_assum (qspec_then `SND abstr_ce` mp_tac)
                 >> `!ce. MEM ce TRNS ==>
                             (MEM_SUBSET ce.pos aP
                             ∧ MEM_SUBSET ce.neg aP
                             ∧ MEM_SUBSET ce.sucs (graphStates g_AA))` by (
                      qunabbrev_tac `TRNS` >> fs[] >> gen_tac >> strip_tac
                      >> simp[MEM_SUBSET_SET_TO_LIST,SUBSET_DEF]
                      >> rpt strip_tac >> rename[`MEM x _`]
                      >- (`∃l ce. MEM l ce_lists ∧ MEM ce l ∧ MEM x ce.pos`
                            by metis_tac[GBA_TRANS_LEMM3]
                          >> qunabbrev_tac `ce_lists`
                          >> fs[MEM_MAP,CAT_OPTIONS_MEM]
                          >> metis_tac[MEM_SUBSET_SET_TO_LIST,SUBSET_DEF]
                         )
                      >- (`∃l ce. MEM l ce_lists ∧ MEM ce l ∧ MEM x ce.neg`
                            by metis_tac[GBA_TRANS_LEMM3]
                          >> qunabbrev_tac `ce_lists`
                          >> fs[MEM_MAP,CAT_OPTIONS_MEM]
                          >> metis_tac[MEM_SUBSET_SET_TO_LIST,SUBSET_DEF]
                         )
                      >- (`∃l ce. MEM l ce_lists ∧ MEM ce l ∧ MEM x ce.sucs`
                            by metis_tac[GBA_TRANS_LEMM3]
                          >> qunabbrev_tac `ce_lists`
                          >> fs[MEM_MAP,CAT_OPTIONS_MEM]
                          >> qunabbrev_tac `L` >> fs[MEM_MAP] >> Cases_on `z`
                          >> fs[] >> rw[]
                          >> `MEM (q,r) (toAList g_AA.nodeInfo)` by (
                             fs[findNode_def] >> metis_tac[FIND_LEMM2]
                          )
                          >> `?fls. lookup q g_AA.followers = SOME fls` by (
                                metis_tac[domain_lookup,MEM_toAList,wfg_def,SOME_11]
                          )
                          >> `∃n cT.
                               (concr_extrTrans g_AA q = SOME cT)
                               ∧ (lookup q g_AA.nodeInfo = SOME n)
                               ∧ (set (MAP (concr2AbstractEdge (set aP)) cT) =
                                  concrTrans g_AA (set aP) n.frml)`
                           by (IMP_RES_TAC CONCR_EXTRTRANS_LEMM
                               >> first_x_assum (qspec_then `q` mp_tac)
                               >> simp[]
                              )
                          >> `l = cT` by metis_tac[SOME_11] >> rw[]
                          >> `concr2AbstractEdge (set aP) ce' ∈
                                    concrTrans g_AA (set aP) n'.frml` by (
                             metis_tac[MEM_MAP,SET_EQ_SUBSET,SUBSET_DEF]
                          )
                          >> fs[concr2AbstrAA_def,ALTER_A_component_equality]
                          >> rw[]
                          >> fs[isValidAlterA_def,concr2Abstr_states_def]
                          >> `n'.frml ∈ (removeStatesSimpl (ltl2vwaa f)).states`
                             by (rw[] >> metis_tac[domain_lookup])
                          >> Cases_on `concr2AbstractEdge (set aP) ce'`
                          >> fs[]
                          >> `r' ⊆ (removeStatesSimpl (ltl2vwaa f)).states`
                             by metis_tac[]
                          >> rw[] >> simp[graphStates_def,MEM_MAP]
                          >> `r' ⊆
                                {x.frml |
                                 ∃n. (SOME x = lookup n g_AA.nodeInfo)
                                  ∧ (n ∈ domain g_AA.nodeInfo)}` by metis_tac[]
                          >> Cases_on `ce'`
                          >> fs[concr2AbstractEdge_def] >> rw[]
                          >> `x ∈
                                {x.frml |
                                 ∃n. (SOME x = lookup n g_AA.nodeInfo)
                                  ∧ n ∈ domain g_AA.nodeInfo}` by fs[SUBSET_DEF]
                          >> fs[] >> metis_tac[MEM_toAList,SND,FST]
                         )
                  )
                 >> `(MEM_SUBSET ce2.pos aP ∧ MEM_SUBSET ce2.neg aP)
                     ∧ (MEM_SUBSET ce2.sucs (graphStates g_AA) ∧ MEM_SUBSET cE.pos aP)
                     ∧ (MEM_SUBSET cE.neg aP ∧ MEM_SUBSET cE.sucs (graphStates g_AA))
                     ∧ ((FST abstr_ce2,SND abstr_ce2) = concr2AbstractEdge (set aP) ce2)
                     ∧ ((FST abstr_ce,SND abstr_ce) = concr2AbstractEdge (set aP) cE)`
                       by (rpt strip_tac >> fs[])
                 >> simp[]
                 >> qunabbrev_tac `W_FINAL` >> fs[all_acc_cond_def]
                 >> `{acc_cond (concr2AbstrAA (concrAA g_AA init aP)) f' |
                      MEM f' (MAP FST acc)} =
                     {acc_cond (concr2AbstrAA (concrAA g_AA init aP)) f |
                      f | f ∈ (concr2AbstrAA (concrAA g_AA init aP)).final}`
                    by (
                     `∀f. MEM f (MAP FST acc) ⇔ f ∈ concr2Abstr_final g_AA`
                        by metis_tac[VALID_ACC_LEMM]
                     >> simp[SET_EQ_SUBSET,SUBSET_DEF,concr2AbstrAA_def]
                     >> rpt strip_tac
                  )
                 >> Cases_on `y` >> fs[concr_min_rel_def]
                 >- metis_tac[]
                 >- (`abstr_ce2 = abstr_ce` by (
                       Cases_on `cE` >> Cases_on `ce2`
                       >> simp[concr2AbstractEdge_def]
                       >> fs[concrEdge_component_equality]
                       >> `!x y. MEM_EQUAL x y ==>
                                  MEM_SUBSET x y ∧ MEM_SUBSET y x`
                          by metis_tac[MEM_EQUAL_SET,MEM_SUBSET_SET_TO_LIST,
                                       SET_EQ_SUBSET]
                       >> simp[SET_EQ_SUBSET] >> rpt strip_tac
                       >- metis_tac[TRANSFORMLABEL_SUBSET]
                       >- metis_tac[TRANSFORMLABEL_SUBSET]
                       >- metis_tac[MEM_EQUAL_SET,SET_EQ_SUBSET]
                       >- metis_tac[MEM_EQUAL_SET,SET_EQ_SUBSET]
                    )
                    >> rw[]
                    )
                 >- (rw[] >> Cases_on `cE` >> Cases_on `ce2`
                     >> simp[concr2AbstractEdge_def]
                     >> fs[concrEdge_component_equality,MEM_EQUAL_SET]
                     >> rename[`_ (set aP) pos1 neg1 = _ (set aP) pos2 neg2`]
                     >> `pos1 = (concrEdge pos1 neg1 l1).pos` by fs[]
                     >> `neg1 = (concrEdge pos1 neg1 l1).neg` by fs[]
                     >> `pos2 = (concrEdge pos2 neg2 l1').pos` by fs[]
                     >> `neg2 = (concrEdge pos2 neg2 l1').neg` by fs[]
                     >> metis_tac[TRNS_IS_EMPTY_LEMM,MEM_SUBSET_SET_TO_LIST]
                    )
                 )
                >- (qexists_tac `node.frmls` >> simp[inGBA_def,EXISTS_MEM]
                    >> qexists_tac `node` >> simp[MEM_MAP,MEM_EQUAL_SET]
                    >> metis_tac[MEM_toAList,SND]
                   )
         )
        >> rpt conj_tac
        >- metis_tac[]
        >- (rpt strip_tac >> fs[] >> rename[`set x ∈ _`]
            >> `set x ∈ {set x | inGBA g x} ∪ set (MAP set NEW_NODES)` by (
                 `set x ∈ {set x | inGBA G1 x}` by (simp[] >> metis_tac[])
                 >> metis_tac[UNION_DEF]
             )
            >> fs[UNION_DEF]
            >- metis_tac[]
            >- (qunabbrev_tac `NEW_NODES` >> fs[MEM_MAP,MEM_FILTER]
                >> `?id nL. (lookup id G2.nodeInfo = SOME nL)
                          ∧ (MEM id new_ids) ∧ (set nL.frmls = set x)` by (
                     fs[inGBA_def,EXISTS_MEM,MEM_MAP]
                     >> rename[`MEM y2 (toAList G2.nodeInfo)`] >> Cases_on `y2`
                     >> rename[`MEM (id,nL) (toAList G2.nodeInfo)`]
                     >> qexists_tac `id` >> qexists_tac `nL`
                     >> fs[MEM_EQUAL_SET,MEM_toAList]
                     >> first_x_assum (qspec_then `nL` mp_tac) >> rw[]
                     >> rename[`set n1.frmls = set _`]
                     >> first_x_assum (qspec_then `(id,n1)` mp_tac)
                     >> simp[] >> rpt strip_tac
                     >> `id ∈ {x | MEM x new_ids ∨ x ∈ domain g.nodeInfo}`
                        by metis_tac[domain_lookup]
                     >> `~(id ∈ domain g.nodeInfo)`
                         by metis_tac[MEM_toAList,domain_lookup]
                     >> fs[]
                 )
                >> `set nL.frmls ∈
                          reachableFromSetGBA abstr_gba {set q | inGBA g q}`
                   by metis_tac[]
                >> rename[`MEM y1 TRNS`, `y = _ y1`] >> Cases_on `y1` >> fs[]
                >> rw[] >> POP_ASSUM mp_tac >> simp[reachableFromSetGBA_def]
                >> rpt strip_tac >> fs[] >> rw[]
                >> rename[`inGBA g q_inter`]
                >> `set q_inter ∈ reachableFromSetGBA abstr_gba abstr_gba.initial`
                   by metis_tac[]
                >> POP_ASSUM mp_tac >> simp[reachableFromSetGBA_def]
                >> rpt strip_tac >> rename[`q_init ∈ abstr_gba.initial`]
                >> qexists_tac `q_init` >> fs[] >> fs[reachableFromGBA_def]
                >> metis_tac[RTC_RTC]
               )
           )
        >- (rpt strip_tac
         >- (`domain g.nodeInfo ⊆ domain G2.nodeInfo` by metis_tac[SUBSET_UNION]
             >> metis_tac[SUBSET_DEF]
            )
         >- metis_tac[domain_lookup]
           )
        >- fs[expandGBA_def]
        >- (rpt strip_tac >> rename[`set x ∈ POW _`]
            >> `set x ∈ {set x | inGBA g x} ∪ set (MAP set NEW_NODES)` by (
                 `set x ∈ {set x | inGBA G1 x}` by (simp[] >> metis_tac[])
                 >> metis_tac[UNION_DEF]
             )
            >> fs[UNION_DEF]
            >- metis_tac[]
            >- (qunabbrev_tac `NEW_NODES` >> qunabbrev_tac `TRNS`
                >> fs[MEM_MAP,MEM_FILTER,ONLY_MINIMAL_MEM]
                >> qabbrev_tac `L =
                    CAT_OPTIONS
                    (MAP (concr_extrTrans g_AA)
                      (CAT_OPTIONS
                       (MAP
                         (λf.
                              OPTION_MAP FST
                              (findNode (λ(i,l). l.frml = f) g_AA))
                         node.frmls)))`
                >> `!s. MEM s cE.sucs ==>
                    ∃l ce. MEM l L ∧ MEM ce l ∧ MEM s ce.sucs`
                     by metis_tac[GBA_TRANS_LEMM3]
                >> simp[IN_POW,SUBSET_DEF] >> rpt strip_tac
                >> rename[`MEM s cE.sucs`]
                >> `∃l ce. MEM l L ∧ MEM ce l ∧ MEM s ce.sucs` by fs[]
                >> qunabbrev_tac `L` >> fs[CAT_OPTIONS_MEM,MEM_MAP]
                >> `MEM s (graphStates g_AA) ∧ ALL_DISTINCT ce.sucs`
                     by metis_tac[CONCR_EXTRTRANS_NODES]
                >> fs[graphStates_def,MEM_MAP,concr2AbstrAA_def,
                      concr2Abstr_states_def]
                >> rename[`MEM y3 (toAList g_AA.nodeInfo)`]
                >> Cases_on `y3` >> fs[]
                >> metis_tac[MEM_toAList,domain_lookup]
               )
           )
        >- (fs[frml_ad_def] >> rpt strip_tac
            >> `i ∈ (set new_ids ∪ domain g.nodeInfo)` by metis_tac[]
            >> fs[UNION_DEF]
            >- (`MEM n.frmls NEW_NODES` by metis_tac[SOME_11]
                >> qunabbrev_tac `NEW_NODES` >> qunabbrev_tac `TRNS`
                >> fs[MEM_MAP,MEM_FILTER,ONLY_MINIMAL_MEM]
                >> qabbrev_tac `L =
                    CAT_OPTIONS
                    (MAP (concr_extrTrans g_AA)
                      (CAT_OPTIONS
                       (MAP
                         (λf.
                              OPTION_MAP FST
                              (findNode (λ(i,l). l.frml = f) g_AA))
                         node.frmls)))`
                >> qunabbrev_tac `L` >> fs[CAT_OPTIONS_MEM,MEM_MAP]
                >> metis_tac[GBA_TRANS_LEMM1]
               )
            >- metis_tac[]
           )
       )
  );

val one_step_closed_apart_l_def = Define`
  one_step_closed_apart_l abstrAA g l =
   !nL qs i.
        (lookup i g.nodeInfo = SOME nL)
        ∧ (set nL.frmls = qs)
        ∧ ~(MEM i l)
        ==> (!ys. stepGBA (vwaa2gba abstrAA) qs (set ys)
                  ==> inGBA g ys)`;

val one_step_closed_def = Define`
  one_step_closed abstrAA g =
        (!xs. inGBA g xs
                  ==> (!ys. stepGBA (vwaa2gba abstrAA) (set xs) (set ys)
                         ==> inGBA g ys)
        )`;

val EXPGBA_ALL_REACHABLE = store_thm
  ("EXPGBA_ALL_REACHABLE",
   ``!abstrAA f init aP g_AA acc ids g g2.
      (abstrAA = concr2AbstrAA (concrAA g_AA init aP))
      ∧ (abstrAA = removeStatesSimpl (ltl2vwaa f))
      ∧ (wfg g_AA)
      ∧ (until_iff_final g_AA)
      ∧ (!id cT. (concr_extrTrans g_AA id = SOME cT)
         ==> (!ce. MEM ce cT
                   ==> (MEM_SUBSET ce.pos aP ∧ MEM_SUBSET ce.neg aP))
        )
      ∧ (valid_acc aP g_AA acc)
      ∧ (unique_node_formula g_AA) ∧ (flws_sorted g_AA)
      ∧ (expandGBA g_AA acc ids g = SOME g2)
      ∧ (!i. MEM i ids ==> i ∈ domain g.nodeInfo)
      ∧ (wfg g)
      ∧ frml_ad g
      ∧ (one_step_closed_apart_l abstrAA g ids)
      ==> (one_step_closed abstrAA g2)``,
   gen_tac >> gen_tac >> gen_tac >> gen_tac
   >> HO_MATCH_MP_TAC (theorem "expandGBA_ind") >> strip_tac
   >- (fs[one_step_closed_def] >> rpt strip_tac >> fs[expandGBA_def] >> rw[]
       >> fs[one_step_closed_apart_l_def,inGBA_def,EXISTS_MEM,MEM_MAP]
       >> Cases_on `y` >> fs[] >> rw[]
       >> first_x_assum (qspec_then `n` mp_tac) >> strip_tac
       >> first_x_assum (qspec_then `q` mp_tac)
       >> `lookup q g.nodeInfo = SOME n` by metis_tac[MEM_toAList]
       >> simp[] >> strip_tac
       >> first_x_assum (qspec_then `ys` mp_tac)
       >> `set xs = set n.frmls` by metis_tac[MEM_EQUAL_SET]
       >> fs[]
      )
   >- (strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac
       >> strip_tac >> strip_tac >> strip_tac
       >> fs[]
       >> simp[one_step_closed_def] >> strip_tac >> strip_tac >> strip_tac
       >> `?node. lookup id g.nodeInfo = SOME node` by metis_tac[domain_lookup]
       >> first_x_assum (qspec_then `node` mp_tac) >> simp[]
       >> strip_tac
       >> qabbrev_tac `TRNS =
            ONLY_MINIMAL
                concr_min_rel
                (MAP (λcE. (cE,get_acc_set acc cE))
                     (gba_trans_concr
                       (CAT_OPTIONS
                         (MAP (concr_extrTrans g_AA)
                           (CAT_OPTIONS
                                (MAP
                                     (λf.
                                          OPTION_MAP FST
                                          (findNode (λ(i,l). l.frml = f)
                                                    g_AA)) node.frmls))))))`
        >> Cases_on `FOLDR
              (λn (ids,g).
                  if inGBA g n then (ids,g)
                  else (g.next::ids,addNodeToGBA g n)) ([],g)
              (FILTER (λqs. ¬inGBA g qs) (MAP (λ(cE,fs). cE.sucs) TRNS))`
        >> fs[] >> rename[`_ = (new_ids,G1)`]
        >> `wfg G1` by (
             `G1 = SND (new_ids,G1)` by fs[]
             >> metis_tac[ADDNODE_GBA_WFG_FOLDR]
         )
        >> qabbrev_tac `NEW_NODES =
             FILTER (λqs. ¬inGBA g qs) (MAP (λ(cE,fs). cE.sucs) TRNS)`
        >> `{set x | inGBA G1 x} =
               {set x | inGBA g x} ∪ set (MAP set NEW_NODES)` by (
             `G1 = SND (new_ids,G1)` by fs[]
             >> metis_tac[ADDNODE_GBA_FOLDR,WF_IMP_SUFFWFG]
         )
        >> `∀x. MEM x (MAP FST TRNS) ⇒ inGBA G1 x.sucs` by (
             rpt strip_tac >> rename[`MEM qs (MAP FST TRNS)`]
             >> fs[MEM_MAP] >> rename[`MEM t TRNS`] >> Cases_on `t` >> fs[]
             >> rw[]
             >> `(MEM q.sucs NEW_NODES) \/ (inGBA g q.sucs)` by (
                 qunabbrev_tac `NEW_NODES` >> fs[MEM_FILTER]
                 >> Cases_on `inGBA g q.sucs` >> fs[]
                 >> simp[MEM_MAP]
                 >> qexists_tac `(q,r)` >> fs[]
             )
             >- (`MEM ((set q.sucs) ) (MAP set NEW_NODES)`
                  by (fs[MEM_MAP] >> metis_tac[])
                 >> `(set q.sucs) ∈ {set x | inGBA G1 x }`
                    by metis_tac[IN_UNION]
                 >> fs[]
                 >> metis_tac[IN_GBA_MEM_EQUAL,MEM,MEM_EQUAL_SET]
                )
             >- (`(set q.sucs) ∈{set x | inGBA g x}`
                   by (fs[MEM_MAP] >> metis_tac[])
                  >> `(set q.sucs) ∈ {set x | inGBA G1 x}`
                   by metis_tac[IN_UNION]
                  >> fs[] >> metis_tac[IN_GBA_MEM_EQUAL,MEM_EQUAL_SET]
                )
         )
        >> `!x. MEM x
                 (MAP SND (MAP
                        (λ(cE,f). (edgeLabelGBA cE.pos cE.neg f,cE.sucs))
                        TRNS)) ==> inGBA G1 x` by (
             rpt strip_tac >> fs[MEM_MAP] >> rename[`MEM t TRNS`]
             >> Cases_on `t` >> fs[]
             >> `FST (q,r) = q` by fs[] >> metis_tac[]
         )
        >> `(set new_ids ∪ domain g.nodeInfo = domain G1.nodeInfo)
           ∧ g.next ≤ G1.next` by metis_tac[FST,SND,ADDNODE_GBA_DOM_FOLDR]
        >> `∃g2.
             (FOLDR
             (λ(eL,suc) g_opt. do g <- g_opt; addEdgeToGBA g id eL suc od)
             (SOME G1)
             (MAP (λ(cE,f). (edgeLabelGBA cE.pos cE.neg f,cE.sucs)) TRNS) =
              SOME g2) ∧ G1.nodeInfo = g2.nodeInfo ∧ wfg g2` by (
             HO_MATCH_MP_TAC ADDEDGE_GBA_FOLDR_LEMM
             >> rpt conj_tac
             >- metis_tac[]
             >- metis_tac[domain_lookup,IN_UNION]
             >- metis_tac[]
         )
        >> rename[`wfg G2`] >> first_x_assum (qspec_then `G2` mp_tac) >> fs[]
        >> `(∀id cT.
              (concr_extrTrans g_AA id = SOME cT) ⇒
              ∀ce. MEM ce cT ⇒ MEM_SUBSET ce.pos aP ∧ MEM_SUBSET ce.neg aP)`
             by (rpt strip_tac >> rw[] >> fs[] >> metis_tac[])
        >> simp[] >> Q.HO_MATCH_ABBREV_TAC `(!g2. A g2 ==> B g2) ==> C`
        >> `B g2 ==> C` by (
            qunabbrev_tac `B` >> simp[one_step_closed_def]
            >> metis_tac[]
        )
        >> `A g2` suffices_by fs[] >> qunabbrev_tac `A` >> fs[]
        >> qabbrev_tac `abstr_gba =
             vwaa2gba (concr2AbstrAA (concrAA g_AA init aP))`
        >> `!x. inGBA G1 x = inGBA G2 x` by simp[inGBA_def]
        >> `!x. set x ∈ reachableFromSetGBA abstr_gba {set q | inGBA g q }
                 ==> (set x ∈ reachableFromSetGBA abstr_gba
                                {set q | inGBA G2 q })` by (
            simp[reachableFromSetGBA_def] >> rpt strip_tac
            >> `set q ∈ {set x | inGBA g x}` by (simp[] >> metis_tac[])
            >> `set q ∈ {set x | inGBA G1 x}` by metis_tac[IN_UNION]
            >> fs[] >> metis_tac[]
        )
        >> `(∀i.
             i ∈ domain g.nodeInfo ⇒
             lookup i g.nodeInfo = lookup i G1.nodeInfo)
                 ∧ (∀i.
                     MEM i new_ids ⇒
                     ∃n.
                     lookup i G1.nodeInfo = SOME n ∧ MEM n.frmls NEW_NODES)`
             by metis_tac[WF_IMP_SUFFWFG,ADDNODE_GBA_FOLDR,SND,FST]
         >> `isVeryWeakAlterA abstrAA ∧ isValidAlterA abstrAA
             ∧ (FINITE abstrAA.states)
             ∧ (abstrAA.alphabet = POW (set aP))` by (
             fs[] >> rpt strip_tac
             >- metis_tac[REDUCE_STATE_IS_WEAK,LTL2WAA_ISWEAK,
                           LTL2WAA_ISVALID]
             >- metis_tac[REDUCE_STATE_IS_VALID,LTL2WAA_ISVALID]
             >- (simp[concr2AbstrAA_def,concr2Abstr_states_def]
                 >> `FINITE {x.frml | ?n. MEM (n,x) (toAList g_AA.nodeInfo)}`
                     suffices_by (
                      Q.HO_MATCH_ABBREV_TAC `FINITE S1 ==> FINITE S2`
                      >> `S1 = S2` suffices_by fs[]
                      >> qunabbrev_tac `S1` >> qunabbrev_tac `S2`
                      >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                      >> metis_tac[MEM_toAList,domain_lookup]
                  )
                 >> `{x.frml | ∃n. MEM (n,x) (toAList g_AA.nodeInfo)} =
                      IMAGE (λ(i,n). n.frml) (set (toAList g_AA.nodeInfo))` by (
                      simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                      >- (qexists_tac `(n,x')` >> fs[])
                      >- (fs[] >> Cases_on `x'` >> fs[] >> metis_tac[])
                  )
                 >> metis_tac[FINITE_LIST_TO_SET,IMAGE_FINITE]
                )
             >- simp[concr2AbstrAA_def]
         )
         >> rpt conj_tac
         >- metis_tac[]
         >- fs[expandGBA_def]
         >- (rpt strip_tac
          >- (`domain g.nodeInfo ⊆ domain G2.nodeInfo` by metis_tac[SUBSET_UNION]
                                                              >> metis_tac[SUBSET_DEF]
                    )
                 >- metis_tac[domain_lookup]
            )
         >- (fs[frml_ad_def] >> rpt strip_tac
            >> `i ∈ (set new_ids ∪ domain g.nodeInfo)` by metis_tac[]
            >> fs[UNION_DEF]
            >- (`MEM n.frmls NEW_NODES` by metis_tac[SOME_11]
                >> qunabbrev_tac `NEW_NODES` >> qunabbrev_tac `TRNS`
                >> fs[MEM_MAP,MEM_FILTER,ONLY_MINIMAL_MEM]
                >> qabbrev_tac `L =
                    CAT_OPTIONS
                    (MAP (concr_extrTrans g_AA)
                      (CAT_OPTIONS
                        (MAP
                             (λf.
                                  OPTION_MAP FST
                                  (findNode (λ(i,l). l.frml = f) g_AA))
                             node.frmls)))`
                >> qunabbrev_tac `L` >> fs[CAT_OPTIONS_MEM,MEM_MAP]
                >> metis_tac[GBA_TRANS_LEMM1]
               )
            >- metis_tac[]
         )
         >- (simp[one_step_closed_apart_l_def] >> rpt strip_tac
             >> rename[`inGBA G2 ys`]
             >> `i ∈ domain G2.nodeInfo` by metis_tac[domain_lookup]
             >> `i ∈ domain g.nodeInfo` by metis_tac[SET_EQ_SUBSET,SUBSET_DEF,IN_UNION]
             >> fs[one_step_closed_apart_l_def]
             >> `lookup i g.nodeInfo = SOME nL` by metis_tac[SOME_11]
             >> Cases_on `i = id`
             >- (rw[]
                 >> fs[stepGBA_def]
                 >> `?ys1.
                       MEM_EQUAL ys1 ys
                    ∧ (MEM ys1
                           (MAP SND
                                (MAP (λ(cE,f).
                                       (edgeLabelGBA cE.pos cE.neg f,cE.sucs))
                                     TRNS)))` suffices_by (
                      rpt strip_tac >> metis_tac[IN_GBA_MEM_EQUAL]
                  )
                 >> fs[stepGBA_def] >> qunabbrev_tac `abstr_gba`
                 >> fs[vwaa2gba_def]
                 >> Cases_on `isVeryWeakAlterA
                               (concr2AbstrAA (concrAA g_AA init aP))` >> fs[]
                 >- (
                  fs[gba_trans_def,d_gen_def,minimal_elements_def]
                    >> qunabbrev_tac `TRNS` >> fs[MEM_MAP,ONLY_MINIMAL_MEM]
                    >> qabbrev_tac `TRNS =
                        gba_trans_concr
                         (CAT_OPTIONS
                          (MAP (concr_extrTrans g_AA)
                               (CAT_OPTIONS
                                    (MAP
                                         (λf.
                                              OPTION_MAP FST
                                              (findNode (λ(i,l). l.frml = f)
                                                        g_AA)) node.frmls))))`
                    >> qabbrev_tac `TO_SUCS =
                        λ(cE,f).
                         (edgeLabelGBA cE.pos cE.neg f,cE.sucs)`
                    >> qabbrev_tac `W_FINAL = λcE. (cE,get_acc_set acc cE)`
                >> qabbrev_tac `ce_lists =
                      CAT_OPTIONS
                       (MAP (concr_extrTrans g_AA)
                         (CAT_OPTIONS
                           (MAP
                             (λf.
                               OPTION_MAP FST
                               (findNode (λ(i,l). l.frml = f) g_AA))
                             node.frmls)))`
                >> qabbrev_tac `zpd = ZIP (node.frmls,ce_lists)`
                >> qabbrev_tac `L =
                      MAP
                       (λf.
                         OPTION_MAP FST
                         (findNode (λ(i,l). l.frml = f) g_AA))
                       node.frmls`
                >> `EVERY IS_SOME L` by (
                       qunabbrev_tac `L` >> fs[] >> simp[EVERY_MEM]
                       >> rpt strip_tac >> fs[MEM_MAP]
                       >> Cases_on `e` >> fs[IS_SOME_DEF]
                       >> `inGBA g node.frmls` by (
                           simp[inGBA_def,EXISTS_MEM] >> qexists_tac `node`
                           >> simp[MEM_MAP,MEM_EQUAL_SET]
                           >> metis_tac[MEM_toAList,SND]
                       )
                       >> `set node.frmls ∈
                            POW (removeStatesSimpl (ltl2vwaa f)).states`
                           by metis_tac[]
                       >> fs[concr2AbstrAA_def]
                       >> `f' ∈ (removeStatesSimpl (ltl2vwaa f)).states`
                          by metis_tac[MEM,IN_POW,SUBSET_DEF]
                       >> `f' ∈ concr2Abstr_states g_AA`
                          by (fs[ALTER_A_component_equality] >> metis_tac[])
                       >> fs[concr2Abstr_states_def,findNode_def]
                       >> rename[`f1 = x1.frml`,`n1 ∈ domain g_AA.nodeInfo`]
                       >> `(λ(i,l). l.frml = f1) (n1,x1)` by fs[]
                       >> metis_tac[FIND_LEMM,NOT_SOME_NONE,MEM_toAList]
                   )
                >> `EVERY IS_SOME
                              (MAP (concr_extrTrans g_AA) (CAT_OPTIONS L))` by (
                       simp[EVERY_MEM] >> rpt strip_tac >> fs[MEM_MAP]
                       >> rename[`MEM some_id (CAT_OPTIONS L)`]
                       >> simp[concr_extrTrans_def]
                       >> Cases_on `lookup some_id g_AA.followers` >> fs[]
                       >-(qunabbrev_tac `L` >> fs[CAT_OPTIONS_MEM,MEM_MAP]
                        >> fs[findNode_def]
                        >> `MEM z (toAList g_AA.nodeInfo)`
                              by metis_tac[FIND_LEMM2]
                        >> Cases_on `z` >> fs[wfg_def]
                        >> rw[]
                        >> metis_tac[MEM_toAList,domain_lookup,wfg_def,
                                     NOT_SOME_NONE]
                         )
                       >- (
                         fs[] >> rpt strip_tac
                         >> Q.HO_MATCH_ABBREV_TAC `IS_SOME H` >> Cases_on `H`
                         >> fs[IS_SOME_DEF]
                         >> `some_id ∈ (domain g_AA.nodeInfo)`
                               by metis_tac[domain_lookup,wfg_def]
                         >> metis_tac[domain_lookup,NOT_SOME_NONE]
                         )
                       )
                >> `LENGTH node.frmls = LENGTH ce_lists` by (
                   qunabbrev_tac `ce_lists`
                   >> qunabbrev_tac `L`
                   >> metis_tac[LENGTH_MAP,CAT_OPTIONS_LENGTH]
                 )
                >> `MAP FST zpd = node.frmls` by (
                     qunabbrev_tac `zpd` >> fs[]
                     >> metis_tac[MAP_ZIP]
                 )
                >> `ALL_DISTINCT (MAP FST zpd)` by metis_tac[frml_ad_def]
                >> rw[]
                >> `!q_i q_nL q q_trns.
                      (findNode (λ(i,l). l.frml = q) g_AA = SOME (q_i,q_nL))
                      ∧ (q_nL.frml = q) ∧ MEM q nL.frmls
                      ∧ concr_extrTrans g_AA q_i = SOME q_trns
                      ==> MEM (q_nL.frml,q_trns) zpd` by (
                        qunabbrev_tac `zpd` >> simp[MEM_ZIP] >> rpt strip_tac
                        >> `?ind_q. EL ind_q nL.frmls = q_nL.frml
                                  ∧ ind_q < LENGTH nL.frmls`
                           by metis_tac[MEM_EL]
                        >> qexists_tac `ind_q` >> fs[]
                        >> qunabbrev_tac `ce_lists` >> rw[]
                        >> `LENGTH nL.frmls =
                             LENGTH (MAP (concr_extrTrans g_AA)
                                         (CAT_OPTIONS L))` by (
                            fs[CAT_OPTIONS_LENGTH]
                        )
                        >> `SOME
                             (EL ind_q (CAT_OPTIONS (MAP (concr_extrTrans g_AA)
                                                        (CAT_OPTIONS L)))) =
                            (EL ind_q (MAP (concr_extrTrans g_AA)
                                          (CAT_OPTIONS L)))` by
                         metis_tac[CAT_OPTIONS_EL]
                        >> `EL ind_q (MAP (concr_extrTrans g_AA)
                                     (CAT_OPTIONS L)) =
                            (concr_extrTrans g_AA (EL ind_q (CAT_OPTIONS L)))`
                            by fs[EL_MAP,LENGTH_MAP]
                        >> `LENGTH L = LENGTH nL.frmls` by (
                            qunabbrev_tac `L`
                            >> fs[LENGTH_MAP]
                        )
                        >> `SOME (EL ind_q (CAT_OPTIONS L)) =
                              EL ind_q L` by metis_tac[CAT_OPTIONS_EL]
                        >> `EL ind_q L = SOME q_i` by (
                            qunabbrev_tac `L` >> simp[EL_MAP]
                        )
                        >> rw[] >> `EL ind_q (CAT_OPTIONS L) = q_i` by fs[]
                        >> metis_tac[SOME_11]
                 )
                >> `{(q,(removeStatesSimpl (ltl2vwaa f)).trans q) |
                         MEM q nL.frmls} =
                      set
                       (MAP (λ(q,d).
                              (q,set (MAP (concr2AbstractEdge (set aP)) d)))
                            zpd)` by (
                     simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                      >- (
                       simp[MEM_MAP]
                       >> `?i nL. findNode (λ(i,l). l.frml = q) g_AA = SOME (i,nL)`
                          by (
                          fs[findNode_def,concr2AbstrAA_def,
                               ALTER_A_component_equality]
                          >> `inGBA g nL.frmls` by (
                              simp[inGBA_def,EXISTS_MEM] >> qexists_tac `nL`
                              >> simp[MEM_MAP,MEM_EQUAL_SET]
                              >> metis_tac[MEM_toAList,SND]
                          )
                          >> `set nL.frmls ∈
                                 POW (concr2Abstr_states g_AA)`
                               by metis_tac[]
                          >> `q ∈ concr2Abstr_states g_AA`
                               by metis_tac[IN_POW,SUBSET_DEF]
                          >> fs[concr2Abstr_states_def]
                          >> rename[`SOME x2 = lookup n1 g_AA.nodeInfo` ]
                          >> rw[]
                          >> `(λ(i,l). l.frml = x2.frml) (n1,x2)` by fs[]
                          >> `∃y. FIND (λ(i,l). l.frml = x2.frml)
                                          (toAList g_AA.nodeInfo) = SOME y`
                              by metis_tac[FIND_LEMM,MEM_toAList]
                          >> qexists_tac `FST y` >> qexists_tac `SND y` >> fs[]
                       )
                       >> rename[`findNode _ g_AA = SOME (q_i,q_nL)`]
                       >> `?q_trns. SOME q_trns = concr_extrTrans g_AA q_i
                             ∧ MEM (q_i,q_nL) (toAList g_AA.nodeInfo)
                             ∧ (q_nL.frml = q)` by (
                           fs[findNode_def]
                           >> `MEM (q_i,q_nL) (toAList g_AA.nodeInfo)
                              ∧ ((λ(i,l). l.frml = q) (q_i,q_nL))`
                              by metis_tac[FIND_LEMM2]
                           >> `IS_SOME (lookup q_i g_AA.followers)` suffices_by (
                               rpt strip_tac >> simp[concr_extrTrans_def] >> fs[]
                               >> Cases_on `lookup q_i g_AA.followers`
                               >> fs[IS_SOME_DEF]
                               >> metis_tac[wfg_def,domain_lookup]
                           )
                           >> Cases_on `lookup q_i g_AA.followers`
                           >> fs[IS_SOME_DEF]
                           >> metis_tac[wfg_def,domain_lookup,MEM_toAList,
                                        NOT_SOME_NONE]
                       )
                       >> qexists_tac `(q,q_trns)` >> simp[]
                       >> fs[concr2AbstrAA_def,ALTER_A_component_equality]
                       >> `?fls. lookup q_i g_AA.followers = SOME fls` by (
                           metis_tac[domain_lookup,MEM_toAList,wfg_def,SOME_11]
                       )
                       >> `∃n cT.
                             concr_extrTrans g_AA q_i = SOME cT
                             ∧ lookup q_i g_AA.nodeInfo = SOME n
                             ∧ set (MAP (concr2AbstractEdge (set aP)) cT) =
                                    concrTrans g_AA (set aP) n.frml`
                         by (IMP_RES_TAC CONCR_EXTRTRANS_LEMM
                             >> first_x_assum (qspec_then `q_i` mp_tac)
                             >> simp[])
                        >> fs[] >> `q_nL = n` by metis_tac[MEM_toAList,SOME_11]
                        >> rw[]
                     )
                      >- (
                       rename[`MEM edge _`] >> fs[MEM_MAP]
                       >> rename[`MEM cE zpd`] >> Cases_on `cE`
                       >> fs[] >> qunabbrev_tac `zpd`
                       >> rename[`MEM (q,q_trans) _`] >> POP_ASSUM mp_tac
                       >> simp[MEM_ZIP] >> rpt strip_tac
                       >- (
                         `inGBA g nL.frmls` by (
                            simp[inGBA_def,EXISTS_MEM] >> qexists_tac `nL`
                            >> simp[MEM_MAP,MEM_EQUAL_SET]
                            >> metis_tac[MEM_toAList,SND]
                         )
                         >> fs[concr2AbstrAA_def,ALTER_A_component_equality]
                         >> `set nL.frmls ∈
                              POW (concr2Abstr_states g_AA)`
                            by metis_tac[]
                         >> `q ∈ concr2Abstr_states g_AA`
                           by metis_tac[IN_POW,SUBSET_DEF,EL_MEM]
                         >> fs[concr2Abstr_states_def]
                         >> rename[`q_i ∈ domain _`,`q = q_nL.frml`]
                         >> `findNode (λ(n,l). l.frml = q) g_AA
                                = SOME (q_i,q_nL)`
                            by metis_tac[UNIQUE_NODE_FIND_LEMM]
                         >> `?q_trns. concr_extrTrans g_AA q_i = SOME q_trns`
                            by (
                             simp[concr_extrTrans_def]
                             >> Cases_on `lookup q_i g_AA.followers` >> fs[]
                             >- metis_tac[wfg_def,NOT_SOME_NONE,domain_lookup]
                             >- metis_tac[]
                         )
                         >> rw[]
                         >> `MEM (q_nL.frml,q_trns) (ZIP (nL.frmls,ce_lists))`
                             by metis_tac[EL_MEM]
                         >> `∃k. k < LENGTH nL.frmls
                               ∧ (q_nL.frml,q_trns) = (EL k nL.frmls,EL k ce_lists)`
                             by metis_tac[MEM_ZIP]
                         >> `EL k nL.frmls = q_nL.frml` by fs[]
                         >> `k = n` by metis_tac[ALL_DISTINCT_EL_IMP]
                         >> fs[]
                         >> `?fls. lookup q_i g_AA.followers = SOME fls`
                            by metis_tac[wfg_def,domain_lookup]
                         >> `∃n cT.
                              concr_extrTrans g_AA q_i = SOME cT
                            ∧ lookup q_i g_AA.nodeInfo = SOME n
                            ∧ set (MAP (concr2AbstractEdge (set aP)) cT) =
                                    concrTrans g_AA (set aP) n.frml`
                           by (IMP_RES_TAC CONCR_EXTRTRANS_LEMM
                               >> first_x_assum (qspec_then `q_i` mp_tac)
                               >> simp[] >> rpt strip_tac
                               >> first_x_assum (qspec_then `set aP` mp_tac)
                               >> fs[]
                              )
                         >> metis_tac[SOME_11]
                       )
                       >- metis_tac[EL_MEM]
                     )
                 )
                >> IMP_RES_TAC GBA_TRANS_LEMM
                >> first_x_assum (qspec_then `set aP` mp_tac) >> simp[]
                >> strip_tac
                >> `(a,set ys) ∈
                       set
                       (MAP (concr2AbstractEdge (set aP))
                            (gba_trans_concr (MAP SND zpd)))` by metis_tac[]
                >> fs[MEM_MAP] >> rename[`MEM edge _`] >> Cases_on `edge`
                >> rename[`MEM (concrEdge pos neg sucs) _`]
                >> fs[concr2AbstractEdge_def] >> qexists_tac `sucs`
                >> `MEM_EQUAL sucs ys` by metis_tac[MEM_EQUAL_SET]
                >> simp[] >> qabbrev_tac `cE = concrEdge pos neg sucs`
                >> qexists_tac `
                      (edgeLabelGBA cE.pos cE.neg (get_acc_set acc cE),
                       cE.sucs)`
                >> simp[] >> `sucs = cE.sucs` by (qunabbrev_tac `cE` >> fs[])
                >> simp[] >> qexists_tac `(cE,get_acc_set acc cE)`
                >> qunabbrev_tac `TO_SUCS` >> qunabbrev_tac `W_FINAL` >> simp[]
                 >> `!ce. MEM ce TRNS ==>
                             (MEM_SUBSET ce.pos aP
                             ∧ MEM_SUBSET ce.neg aP
                             ∧ MEM_SUBSET ce.sucs (graphStates g_AA))` by (
                      qunabbrev_tac `TRNS` >> fs[] >> gen_tac >> strip_tac
                      >> simp[MEM_SUBSET_SET_TO_LIST,SUBSET_DEF]
                      >> rpt strip_tac >> rename[`MEM x _`]
                      >- (`∃l ce. MEM l ce_lists ∧ MEM ce l ∧ MEM x ce.pos`
                            by metis_tac[GBA_TRANS_LEMM3]
                          >> qunabbrev_tac `ce_lists`
                          >> fs[MEM_MAP,CAT_OPTIONS_MEM]
                          >> metis_tac[MEM_SUBSET_SET_TO_LIST,SUBSET_DEF]
                         )
                      >- (`∃l ce. MEM l ce_lists ∧ MEM ce l ∧ MEM x ce.neg`
                            by metis_tac[GBA_TRANS_LEMM3]
                          >> qunabbrev_tac `ce_lists`
                          >> fs[MEM_MAP,CAT_OPTIONS_MEM]
                          >> metis_tac[MEM_SUBSET_SET_TO_LIST,SUBSET_DEF]
                         )
                      >- (`∃l ce. MEM l ce_lists ∧ MEM ce l ∧ MEM x ce.sucs`
                            by metis_tac[GBA_TRANS_LEMM3]
                          >> qunabbrev_tac `ce_lists`
                          >> fs[MEM_MAP,CAT_OPTIONS_MEM]
                          >> qunabbrev_tac `L` >> fs[MEM_MAP] >> Cases_on `z`
                          >> fs[] >> rw[]
                          >> `MEM (q,r) (toAList g_AA.nodeInfo)` by (
                             fs[findNode_def] >> metis_tac[FIND_LEMM2]
                          )
                          >> `?fls. lookup q g_AA.followers = SOME fls`
                                by metis_tac[domain_lookup,MEM_toAList,
                                             wfg_def,SOME_11]
                          >> `∃n cT.
                               (concr_extrTrans g_AA q = SOME cT)
                               ∧ (lookup q g_AA.nodeInfo = SOME n)
                               ∧ (set (MAP (concr2AbstractEdge (set aP)) cT) =
                                  concrTrans g_AA (set aP) n.frml)`
                           by (IMP_RES_TAC CONCR_EXTRTRANS_LEMM
                               >> first_x_assum (qspec_then `q` mp_tac)
                               >> simp[]
                              )
                          >> `l = cT` by metis_tac[SOME_11] >> rw[]
                          >> `concr2AbstractEdge (set aP) ce' ∈
                                    concrTrans g_AA (set aP) n.frml` by (
                             metis_tac[MEM_MAP,SET_EQ_SUBSET,SUBSET_DEF]
                          )
                          >> fs[concr2AbstrAA_def,ALTER_A_component_equality]
                          >> rw[]
                          >> fs[isValidAlterA_def,concr2Abstr_states_def]
                          >> `n.frml ∈ (removeStatesSimpl (ltl2vwaa f)).states`
                             by (rw[] >> metis_tac[domain_lookup])
                          >> Cases_on `concr2AbstractEdge (set aP) ce'`
                          >> fs[]
                          >> `r' ⊆ (removeStatesSimpl (ltl2vwaa f)).states`
                             by metis_tac[]
                          >> rw[] >> simp[graphStates_def,MEM_MAP]
                          >> `r' ⊆
                                {x.frml |
                                 ∃n. (SOME x = lookup n g_AA.nodeInfo)
                                  ∧ (n ∈ domain g_AA.nodeInfo)}` by metis_tac[]
                          >> Cases_on `ce'`
                          >> fs[concr2AbstractEdge_def] >> rw[]
                          >> `x ∈
                                {x.frml |
                                 ∃n. (SOME x = lookup n g_AA.nodeInfo)
                                  ∧ n ∈ domain g_AA.nodeInfo}` by fs[SUBSET_DEF]
                          >> fs[] >> metis_tac[MEM_toAList,SND,FST]
                         )
                  )
                 >> qunabbrev_tac `TRNS` >> simp[]
                >> `MAP SND zpd = ce_lists`
                   by (qunabbrev_tac `zpd` >> metis_tac[MAP_ZIP])
                >> fs[] >> rpt strip_tac >> rename[`MEM cE2 _`]
                >> first_x_assum
                       (qspec_then `concr2AbstractEdge (set aP) cE2` mp_tac)
                >> Q.HO_MATCH_ABBREV_TAC `(Q1 ==> Q2) ==> F`
                >> `Q2 ==> F` by (
                      qunabbrev_tac `Q2` >> simp[] >> Cases_on `y`
                      >> `~(cE = cE2)` by metis_tac[]
                      >> Cases_on `~MEM_EQUAL q.sucs cE.sucs`
                      >- (Cases_on `cE2` >> simp[concr2AbstractEdge_def]
                          >> fs[MEM_EQUAL_SET,concrEdge_component_equality]
                          >> rw[] >> metis_tac[]
                         )
                      >- (Cases_on `~ trns_is_empty cE ∧ ~ trns_is_empty q`
                       >- (fs[concr_min_rel_def] >> Cases_on `cE2`
                           >> `!l1 l2. ~(set l1 ⊆ set l2) ==> ~MEM_SUBSET l1 l2`
                             by fs[MEM_SUBSET_SET_TO_LIST]
                           >> fs[MEM_EQUAL_SET,concrEdge_component_equality]
                           >> simp[concr2AbstractEdge_def]
                           >> rw[]
                           >> `(concrEdge q.pos q.neg q.sucs).pos = q.pos
                             ∧ (concrEdge q.pos q.neg q.sucs).neg = q.neg`
                             by fs[]
                           >> `∀x. MEM x pos ∨ MEM x q.pos
                                 ∨ MEM x neg ∨ MEM x q.neg ⇒ x ∈ set aP` by (
                                metis_tac[MEM_SUBSET_SET_TO_LIST,SUBSET_DEF,MEM]
                            ) >> CCONTR_TAC
                           >> fs[]
                           >> `set cE.pos ⊆ set aP
                                 ∧ set cE.neg ⊆ set aP
                                 ∧ set q.pos ⊆ set aP
                                 ∧ set q.neg ⊆ set aP`
                                by metis_tac[SUBSET_DEF]
                           >> fs[SET_EQ_SUBSET]
                           >> `~(transformLabel (set aP) pos neg = {})`
                               by metis_tac[TRNS_IS_EMPTY_LEMM]
                           >> `~(transformLabel (set aP) q.pos q.neg = {})`
                               by metis_tac[TRNS_IS_EMPTY_LEMM]
                           >> IMP_RES_TAC TRANSFORMLABEL_SUBSET2
                           >> metis_tac[]
                          )
                       >- (fs[concr_min_rel_def] >> Cases_on `cE2`
                           >> fs[MEM_EQUAL_SET,concrEdge_component_equality]
                           >> fs[concr2AbstractEdge_def]
                           >> rw[]
                           >> `(concrEdge q.pos q.neg q.sucs).pos = q.pos
                             ∧ (concrEdge q.pos q.neg q.sucs).neg = q.neg`
                               by fs[]
                           >> `set cE.pos ⊆ set aP
                             ∧ set cE.neg ⊆ set aP
                             ∧ set q.pos ⊆ set aP
                             ∧ set q.neg ⊆ set aP`
                                by metis_tac[MEM_SUBSET_SET_TO_LIST]
                           >> metis_tac[TRNS_IS_EMPTY_LEMM]
                          )
                  )
                  )
                >> `Q1` suffices_by metis_tac[]
                >> qunabbrev_tac `Q1` >> fs[]
                >> conj_tac
                >- metis_tac[MEM_MAP]
                >- (simp[rrestrict_def] >> conj_tac
                 >- (`tlg_concr y (cE,get_acc_set acc cE)` by
                        (Cases_on `y` >> fs[concr_min_rel_def])
                     >> Cases_on `y` >> rw[]
                     >> qabbrev_tac `abstrAA =
                          concr2AbstrAA (concrAA g_AA init aP)`
                     >> `∀e1_lab e1_sucs e2_lab e2_sucs.
                      MEM_SUBSET cE2.pos aP ∧ MEM_SUBSET cE2.neg aP ∧
                      MEM_SUBSET cE2.sucs (graphStates g_AA) ∧ MEM_SUBSET cE.pos aP ∧
                      MEM_SUBSET cE.neg aP ∧ MEM_SUBSET cE.sucs (graphStates g_AA) ∧
                      ((e1_lab,e1_sucs) = concr2AbstractEdge (set aP) cE2) ∧
                      ((e2_lab,e2_sucs) = concr2AbstractEdge (set aP) cE)
                      ⇒ (((e1_lab,e1_sucs),e2_lab,e2_sucs) ∈
                        tr_less_general
                          {acc_cond abstrAA f | MEM f (MAP FST acc)}
                          (set nL.frmls) ⇔
                        tlg_concr (cE2,get_acc_set acc cE2)
                                  (cE,get_acc_set acc cE))` by (
                        HO_MATCH_MP_TAC TLG_CONCR_LEMM >> qexists_tac `f`
                        >> qexists_tac `init` >> fs[] >> metis_tac[]
                        )
                     >> fs[]
                     >> first_x_assum
                           (qspec_then `transformLabel (set aP) cE2.pos cE2.neg`
                             mp_tac)
                     >> simp[] >> strip_tac
                     >> first_x_assum (qspec_then `set cE2.sucs` mp_tac)
                     >> simp[] >> strip_tac
                     >> first_x_assum
                           (qspec_then `transformLabel (set aP) cE.pos cE.neg`
                            mp_tac)
                     >> simp[] >> strip_tac
                     >> first_x_assum (qspec_then `set cE.sucs` mp_tac)
                     >> simp[] >> strip_tac
                     >> fs[all_acc_cond_def]
                     >> `{acc_cond (concr2AbstrAA (concrAA g_AA init aP)) f' |
                           MEM f' (MAP FST acc)} =
                         {acc_cond (concr2AbstrAA (concrAA g_AA init aP)) f |
                           f | f ∈ (concr2AbstrAA (concrAA g_AA init aP)).final}`
                    by (
                     `∀f. MEM f (MAP FST acc) ⇔ f ∈ concr2Abstr_final g_AA`
                        by metis_tac[VALID_ACC_LEMM]
                     >> simp[SET_EQ_SUBSET,SUBSET_DEF,concr2AbstrAA_def]
                     >> rpt strip_tac >> qexists_tac `f'` >> simp[]
                     >> qunabbrev_tac `abstrAA` >> fs[concr2AbstrAA_def]
                      )
                    >> Cases_on `cE` >> Cases_on `cE2`
                    >> fs[concr2AbstractEdge_def]
                    >> qunabbrev_tac `abstrAA` >> fs[concr2AbstrAA_def]
                    >> metis_tac[]
                    )
                 >- (metis_tac[MEM_MAP])
                   )
                  )
                 >- metis_tac[]
                )
             >- (`inGBA g ys` by metis_tac[SOME_11]
                 >> `set ys ∈ ({set x | inGBA g x} ∪ set (MAP set NEW_NODES))`
                  by (simp[IN_UNION] >> metis_tac[])
                 >> `set ys ∈ {set x | inGBA G2 x}`
                  by metis_tac[SET_EQ_SUBSET,SUBSET_DEF]
                 >> fs[] >> metis_tac[IN_GBA_MEM_EQUAL,MEM_EQUAL_SET]
                )
            )
      )
  );

val EXPGBA_TRANS_AND_FINAL = store_thm
  ("EXPGBA_TRANS_AND_FINAL",
   ``!abstrAA f init aP g_AA acc ids g g2.
     (abstrAA = concr2AbstrAA (concrAA g_AA init aP))
     ∧ (abstrAA = removeStatesSimpl (ltl2vwaa f))
     ∧ (wfg g_AA)
     ∧ (until_iff_final g_AA)
     ∧ (!id cT. (concr_extrTrans g_AA id = SOME cT)
         ==> (!ce. MEM ce cT
                   ==> (MEM_SUBSET ce.pos aP ∧ MEM_SUBSET ce.neg aP))
       )
     ∧ (valid_acc aP g_AA acc)
     ∧ (unique_node_formula g_AA) ∧ (flws_sorted g_AA)
     ∧ (expandGBA g_AA acc ids g = SOME g2)
     ∧ (!i. MEM i ids ==> i ∈ domain g.nodeInfo)
     ∧ (!i. MEM i ids ==> (lookup i g.followers = SOME []))
     ∧ (wfg g)
     ∧ (aP_correct abstrAA g aP)
     ∧ (final_correct abstrAA g acc)
     ∧ (trns_correct ids abstrAA g (set aP))
     ∧ (ALL_DISTINCT ids)
     ∧ frml_ad g
     ∧ ((!id fls.
         (lookup id g.followers = SOME fls)
     ==> (!eL s_id.
               MEM (eL,s_id) fls
               ==> s_id ∈ domain g.nodeInfo)))
  ==> ((aP_correct abstrAA g2 aP)
        ∧ (final_correct abstrAA g2 acc)
        ∧ (trns_correct [] abstrAA g2 (set aP))
      )``,
   gen_tac >> gen_tac >> gen_tac >> gen_tac
   >> HO_MATCH_MP_TAC (theorem "expandGBA_ind") >> strip_tac
   >- (rpt strip_tac >> fs[expandGBA_def] >> metis_tac[])
   >- (
    strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac
    >> strip_tac >> strip_tac >> strip_tac
    >> fs[]
    >> `?node. lookup id g.nodeInfo = SOME node` by metis_tac[domain_lookup]
    >> first_x_assum (qspec_then `node` mp_tac) >> simp[]
    >> strip_tac >> Q.HO_MATCH_ABBREV_TAC `P g2`
    >> qabbrev_tac `TRNS =
             ONLY_MINIMAL
                 concr_min_rel
                 (MAP (λcE. (cE,get_acc_set acc cE))
                    (gba_trans_concr
                        (CAT_OPTIONS
                            (MAP (concr_extrTrans g_AA)
                                 (CAT_OPTIONS
                                      (MAP
                                        (λf.
                                           OPTION_MAP FST
                                            (findNode (λ(i,l). l.frml = f)
                                                      g_AA)) node.frmls))))))`
    >> Cases_on `FOLDR
              (λn (ids,g).
                  if inGBA g n then (ids,g)
                  else (g.next::ids,addNodeToGBA g n)) ([],g)
              (FILTER (λqs. ¬inGBA g qs) (MAP (λ(cE,fs). cE.sucs) TRNS))`
    >> fs[] >> rename[`_ = (new_ids,G1)`]
    >> `wfg G1` by (
             `G1 = SND (new_ids,G1)` by fs[]
             >> metis_tac[ADDNODE_GBA_WFG_FOLDR]
         )
    >> qabbrev_tac `NEW_NODES =
             FILTER (λqs. ¬inGBA g qs) (MAP (λ(cE,fs). cE.sucs) TRNS)`
    >> `{set x | inGBA G1 x} =
               {set x | inGBA g x} ∪ set (MAP set NEW_NODES)` by (
             `G1 = SND (new_ids,G1)` by fs[]
             >> metis_tac[ADDNODE_GBA_FOLDR,WF_IMP_SUFFWFG]
         )
    >> `∀x. MEM x (MAP FST TRNS) ⇒ inGBA G1 x.sucs` by (
             rpt strip_tac >> rename[`MEM qs (MAP FST TRNS)`]
             >> fs[MEM_MAP] >> rename[`MEM t TRNS`] >> Cases_on `t` >> fs[]
             >> rw[]
             >> `(MEM q.sucs NEW_NODES) \/ (inGBA g q.sucs)` by (
                 qunabbrev_tac `NEW_NODES` >> fs[MEM_FILTER]
                 >> Cases_on `inGBA g q.sucs` >> fs[]
                 >> simp[MEM_MAP]
                 >> qexists_tac `(q,r)` >> fs[]
             )
             >- (`MEM ((set q.sucs) ) (MAP set NEW_NODES)`
                  by (fs[MEM_MAP] >> metis_tac[])
                 >> `(set q.sucs) ∈ {set x | inGBA G1 x }`
                    by metis_tac[IN_UNION]
                 >> fs[]
                 >> metis_tac[IN_GBA_MEM_EQUAL,MEM,MEM_EQUAL_SET]
                )
             >- (`(set q.sucs) ∈{set x | inGBA g x}`
                   by (fs[MEM_MAP] >> metis_tac[])
                  >> `(set q.sucs) ∈ {set x | inGBA G1 x}`
                   by metis_tac[IN_UNION]
                  >> fs[] >> metis_tac[IN_GBA_MEM_EQUAL,MEM_EQUAL_SET]
                )
         )
    >> `!x. MEM x
                 (MAP SND (MAP
                        (λ(cE,f). (edgeLabelGBA cE.pos cE.neg f,cE.sucs))
                        TRNS)) ==> inGBA G1 x` by (
             rpt strip_tac >> fs[MEM_MAP] >> rename[`MEM t TRNS`]
             >> Cases_on `t` >> fs[]
             >> `FST (q,r) = q` by fs[] >> metis_tac[]
         )
    >> `(set new_ids ∪ domain g.nodeInfo = domain G1.nodeInfo)
           ∧ g.next ≤ G1.next` by metis_tac[FST,SND,ADDNODE_GBA_DOM_FOLDR]
    >> `∃g2.
             (FOLDR
             (λ(eL,suc) g_opt. do g <- g_opt; addEdgeToGBA g id eL suc od)
             (SOME G1)
             (MAP (λ(cE,f). (edgeLabelGBA cE.pos cE.neg f,cE.sucs)) TRNS) =
              SOME g2) ∧ G1.nodeInfo = g2.nodeInfo ∧ wfg g2` by (
             HO_MATCH_MP_TAC ADDEDGE_GBA_FOLDR_LEMM
             >> rpt conj_tac
             >- metis_tac[]
             >- metis_tac[domain_lookup,IN_UNION]
             >- metis_tac[]
         )
    >> rename[`wfg G2`] >> first_x_assum (qspec_then `G2` mp_tac) >> fs[]
    >> `(∀id cT.
              (concr_extrTrans g_AA id = SOME cT) ⇒
              ∀ce. MEM ce cT ⇒ MEM_SUBSET ce.pos aP ∧ MEM_SUBSET ce.neg aP)`
             by (rpt strip_tac >> rw[] >> fs[] >> metis_tac[])
    >> simp[]
    >> Q.HO_MATCH_ABBREV_TAC `(!g2. (A g2) ==> B g2) ==> P g2`
    >> `B g2 ==> P g2` by (
        qunabbrev_tac `B` >> qunabbrev_tac `P`
        >> metis_tac[]
    )
    >> `A g2` suffices_by fs[] >> qunabbrev_tac `A` >> fs[]
    >> qabbrev_tac `abstr_gba =
        vwaa2gba (concr2AbstrAA (concrAA g_AA init aP))`
    >> `!x. inGBA G1 x = inGBA G2 x` by simp[inGBA_def]
    >> `(∀i.
          i ∈ domain g.nodeInfo ⇒
          (lookup i g.nodeInfo = lookup i G1.nodeInfo)
        ∧ (lookup i g.followers = lookup i G1.followers))
              ∧ (∀i.
                  MEM i new_ids ⇒
                  ∃n.
                  lookup i G1.nodeInfo = SOME n ∧ MEM n.frmls NEW_NODES
                ∧ (lookup i G1.followers = SOME [])
                ∧ (g.next <= i))`
          by metis_tac[WF_IMP_SUFFWFG,ADDNODE_GBA_FOLDR,SND,FST]
    >> `isVeryWeakAlterA abstrAA ∧ isValidAlterA abstrAA
              ∧ (FINITE abstrAA.states)
             ∧ (abstrAA.alphabet = POW (set aP))` by (
             fs[] >> rpt strip_tac
             >- metis_tac[REDUCE_STATE_IS_WEAK,LTL2WAA_ISWEAK,
                           LTL2WAA_ISVALID]
             >- metis_tac[REDUCE_STATE_IS_VALID,LTL2WAA_ISVALID]
             >- (simp[concr2AbstrAA_def,concr2Abstr_states_def]
                 >> `FINITE {x.frml | ?n. MEM (n,x) (toAList g_AA.nodeInfo)}`
                     suffices_by (
                      Q.HO_MATCH_ABBREV_TAC `FINITE S1 ==> FINITE S2`
                      >> `S1 = S2` suffices_by fs[]
                      >> qunabbrev_tac `S1` >> qunabbrev_tac `S2`
                      >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                      >> metis_tac[MEM_toAList,domain_lookup]
                  )
                 >> `{x.frml | ∃n. MEM (n,x) (toAList g_AA.nodeInfo)} =
                      IMAGE (λ(i,n). n.frml) (set (toAList g_AA.nodeInfo))` by (
                      simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                      >- (qexists_tac `(n,x')` >> fs[])
                      >- (fs[] >> Cases_on `x'` >> fs[] >> metis_tac[])
                  )
                 >> metis_tac[FINITE_LIST_TO_SET,IMAGE_FINITE]
                )
             >- simp[concr2AbstrAA_def]
         )
    >> `!ls G fls. (FOLDR
             (λ(eL,suc) g_opt. do g <- g_opt; addEdgeToGBA g id eL suc od)
             (SOME G1)
             (MAP (λ(cE,f). (edgeLabelGBA cE.pos cE.neg f,cE.sucs)) ls) =
               SOME G)
             ∧ (lookup id G.followers = SOME fls)
             ==> ((!eL s_id.
                      MEM (eL,s_id) fls
                      ==> s_id ∈ domain G.nodeInfo)
                ∧ (!eL qs.
                      (?s_id s_nL.
                        MEM (eL,s_id) fls
                        ∧ (lookup s_id G.nodeInfo = SOME s_nL)
                        ∧ MEM_EQUAL s_nL.frmls qs)
                      =
                      (?s_list.
                        MEM_EQUAL s_list qs
                        ∧ (MEM (eL,s_list)
                             (MAP (λ(cE,f).
                                    (edgeLabelGBA cE.pos cE.neg f,cE.sucs))
                                  ls)))))` by (
        Induct_on `ls` >> fs[] >> strip_tac
        >- (strip_tac >> `fls = []` by metis_tac[domain_lookup,SOME_11]
            >> fs[]
           )
        >- (rpt gen_tac >> strip_tac
            >> Cases_on `h` >> fs[] >> rename[`addEdgeToGBA G_int _ _ _ = _ _`]
            >> fs[addEdgeToGBA_def]
            >> Cases_on `findNode (λ(i,q'). MEM_EQUAL q'.frmls q.sucs) G_int`
            >> fs[] >> Cases_on `x` >> fs[addEdge_def]
            >> fs[gfg_component_equality]
            >> `fls = ((edgeLabelGBA q.pos q.neg r,q')::followers_old)`
                by metis_tac[lookup_insert,SOME_11]
            >> rpt gen_tac >> simp[EQ_IMP_THM] >> strip_tac
            >- (rw[]
                  >- metis_tac[findNode_def,FIND_LEMM2,MEM_toAList,domain_lookup]
                  >- metis_tac[]
               )
            >- (rw[]
             >- (qexists_tac `q.sucs` >> fs[]
                 >> rename[`findNode _ _ = SOME (id1,nL1)`]
                 >> `(λ(i,q'). MEM_EQUAL q'.frmls q.sucs) (id1,nL1)
                    ∧ MEM (id1,nL1) (toAList G_int.nodeInfo)`
                   by metis_tac[FIND_LEMM2,findNode_def]
                 >> `s_nL = nL1` by metis_tac[MEM_toAList,SOME_11]
                 >> rw[] >> fs[MEM_EQUAL_SET]
                )
             >- metis_tac[]
             >- (rename[`findNode _ _ = SOME (id1,nL1)`]
                 >> `(λ(i,q'). MEM_EQUAL q'.frmls q.sucs) (id1,nL1)
                     ∧ MEM (id1,nL1) (toAList G_int.nodeInfo)`
                     by metis_tac[FIND_LEMM2,findNode_def]
                 >> qexists_tac `id1` >> fs[] >> qexists_tac `nL1` >> simp[]
                 >> metis_tac[MEM_EQUAL_SET,MEM_toAList]
                )
             >- metis_tac[]
               )
           )
    )
    >> first_x_assum (qspec_then `TRNS` mp_tac) >> simp[]
    >> strip_tac
    >> `!ls G i. ~(i = id) ==>
             (FOLDR
                  (λ(eL,suc) g_opt. do g <- g_opt; addEdgeToGBA g id eL suc od)
                  (SOME G1)
                  (MAP (λ(cE,f). (edgeLabelGBA cE.pos cE.neg f,cE.sucs)) ls) =
              SOME G)
             ==> (lookup i G.followers = lookup i G1.followers)` by (
        Induct_on `ls` >> fs[] >> rpt strip_tac
        >> Cases_on `h` >> fs[] >> rename[`addEdgeToGBA G_int _ _ _ = _ _`]
        >> fs[addEdgeToGBA_def]
        >> Cases_on `findNode (λ(i,q'). MEM_EQUAL q'.frmls q.sucs) G_int`
        >> fs[] >> Cases_on `x` >> fs[]
        >> fs[addEdge_def,gfg_component_equality]
        >> metis_tac[lookup_insert]
    )
    >> first_x_assum (qspec_then `TRNS` mp_tac) >> simp[] >> strip_tac
    >> `aP_correct (concr2AbstrAA (concrAA g_AA init aP)) G2 aP
        ∧ trns_correct (nub (ids ++ new_ids))
           (concr2AbstrAA (concrAA g_AA init aP)) G2 (set aP)
        ∧ final_correct (concr2AbstrAA (concrAA g_AA init aP)) G2 acc` by (
     `!id fls nL.
        (lookup id G2.nodeInfo = SOME nL)
        ∧ (lookup id G2.followers = SOME fls)
        ∧ ((set nL.frmls) ∈ POW abstrAA.states)
        ==>
        ((~MEM id (nub (ids ++ new_ids))
         ==>
         (set
          (CAT_OPTIONS
            (MAP
             (λ(eL,i).
               do
               s_nL <- lookup i G2.nodeInfo;
              SOME
               (transformLabel (set aP) eL.pos_lab eL.neg_lab,
                set s_nL.frmls)
               od) fls)) = gba_trans abstrAA (set nL.frmls)
        ))
        ∧ (!eL s_id.
            MEM (eL,s_id) fls ⇒
            MEM_SUBSET eL.pos_lab aP ∧ MEM_SUBSET eL.neg_lab aP
          )
        ∧ (!eL s_id s_nL.
               MEM (eL,s_id) fls
               ∧ (lookup s_id G2.nodeInfo = SOME s_nL)
               ==> ∀u.
               MEM u eL.acc_set ⇔
               MEM u
               (get_acc_set acc
                           (concrEdge eL.pos_lab eL.neg_lab s_nL.frmls))))
        ` suffices_by (
        rpt strip_tac >> fs[aP_correct_def,trns_correct_def,final_correct_def]
        >> rpt strip_tac >> fs[]
        >- metis_tac[]
        >- metis_tac[]
        >- (first_x_assum(qspec_then `id'` mp_tac) >> simp[]
           )
        >- metis_tac[]
     )
     >> rpt gen_tac >> strip_tac
     >> rename[`lookup id2 G2.nodeInfo = SOME nL`]
     >> Cases_on `id = id2` >> fs[]
     >- (
         `node = nL` by metis_tac[SOME_11]
         >> qunabbrev_tac `TRNS` >> fs[MEM_MAP,ONLY_MINIMAL_MEM]
                    >> qabbrev_tac `TRNS =
                        gba_trans_concr
                         (CAT_OPTIONS
                          (MAP (concr_extrTrans g_AA)
                               (CAT_OPTIONS
                                    (MAP
                                         (λf.
                                              OPTION_MAP FST
                                              (findNode (λ(i,l). l.frml = f)
                                                        g_AA)) nL.frmls))))`
         >> qabbrev_tac `TO_SUCS =
                        λ(cE,f).
                         (edgeLabelGBA cE.pos cE.neg f,cE.sucs)`
         >> qabbrev_tac `W_FINAL = λcE. (cE,get_acc_set acc cE)`
         >> qabbrev_tac `ce_lists =
                      CAT_OPTIONS
                       (MAP (concr_extrTrans g_AA)
                         (CAT_OPTIONS
                           (MAP
                             (λf.
                               OPTION_MAP FST
                               (findNode (λ(i,l). l.frml = f) g_AA))
                             nL.frmls)))`
         >> qabbrev_tac `zpd = ZIP (nL.frmls,ce_lists)`
         >> qabbrev_tac `L =
                      MAP
                       (λf.
                         OPTION_MAP FST
                         (findNode (λ(i,l). l.frml = f) g_AA))
                       node.frmls`
         >> `EVERY IS_SOME L` by (
                       qunabbrev_tac `L` >> fs[] >> simp[EVERY_MEM]
                       >> rpt strip_tac >> fs[MEM_MAP]
                       >> Cases_on `e` >> fs[IS_SOME_DEF]
                       >> `inGBA g node.frmls` by (
                           simp[inGBA_def,EXISTS_MEM] >> qexists_tac `node`
                           >> simp[MEM_MAP,MEM_EQUAL_SET]
                           >> metis_tac[MEM_toAList,SND]
                       )
                       >> `set node.frmls ∈
                            POW (removeStatesSimpl (ltl2vwaa f)).states`
                           by metis_tac[]
                       >> fs[concr2AbstrAA_def]
                       >> `f' ∈ (removeStatesSimpl (ltl2vwaa f)).states`
                          by metis_tac[MEM,IN_POW,SUBSET_DEF]
                       >> `f' ∈ concr2Abstr_states g_AA`
                          by (fs[ALTER_A_component_equality] >> metis_tac[])
                       >> fs[concr2Abstr_states_def,findNode_def]
                       >> rename[`f1 = x1.frml`,`n1 ∈ domain g_AA.nodeInfo`]
                       >> `(λ(i,l). l.frml = f1) (n1,x1)` by fs[]
                       >> metis_tac[FIND_LEMM,NOT_SOME_NONE,MEM_toAList]
                   )
         >> `EVERY IS_SOME
                              (MAP (concr_extrTrans g_AA) (CAT_OPTIONS L))` by (
                       simp[EVERY_MEM] >> rpt strip_tac >> fs[MEM_MAP]
                       >> rename[`MEM some_id (CAT_OPTIONS L)`]
                       >> simp[concr_extrTrans_def]
                       >> Cases_on `lookup some_id g_AA.followers` >> fs[]
                       >-(qunabbrev_tac `L` >> fs[CAT_OPTIONS_MEM,MEM_MAP]
                        >> fs[findNode_def]
                        >> `MEM z (toAList g_AA.nodeInfo)`
                              by metis_tac[FIND_LEMM2]
                        >> Cases_on `z` >> fs[wfg_def]
                        >> rw[]
                        >> metis_tac[MEM_toAList,domain_lookup,wfg_def,
                                     NOT_SOME_NONE]
                         )
                       >- (
                         fs[] >> rpt strip_tac
                         >> Q.HO_MATCH_ABBREV_TAC `IS_SOME H` >> Cases_on `H`
                         >> fs[IS_SOME_DEF]
                         >> `some_id ∈ (domain g_AA.nodeInfo)`
                               by metis_tac[domain_lookup,wfg_def]
                         >> metis_tac[domain_lookup,NOT_SOME_NONE]
                         )
                       )
         >> `LENGTH node.frmls = LENGTH ce_lists` by (
                   qunabbrev_tac `ce_lists`
                   >> qunabbrev_tac `L`
                   >> metis_tac[LENGTH_MAP,CAT_OPTIONS_LENGTH]
                 )
         >> `MAP FST zpd = node.frmls` by (
                     qunabbrev_tac `zpd` >> fs[]
                     >> metis_tac[MAP_ZIP]
                 )
         >> `ALL_DISTINCT (MAP FST zpd)` by metis_tac[frml_ad_def]
         >> Q.HO_MATCH_ABBREV_TAC `GOAL`
         >> rw[]
         >> `!q_i q_nL q q_trns.
                      (findNode (λ(i,l). l.frml = q) g_AA = SOME (q_i,q_nL))
                      ∧ (q_nL.frml = q) ∧ MEM q nL.frmls
                      ∧ concr_extrTrans g_AA q_i = SOME q_trns
                      ==> MEM (q_nL.frml,q_trns) zpd` by (
                        qunabbrev_tac `zpd` >> simp[MEM_ZIP] >> rpt strip_tac
                        >> `?ind_q. EL ind_q nL.frmls = q_nL.frml
                                  ∧ ind_q < LENGTH nL.frmls`
                           by metis_tac[MEM_EL]
                        >> qexists_tac `ind_q` >> fs[]
                        >> qunabbrev_tac `ce_lists` >> rw[]
                        >> `LENGTH nL.frmls =
                             LENGTH (MAP (concr_extrTrans g_AA)
                                         (CAT_OPTIONS L))` by (
                            fs[CAT_OPTIONS_LENGTH]
                        )
                        >> `SOME
                             (EL ind_q (CAT_OPTIONS (MAP (concr_extrTrans g_AA)
                                                        (CAT_OPTIONS L)))) =
                            (EL ind_q (MAP (concr_extrTrans g_AA)
                                          (CAT_OPTIONS L)))` by
                         metis_tac[CAT_OPTIONS_EL]
                        >> `EL ind_q (MAP (concr_extrTrans g_AA)
                                     (CAT_OPTIONS L)) =
                            (concr_extrTrans g_AA (EL ind_q (CAT_OPTIONS L)))`
                            by fs[EL_MAP,LENGTH_MAP]
                        >> `LENGTH L = LENGTH nL.frmls` by (
                            qunabbrev_tac `L`
                            >> fs[LENGTH_MAP]
                        )
                        >> `SOME (EL ind_q (CAT_OPTIONS L)) =
                              EL ind_q L` by metis_tac[CAT_OPTIONS_EL]
                        >> `EL ind_q L = SOME q_i` by (
                            qunabbrev_tac `L` >> simp[EL_MAP]
                        )
                        >> rw[] >> `EL ind_q (CAT_OPTIONS L) = q_i` by fs[]
                        >> metis_tac[SOME_11]
                 )
         >> `{(q,(removeStatesSimpl (ltl2vwaa f)).trans q) |
                         MEM q nL.frmls} =
                      set
                       (MAP (λ(q,d).
                              (q,set (MAP (concr2AbstractEdge (set aP)) d)))
                            zpd)` by (
                     simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                      >- (
                       simp[MEM_MAP]
                       >> `?i nL. findNode (λ(i,l). l.frml = q) g_AA = SOME (i,nL)`
                          by (
                          fs[findNode_def,concr2AbstrAA_def,
                               ALTER_A_component_equality]
                          >> `inGBA g nL.frmls` by (
                              simp[inGBA_def,EXISTS_MEM] >> qexists_tac `nL`
                              >> simp[MEM_MAP,MEM_EQUAL_SET]
                              >> metis_tac[MEM_toAList,SND]
                          )
                          >> `set nL.frmls ∈
                                 POW (concr2Abstr_states g_AA)`
                               by metis_tac[]
                          >> `q ∈ concr2Abstr_states g_AA`
                               by metis_tac[IN_POW,SUBSET_DEF]
                          >> fs[concr2Abstr_states_def]
                          >> rename[`SOME x2 = lookup n1 g_AA.nodeInfo` ]
                          >> rw[]
                          >> `(λ(i,l). l.frml = x2.frml) (n1,x2)` by fs[]
                          >> `∃y. FIND (λ(i,l). l.frml = x2.frml)
                                          (toAList g_AA.nodeInfo) = SOME y`
                              by metis_tac[FIND_LEMM,MEM_toAList]
                          >> qexists_tac `FST y` >> qexists_tac `SND y` >> fs[]
                       )
                       >> rename[`findNode _ g_AA = SOME (q_i,q_nL)`]
                       >> `?q_trns. SOME q_trns = concr_extrTrans g_AA q_i
                             ∧ MEM (q_i,q_nL) (toAList g_AA.nodeInfo)
                             ∧ (q_nL.frml = q)` by (
                           fs[findNode_def]
                           >> `MEM (q_i,q_nL) (toAList g_AA.nodeInfo)
                              ∧ ((λ(i,l). l.frml = q) (q_i,q_nL))`
                              by metis_tac[FIND_LEMM2]
                           >> `IS_SOME (lookup q_i g_AA.followers)` suffices_by (
                               rpt strip_tac >> simp[concr_extrTrans_def] >> fs[]
                               >> Cases_on `lookup q_i g_AA.followers`
                               >> fs[IS_SOME_DEF]
                               >> metis_tac[wfg_def,domain_lookup]
                           )
                           >> Cases_on `lookup q_i g_AA.followers`
                           >> fs[IS_SOME_DEF]
                           >> metis_tac[wfg_def,domain_lookup,MEM_toAList,
                                        NOT_SOME_NONE]
                       )
                       >> qexists_tac `(q,q_trns)` >> simp[]
                       >> fs[concr2AbstrAA_def,ALTER_A_component_equality]
                       >> `?fls. lookup q_i g_AA.followers = SOME fls` by (
                           metis_tac[domain_lookup,MEM_toAList,wfg_def,SOME_11]
                       )
                       >> `∃n cT.
                             concr_extrTrans g_AA q_i = SOME cT
                             ∧ lookup q_i g_AA.nodeInfo = SOME n
                             ∧ set (MAP (concr2AbstractEdge (set aP)) cT) =
                                    concrTrans g_AA (set aP) n.frml`
                         by (IMP_RES_TAC CONCR_EXTRTRANS_LEMM
                             >> first_x_assum (qspec_then `q_i` mp_tac)
                             >> simp[])
                        >> fs[] >> `q_nL = n` by metis_tac[MEM_toAList,SOME_11]
                        >> rw[]
                     )
                      >- (
                       rename[`MEM edge _`] >> fs[MEM_MAP]
                       >> rename[`MEM cE zpd`] >> Cases_on `cE`
                       >> fs[] >> qunabbrev_tac `zpd`
                       >> rename[`MEM (q,q_trans) _`] >> POP_ASSUM mp_tac
                       >> simp[MEM_ZIP] >> rpt strip_tac
                       >- (
                         `inGBA g nL.frmls` by (
                            simp[inGBA_def,EXISTS_MEM] >> qexists_tac `nL`
                            >> simp[MEM_MAP,MEM_EQUAL_SET]
                            >> metis_tac[MEM_toAList,SND]
                         )
                         >> fs[concr2AbstrAA_def,ALTER_A_component_equality]
                         >> `set nL.frmls ∈
                              POW (concr2Abstr_states g_AA)`
                            by metis_tac[]
                         >> `q ∈ concr2Abstr_states g_AA`
                           by metis_tac[IN_POW,SUBSET_DEF,EL_MEM]
                         >> fs[concr2Abstr_states_def]
                         >> rename[`q_i ∈ domain _`,`q = q_nL.frml`]
                         >> `findNode (λ(n,l). l.frml = q) g_AA
                                = SOME (q_i,q_nL)`
                            by metis_tac[UNIQUE_NODE_FIND_LEMM]
                         >> `?q_trns. concr_extrTrans g_AA q_i = SOME q_trns`
                            by (
                             simp[concr_extrTrans_def]
                             >> Cases_on `lookup q_i g_AA.followers` >> fs[]
                             >- metis_tac[wfg_def,NOT_SOME_NONE,domain_lookup]
                             >- metis_tac[]
                         )
                         >> rw[]
                         >> `MEM (q_nL.frml,q_trns) (ZIP (nL.frmls,ce_lists))`
                             by metis_tac[EL_MEM]
                         >> `∃k. k < LENGTH nL.frmls
                               ∧ (q_nL.frml,q_trns) = (EL k nL.frmls,EL k ce_lists)`
                             by metis_tac[MEM_ZIP]
                         >> `EL k nL.frmls = q_nL.frml` by fs[]
                         >> `k = n` by metis_tac[ALL_DISTINCT_EL_IMP]
                         >> fs[]
                         >> `?fls. lookup q_i g_AA.followers = SOME fls`
                            by metis_tac[wfg_def,domain_lookup]
                         >> `∃n cT.
                              concr_extrTrans g_AA q_i = SOME cT
                            ∧ lookup q_i g_AA.nodeInfo = SOME n
                            ∧ set (MAP (concr2AbstractEdge (set aP)) cT) =
                                    concrTrans g_AA (set aP) n.frml`
                           by (IMP_RES_TAC CONCR_EXTRTRANS_LEMM
                               >> first_x_assum (qspec_then `q_i` mp_tac)
                               >> simp[] >> rpt strip_tac
                               >> first_x_assum (qspec_then `set aP` mp_tac)
                               >> fs[]
                              )
                         >> metis_tac[SOME_11]
                       )
                       >- metis_tac[EL_MEM]
                     )
         )
         >> IMP_RES_TAC GBA_TRANS_LEMM
         >> first_x_assum (qspec_then `set aP` mp_tac) >> simp[]
         >> `!ce. MEM ce TRNS ==>
                       (MEM_SUBSET ce.pos aP
                             ∧ MEM_SUBSET ce.neg aP
                             ∧ MEM_SUBSET ce.sucs (graphStates g_AA))` by (
                      qunabbrev_tac `TRNS` >> fs[] >> gen_tac >> strip_tac
                      >> simp[MEM_SUBSET_SET_TO_LIST,SUBSET_DEF]
                      >> rpt strip_tac >> rename[`MEM x _`]
                      >- (`∃l ce. MEM l ce_lists ∧ MEM ce l ∧ MEM x ce.pos`
                            by metis_tac[GBA_TRANS_LEMM3]
                          >> qunabbrev_tac `ce_lists`
                          >> fs[MEM_MAP,CAT_OPTIONS_MEM]
                          >> metis_tac[MEM_SUBSET_SET_TO_LIST,SUBSET_DEF]
                         )
                      >- (`∃l ce. MEM l ce_lists ∧ MEM ce l ∧ MEM x ce.neg`
                            by metis_tac[GBA_TRANS_LEMM3]
                          >> qunabbrev_tac `ce_lists`
                          >> fs[MEM_MAP,CAT_OPTIONS_MEM]
                          >> metis_tac[MEM_SUBSET_SET_TO_LIST,SUBSET_DEF]
                         )
                      >- (`∃l ce. MEM l ce_lists ∧ MEM ce l ∧ MEM x ce.sucs`
                            by metis_tac[GBA_TRANS_LEMM3]
                          >> qunabbrev_tac `ce_lists`
                          >> fs[MEM_MAP,CAT_OPTIONS_MEM]
                          >> qunabbrev_tac `L` >> fs[MEM_MAP] >> Cases_on `z`
                          >> fs[] >> rw[]
                          >> `MEM (q,r) (toAList g_AA.nodeInfo)` by (
                             fs[findNode_def] >> metis_tac[FIND_LEMM2]
                          )
                          >> `?fls. lookup q g_AA.followers = SOME fls`
                                by metis_tac[domain_lookup,MEM_toAList,
                                             wfg_def,SOME_11]
                          >> `∃n cT.
                               (concr_extrTrans g_AA q = SOME cT)
                               ∧ (lookup q g_AA.nodeInfo = SOME n)
                               ∧ (set (MAP (concr2AbstractEdge (set aP)) cT) =
                                  concrTrans g_AA (set aP) n.frml)`
                           by (IMP_RES_TAC CONCR_EXTRTRANS_LEMM
                               >> first_x_assum (qspec_then `q` mp_tac)
                               >> simp[]
                              )
                          >> `l = cT` by metis_tac[SOME_11] >> rw[]
                          >> `concr2AbstractEdge (set aP) ce' ∈
                                    concrTrans g_AA (set aP) n.frml` by (
                             metis_tac[MEM_MAP,SET_EQ_SUBSET,SUBSET_DEF]
                          )
                          >> fs[concr2AbstrAA_def,ALTER_A_component_equality]
                          >> rw[]
                          >> fs[isValidAlterA_def,concr2Abstr_states_def]
                          >> `n.frml ∈ (removeStatesSimpl (ltl2vwaa f)).states`
                             by (rw[] >> metis_tac[domain_lookup])
                          >> Cases_on `concr2AbstractEdge (set aP) ce'`
                          >> fs[]
                          >> `r' ⊆ (removeStatesSimpl (ltl2vwaa f)).states`
                             by metis_tac[]
                          >> rw[] >> simp[graphStates_def,MEM_MAP]
                          >> `r' ⊆
                                {x.frml |
                                 ∃n. (SOME x = lookup n g_AA.nodeInfo)
                                  ∧ (n ∈ domain g_AA.nodeInfo)}` by metis_tac[]
                          >> Cases_on `ce'`
                          >> fs[concr2AbstractEdge_def] >> rw[]
                          >> `x ∈
                                {x.frml |
                                 ∃n. (SOME x = lookup n g_AA.nodeInfo)
                                  ∧ n ∈ domain g_AA.nodeInfo}` by fs[SUBSET_DEF]
                          >> fs[] >> metis_tac[MEM_toAList,SND,FST]
                         )
                  ) >> strip_tac
         >> qunabbrev_tac `GOAL` >> rpt strip_tac
         >- (simp[SET_EQ_SUBSET,SUBSET_DEF] >> strip_tac
          >- (
           rpt strip_tac >> fs[CAT_OPTIONS_MEM,MEM_MAP]
           >> Cases_on `y` >> fs[]
           >> rename[`MEM (eL, s_id) fls`]
           >> simp[gba_trans_def,minimal_elements_def,rrestrict_def]
           >> simp[d_gen_def]
           >> Cases_on `x` >> fs[]
           >> first_x_assum (qspec_then `eL` mp_tac) >> simp[]
           >> strip_tac
           >> first_x_assum (qspec_then `s_nL.frmls` mp_tac) >> simp[]
           >> `(∃s_id s_nL'.
                 MEM (eL,s_id) fls
                 ∧ (lookup s_id G2.nodeInfo = SOME s_nL')
                 ∧ MEM_EQUAL s_nL'.frmls s_nL.frmls)` by (
               qexists_tac `s_id` >> qexists_tac `s_nL`
               >> fs[MEM_EQUAL_SET]
           )
           >> strip_tac
           >> `∃s_list.
               (MEM_EQUAL s_list s_nL.frmls)
               ∧ ∃y.
               ((eL,s_list) = TO_SUCS y)
               ∧ (∃cE. y = W_FINAL cE ∧ MEM cE TRNS)
               ∧ ∀y'.
               (∃cE. y' = W_FINAL cE ∧ MEM cE TRNS) ∧ y ≠ y' ⇒
               ¬concr_min_rel y' y` by metis_tac[EQ_IMP_THM]
           >> rw[]
           >- (
             `(transformLabel (set aP) eL.pos_lab eL.neg_lab,set s_nL.frmls) ∈
                  set
                  (MAP (concr2AbstractEdge (set aP))
                       (gba_trans_concr (MAP SND zpd)))`
               suffices_by metis_tac[]
             >> simp[MEM_MAP] >> qexists_tac `cE`
             >> Cases_on `cE` >> fs[concr2AbstractEdge_def]
             >> qunabbrev_tac `TRNS` >> qunabbrev_tac `TO_SUCS`
             >> qunabbrev_tac `W_FINAL` >> fs[]
             >> `MAP SND zpd = ce_lists` by metis_tac[MAP_ZIP]
             >> fs[] >> rw[] >> metis_tac[MEM_EQUAL_SET]
           )
           >- (rpt strip_tac
               >>  rename[`_ = abstr_ce2`]
               >> `abstr_ce2 ∈
                    set (MAP (concr2AbstractEdge (set aP)) TRNS)` by (
                    IMP_RES_TAC GBA_TRANS_LEMM
                    >> first_x_assum (qspec_then `set aP` mp_tac) >> fs[]
                    >> rpt strip_tac >> qunabbrev_tac `TRNS` >> fs[]
                    >> metis_tac[MAP_ZIP]
                )
               >> POP_ASSUM mp_tac >> simp[MEM_MAP] >> strip_tac
               >> rename[`MEM ce2 TRNS`] >> fs[]
               >> `ce2 = cE \/ ~concr_min_rel (W_FINAL ce2) (W_FINAL cE)`
                   by (
                       first_x_assum (qspec_then `W_FINAL ce2` mp_tac)
                       >> simp[]
                       >> strip_tac
                       >> qunabbrev_tac `W_FINAL` >> fs[]
                       >> Cases_on `ce2 = cE` >> fs[]
                 )
               >- (qunabbrev_tac `W_FINAL` >> qunabbrev_tac `TO_SUCS` >> fs[]
                   >> rw[] >> Cases_on `cE` >> simp[concr2AbstractEdge_def]
                   >> fs[concrEdge_component_equality]
                   >> metis_tac[MEM_EQUAL_SET]
                  )
               >- (
                fs[]
                >> qabbrev_tac `abstrAA = concr2AbstrAA (concrAA g_AA init aP)`
                >> `∀e1_lab e1_sucs e2_lab e2_sucs.
                   MEM_SUBSET ce2.pos aP ∧ MEM_SUBSET ce2.neg aP ∧
                   MEM_SUBSET ce2.sucs (graphStates g_AA) ∧ MEM_SUBSET cE.pos aP ∧
                   MEM_SUBSET cE.neg aP ∧ MEM_SUBSET cE.sucs (graphStates g_AA) ∧
                   ((e1_lab,e1_sucs) = concr2AbstractEdge (set aP) ce2) ∧
                   ((e2_lab,e2_sucs) = concr2AbstractEdge (set aP) cE)
                   ⇒ (((e1_lab,e1_sucs),e2_lab,e2_sucs) ∈
                        tr_less_general
                          {acc_cond abstrAA f | MEM f (MAP FST acc)}
                          (set nL.frmls) ⇔
                        tlg_concr
                        (ce2,get_acc_set acc ce2)
                        (cE,get_acc_set acc cE))` by (
                        HO_MATCH_MP_TAC TLG_CONCR_LEMM >> qexists_tac `f`
                        >> qexists_tac `init` >> fs[] >> metis_tac[]
                )
                 >> fs[]
                 >> first_x_assum (qspec_then `FST abstr_ce2` mp_tac)
                 >> rpt strip_tac
                 >> first_x_assum (qspec_then `SND abstr_ce2` mp_tac)
                 >> rpt strip_tac
                 >> first_x_assum
                     (qspec_then `transformLabel (set aP) eL.pos_lab eL.neg_lab`
                       mp_tac)
                 >> rpt strip_tac
                 >> first_x_assum (qspec_then `set s_nL.frmls` mp_tac)
                 >> `(transformLabel (set aP) eL.pos_lab eL.neg_lab,
                     set s_nL.frmls) =
                        concr2AbstractEdge (set aP) cE` by (
                    qunabbrev_tac `W_FINAL` >> qunabbrev_tac `TO_SUCS` >> fs[]
                    >> rw[] >> Cases_on `cE` >> simp[concr2AbstractEdge_def]
                    >> fs[concrEdge_component_equality]
                    >> metis_tac[MEM_EQUAL_SET]
                )
                 >> simp[] >> strip_tac
                 >> `{acc_cond (concr2AbstrAA (concrAA g_AA init aP)) f' |
                      MEM f' (MAP FST acc)} =
                     {acc_cond (concr2AbstrAA (concrAA g_AA init aP)) f |
                       f | f ∈ (concr2AbstrAA (concrAA g_AA init aP)).final}`
                by (
                 `∀f. MEM f (MAP FST acc) ⇔ f ∈ concr2Abstr_final g_AA`
                    by metis_tac[VALID_ACC_LEMM]
                 >> qunabbrev_tac `abstrAA` >> fs[]
                 >> simp[SET_EQ_SUBSET,SUBSET_DEF,concr2AbstrAA_def]
                )
                >> qunabbrev_tac `W_FINAL` >> qunabbrev_tac `TO_SUCS`
                >> fs[concr_min_rel_def]
                >- (rw[] >> metis_tac[all_acc_cond_def])
                >- (Cases_on `cE` >> Cases_on `ce2`
                    >> simp[concr2AbstractEdge_def]
                    >> fs[concrEdge_component_equality]
                    >> `!x y. MEM_EQUAL x y ==>
                                  MEM_SUBSET x y ∧ MEM_SUBSET y x`
                          by metis_tac[MEM_EQUAL_SET,MEM_SUBSET_SET_TO_LIST,
                                       SET_EQ_SUBSET]
                    >> simp[SET_EQ_SUBSET] >> rpt strip_tac
                    >- metis_tac[TRANSFORMLABEL_SUBSET]
                    >- metis_tac[TRANSFORMLABEL_SUBSET]
                    >- metis_tac[MEM_EQUAL_SET,SET_EQ_SUBSET]
                    >- metis_tac[MEM_EQUAL_SET,SET_EQ_SUBSET]
                    )
                 >- (rw[] >> Cases_on `cE` >> Cases_on `ce2`
                     >> simp[concr2AbstractEdge_def]
                     >> fs[concrEdge_component_equality,MEM_EQUAL_SET]
                     >> rename[`_ (set aP) pos1 neg1 = _ (set aP) pos2 neg2`]
                     >> `pos1 = (concrEdge pos1 neg1 l1).pos` by fs[]
                     >> `neg1 = (concrEdge pos1 neg1 l1).neg` by fs[]
                     >> `pos2 = (concrEdge pos2 neg2 l1').pos` by fs[]
                     >> `neg2 = (concrEdge pos2 neg2 l1').neg` by fs[]
                     >> metis_tac[TRNS_IS_EMPTY_LEMM,MEM_SUBSET_SET_TO_LIST]
                    )
                )
              )
            )
          >- (rpt strip_tac >> simp[CAT_OPTIONS_MEM,MEM_MAP] >> POP_ASSUM mp_tac
              >> simp[gba_trans_def,minimal_elements_def,rrestrict_def,d_gen_def]
              >> strip_tac
              >> rename[`(a,sucs) ∈ d_conj_set _ _`] >> rw[]
              >> `(a,sucs) ∈
                  set
                  (MAP (concr2AbstractEdge (set aP))
                       (gba_trans_concr (MAP SND zpd)))` by metis_tac[]
              >> POP_ASSUM mp_tac >> simp[MEM_MAP] >> strip_tac
              >> rename[`MEM ce (gba_trans_concr _)`]
              >> qabbrev_tac `eL =
                     edgeLabelGBA ce.pos ce.neg (get_acc_set acc ce)`
              >> first_x_assum (qspec_then `eL` mp_tac) >> simp[]
              >> strip_tac
              >> first_x_assum (qspec_then `ce.sucs` mp_tac) >> simp[]
              >> strip_tac
              >> `∃s_list.
                   MEM_EQUAL s_list ce.sucs
                   ∧ ∃y.
                     ((eL,s_list) = TO_SUCS y)
                     ∧ (∃cE. y = W_FINAL cE ∧ MEM cE TRNS)
                     ∧ ∀y'.
                     (∃cE. y' = W_FINAL cE ∧ MEM cE TRNS) ∧ y ≠ y' ⇒
                     ¬concr_min_rel y' y` suffices_by (
                 strip_tac
                 >> `(∃s_id s_nL.
                       (MEM (eL,s_id) fls ∧ lookup s_id G2.nodeInfo = SOME s_nL)
                       ∧ MEM_EQUAL s_nL.frmls ce.sucs)` by metis_tac[]
                 >> qunabbrev_tac `W_FINAL` >> qunabbrev_tac `TO_SUCS` >> fs[]
                 >> qexists_tac `(eL,s_id)` >> simp[]
                 >> Cases_on `ce` >> simp[concr2AbstractEdge_def]
                 >> fs[concrEdge_component_equality]
                 >> `l = cE.pos ∧ l0 = cE.neg` by metis_tac[]
                 >> fs[MEM_EQUAL_SET]
               )
              >> qexists_tac `ce.sucs` >> fs[MEM_EQUAL_SET]
              >> qexists_tac `(ce,get_acc_set acc ce)` >> fs[]
              >> qunabbrev_tac `TO_SUCS` >> qunabbrev_tac `W_FINAL` >> fs[]
              >> rpt strip_tac
              >- (`MAP SND zpd = ce_lists` by metis_tac[MAP_ZIP]
                  >> qunabbrev_tac `TRNS` >> fs[]
                 )
              >- (rename[`MEM cE2 TRNS`]
                  >> rename[`concr_min_rel y1 (ce,_)`] >> Cases_on `y1`
                  >> `~(cE2 = ce)` by (
                       rw[] >> fs[] >> CCONTR_TAC >> rw[]
                   )
                >> first_x_assum
                       (qspec_then `concr2AbstractEdge (set aP) cE2` mp_tac)
                >> Q.HO_MATCH_ABBREV_TAC `(Q1 ==> Q2) ==> F`
                >> `Q2 ==> F` by (
                      qunabbrev_tac `Q2` >> simp[] (* >> Cases_on `y` *)
                      >> `~(ce = cE2)` by metis_tac[]
                      >> Cases_on `~MEM_EQUAL cE2.sucs ce.sucs`
                      >- (Cases_on `ce` >> fs[]
                          >> Cases_on `cE2` >> simp[concr2AbstractEdge_def]
                          >> fs[MEM_EQUAL_SET,concrEdge_component_equality]
                          >> rw[] >> metis_tac[]
                         )
                      >- (Cases_on `~ trns_is_empty ce ∧ ~ trns_is_empty cE2`
                       >- (`MEM ce TRNS` by metis_tac[MAP_ZIP]
                           >> `∀x. MEM x ce.pos ∨ MEM x cE2.pos
                                 ∨ MEM x ce.neg ∨ MEM x cE2.neg ⇒ x ∈ set aP` by (
                              metis_tac[MEM_SUBSET_SET_TO_LIST,SUBSET_DEF,MEM]
                           )
                           >> `~(transformLabel (set aP) ce.pos ce.neg =
                                transformLabel (set aP) cE2.pos cE2.neg)`
                              suffices_by (Cases_on `ce` >> Cases_on `cE2`
                                           >> simp[concr2AbstractEdge_def]
                                          )
                           >> HO_MATCH_MP_TAC TRANSFORMLABEL_LEMM
                           >> simp[] >> fs[concr_min_rel_def]
                           >> rw[] >> metis_tac[MEM_EQUAL_SET]
                          )
                       >- (`MEM ce TRNS` by metis_tac[MAP_ZIP]
                           >> `(concrEdge cE2.pos cE2.neg cE2.sucs).pos = cE2.pos
                             ∧ (concrEdge cE2.pos cE2.neg cE2.sucs).neg = cE2.neg`
                               by fs[]
                           >> `set ce.pos ⊆ set aP
                             ∧ set ce.neg ⊆ set aP
                             ∧ set cE2.pos ⊆ set aP
                             ∧ set cE2.neg ⊆ set aP`
                                by metis_tac[MEM_SUBSET_SET_TO_LIST]
                           >> `trns_is_empty ce = ~trns_is_empty cE2` by (
                                fs[concr_min_rel_def] >> metis_tac[]
                           )
                           >> `~(transformLabel (set aP) ce.pos ce.neg
                                  = transformLabel (set aP) cE2.pos cE2.neg)`
                                suffices_by (Cases_on `ce` >> Cases_on `cE2`
                                             >> simp[concr2AbstractEdge_def])
                           >> metis_tac[TRNS_IS_EMPTY_LEMM]
                          )
                  )
                  )
                >> `Q1` suffices_by metis_tac[]
                >> qunabbrev_tac `Q1` >> fs[]
                >> (conj_tac
                >- (qunabbrev_tac `TRNS`
                    >> `MAP SND zpd = ce_lists` by metis_tac[MAP_ZIP]
                    >> metis_tac[MEM_MAP]
                   )
                >- (conj_tac
                 >- (`MEM ce TRNS` by metis_tac[MAP_ZIP]
                     >> `tlg_concr (cE2,get_acc_set acc cE2)
                         (ce,get_acc_set acc ce)` by
                        (fs[concr_min_rel_def] >> rw[])
                     >> qabbrev_tac `abstrAA =
                          concr2AbstrAA (concrAA g_AA init aP)`
                     >> `∀e1_lab e1_sucs e2_lab e2_sucs.
                      MEM_SUBSET cE2.pos aP ∧ MEM_SUBSET cE2.neg aP ∧
                      MEM_SUBSET cE2.sucs (graphStates g_AA) ∧ MEM_SUBSET ce.pos aP ∧
                      MEM_SUBSET ce.neg aP ∧ MEM_SUBSET ce.sucs (graphStates g_AA) ∧
                      ((e1_lab,e1_sucs) = concr2AbstractEdge (set aP) cE2) ∧
                      ((e2_lab,e2_sucs) = concr2AbstractEdge (set aP) ce)
                      ⇒ (((e1_lab,e1_sucs),e2_lab,e2_sucs) ∈
                        tr_less_general
                          {acc_cond abstrAA f | MEM f (MAP FST acc)}
                          (set nL.frmls) ⇔
                        tlg_concr (cE2,get_acc_set acc cE2)
                                  (ce,get_acc_set acc ce))` by (
                        HO_MATCH_MP_TAC TLG_CONCR_LEMM >> qexists_tac `f`
                        >> qexists_tac `init` >> fs[] >> metis_tac[]
                        )
                     >> fs[]
                     >> first_x_assum
                           (qspec_then `transformLabel (set aP) cE2.pos cE2.neg`
                             mp_tac)
                     >> simp[] >> strip_tac
                     >> first_x_assum (qspec_then `set cE2.sucs` mp_tac)
                     >> simp[] >> strip_tac
                     >> first_x_assum
                           (qspec_then `transformLabel (set aP) ce.pos ce.neg`
                            mp_tac)
                     >> simp[] >> strip_tac
                     >> first_x_assum (qspec_then `set ce.sucs` mp_tac)
                     >> simp[] >> strip_tac
                     >> fs[all_acc_cond_def]
                     >> `{acc_cond (concr2AbstrAA (concrAA g_AA init aP)) f' |
                           MEM f' (MAP FST acc)} =
                         {acc_cond (concr2AbstrAA (concrAA g_AA init aP)) f |
                           f | f ∈ (concr2AbstrAA (concrAA g_AA init aP)).final}`
                    by (
                     `∀f. MEM f (MAP FST acc) ⇔ f ∈ concr2Abstr_final g_AA`
                        by metis_tac[VALID_ACC_LEMM]
                     >> simp[SET_EQ_SUBSET,SUBSET_DEF,concr2AbstrAA_def]
                     >> rpt strip_tac >> qexists_tac `f'` >> simp[]
                     >> qunabbrev_tac `abstrAA` >> fs[concr2AbstrAA_def]
                      )
                    >> Cases_on `ce` >> Cases_on `cE2`
                    >> fs[concr2AbstractEdge_def]
                    >> qunabbrev_tac `abstrAA` >> fs[concr2AbstrAA_def]
                    )
                 >- (qunabbrev_tac `TRNS`
                     >> `MAP SND zpd = ce_lists` by metis_tac[MAP_ZIP]
                     >> metis_tac[MEM_MAP]
                    )
                   ))
                 )
             )
            )
         >- (first_x_assum (qspec_then `eL` mp_tac) >> simp[]
             >> strip_tac
             >> `s_id ∈ domain G2.nodeInfo` by metis_tac[]
             >> `?s_nL. lookup s_id G2.nodeInfo = SOME s_nL`
                by metis_tac[domain_lookup]
             >> first_x_assum (qspec_then `s_nL.frmls` mp_tac) >> simp[]
             >> strip_tac
             >> `∃s_id s_nL'.
                  MEM (eL,s_id) fls
                  ∧ lookup s_id G2.nodeInfo = SOME s_nL'
                  ∧ MEM_EQUAL s_nL'.frmls s_nL.frmls` by (
                  metis_tac[MEM_EQUAL_SET]
              )
             >> `∃s_list.
                  MEM_EQUAL s_list s_nL.frmls ∧
                  ∃y.
                  ((eL,s_list) = TO_SUCS y) ∧ (∃cE. y = W_FINAL cE ∧ MEM cE TRNS)
                  ∧ ∀y'.
                  (∃cE. y' = W_FINAL cE ∧ MEM cE TRNS) ∧ y ≠ y' ⇒
                  ¬concr_min_rel y' y` by metis_tac[]
             >> qunabbrev_tac `W_FINAL` >> qunabbrev_tac `TO_SUCS`
             >> Cases_on `y` >> fs[]
            )
         >- (first_x_assum (qspec_then `eL` mp_tac) >> simp[]
             >> strip_tac
             >> `s_id ∈ domain G2.nodeInfo` by metis_tac[]
             >> `?s_nL. lookup s_id G2.nodeInfo = SOME s_nL`
                by metis_tac[domain_lookup]
             >> first_x_assum (qspec_then `s_nL.frmls` mp_tac) >> simp[]
             >> strip_tac
             >> `∃s_id s_nL'.
                  MEM (eL,s_id) fls
                  ∧ lookup s_id G2.nodeInfo = SOME s_nL'
                  ∧ MEM_EQUAL s_nL'.frmls s_nL.frmls` by (
                  metis_tac[MEM_EQUAL_SET]
              )
             >> `∃s_list.
                  MEM_EQUAL s_list s_nL.frmls ∧
                  ∃y.
                  ((eL,s_list) = TO_SUCS y) ∧ (∃cE. y = W_FINAL cE ∧ MEM cE TRNS)
                  ∧ ∀y'.
                  (∃cE. y' = W_FINAL cE ∧ MEM cE TRNS) ∧ y ≠ y' ⇒
                  ¬concr_min_rel y' y` by metis_tac[]
             >> qunabbrev_tac `W_FINAL` >> qunabbrev_tac `TO_SUCS`
             >> Cases_on `y` >> fs[]
            )
         >- (first_x_assum (qspec_then `eL` mp_tac) >> simp[]
             >> strip_tac
             >> first_x_assum (qspec_then `s_nL.frmls` mp_tac) >> simp[]
             >> strip_tac
             >> `∃s_id s_nL'.
                  MEM (eL,s_id) fls
                  ∧ (lookup s_id G2.nodeInfo = SOME s_nL')
                  ∧ MEM_EQUAL s_nL'.frmls s_nL.frmls` by (
                  metis_tac[MEM_EQUAL_SET]
              )
             >> `∃s_list.
                  (MEM_EQUAL s_list s_nL.frmls) ∧
                  ∃y.
                  ((eL,s_list) = TO_SUCS y) ∧ (∃cE. y = W_FINAL cE ∧ MEM cE TRNS)
                  ∧ ∀y'.
                  (∃cE. y' = W_FINAL cE ∧ MEM cE TRNS) ∧ y ≠ y' ⇒
                  ¬concr_min_rel y' y` by metis_tac[]
             >> qunabbrev_tac `W_FINAL` >> qunabbrev_tac `TO_SUCS`
             >> Cases_on `y` >> fs[]
             >> rw[] >> qunabbrev_tac `TRNS`
             >> `get_acc_set acc cE =
                  get_acc_set acc (concrEdge cE.pos cE.neg s_nL.frmls)` by (
                  HO_MATCH_MP_TAC GET_ACC_SET_LEMM
                  >> Cases_on `cE` >> simp[concrEdge_component_equality]
                  >> fs[MEM_EQUAL_SET]
              )
             >> metis_tac[]
            )
     )
     >- (`id2 ∈ domain G2.nodeInfo` by metis_tac[domain_lookup]
         >> `id2 ∈ (set new_ids ∪ domain g.nodeInfo)` by metis_tac[]
         >> fs[IN_UNION]
         >- (`lookup id2 G2.followers = SOME []` by metis_tac[]
             >> rw[] >> fs[] >> rw[] >> fs[]
            )
         >- (fs[trns_correct_def,final_correct_def,aP_correct_def]
             >> rpt strip_tac
             >- (simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
              >- (fs[CAT_OPTIONS_MEM,MEM_MAP]
                  >> Cases_on `y` >> fs[]
                  >> `lookup id2 g.nodeInfo = SOME nL` by metis_tac[]
                  >> `lookup id2 g.followers = SOME fls` by metis_tac[]
                  >> `r ∈ domain g.nodeInfo` by metis_tac[]
                  >> `MEM x
                      (CAT_OPTIONS
                        (MAP
                          (λ(eL,i).
                            do
                            s_nL <- lookup i g.nodeInfo;
                           SOME
                               (transformLabel (set aP) eL.pos_lab
                                               eL.neg_lab,set s_nL.frmls)
                               od) fls))` by (
                       simp[CAT_OPTIONS_MEM,MEM_MAP]
                       >> qexists_tac `(q,r)` >> fs[]
                   )
                  >> metis_tac[]
                 )
              >- (`MEM x
                     (CAT_OPTIONS
                        (MAP
                             (λ(eL,i).
                               do
                               s_nL <- lookup i g.nodeInfo;
                              SOME
                                  (transformLabel (set aP) eL.pos_lab
                                                  eL.neg_lab,set s_nL.frmls)
                                  od) fls))` by metis_tac[]
                  >> fs[CAT_OPTIONS_MEM,MEM_MAP]
                  >> qexists_tac `y` >> fs[] >> Cases_on `y` >> fs[]
                  >> `r ∈ domain g.nodeInfo` by metis_tac[]
                  >> metis_tac[domain_lookup]
                 )
                )
            >- metis_tac[]
            >- metis_tac[]
            >- metis_tac[]
            )
        )
    )
    >> rpt conj_tac
    >- metis_tac[]
    >- fs[expandGBA_def]
    >- (rpt strip_tac
        >- (`domain g.nodeInfo ⊆ domain G2.nodeInfo` by metis_tac[SUBSET_UNION]
            >> metis_tac[SUBSET_DEF]
           )
        >- metis_tac[domain_lookup]
       )
    >- (rpt strip_tac
        >- (`~(i = id)` by metis_tac[]
             >> metis_tac[]
           )
        >- (`id ∈ domain g.nodeInfo` by metis_tac[]
            >> fs[wfg_def]
            >> `~(g.next <= id)` by metis_tac[]
            >> `~(id = i)` by metis_tac[]
            >> metis_tac[]
           )
       )
    >- metis_tac[]
    >- metis_tac[]
    >- metis_tac[]
    >- fs[all_distinct_nub]
    >- (fs[frml_ad_def] >> rpt strip_tac
        >> `i ∈ (set new_ids ∪ domain g.nodeInfo)` by metis_tac[]
        >> fs[UNION_DEF]
        >- (`MEM n.frmls NEW_NODES` by metis_tac[SOME_11]
            >> qunabbrev_tac `NEW_NODES` >> qunabbrev_tac `TRNS`
            >> fs[MEM_MAP,MEM_FILTER,ONLY_MINIMAL_MEM]
            >> qabbrev_tac `L =
                CAT_OPTIONS
                 (MAP (concr_extrTrans g_AA)
                  (CAT_OPTIONS
                   (MAP
                        (λf.
                             OPTION_MAP FST
                             (findNode (λ(i,l). l.frml = f) g_AA))
                        node.frmls)))`
            >> qunabbrev_tac `L` >> fs[CAT_OPTIONS_MEM,MEM_MAP]
            >> metis_tac[GBA_TRANS_LEMM1]
           )
       >- metis_tac[]
       )
    >- (rpt strip_tac >> rename[`lookup id2 _`]
        >> Cases_on `id = id2` >> fs[]
        >- metis_tac[]
        >- (fs[wfg_def]
            >> `id2 ∈ (set new_ids ∪ domain g.nodeInfo)`
                 by metis_tac[domain_lookup]
            >> fs[IN_UNION]
            >- (`fls = []` by metis_tac[SOME_11]
                >> fs[] >> rw[]
               )
            >- (`lookup id2 g.followers = SOME fls` by metis_tac[]
                >> `id2 ∈ domain g.nodeInfo` by metis_tac[]
                >> metis_tac[UNION_SUBSET,SUBSET_DEF]
               )
           )
       )
   )
  );

val EXPGBA_CORRECT_LEMM = store_thm
  ("EXPGBA_CORRECT_LEMM",
   ``!f init aP g_AA abstrAA.
    (expandAuto_init f = SOME (concrAA g_AA init aP))
    ∧ (abstrAA = concr2AbstrAA (concrAA g_AA init aP))
    ==>
      case expandGBA_init (concrAA g_AA init aP) of
        | NONE => F
        | SOME c_gba =>
          (concr2AbstrGBA c_gba =
             removeStatesSimpl (vwaa2gba abstrAA))``,
   fs[] >> rpt strip_tac >> simp[expandGBA_init_def]
   >> `(wfg g_AA) ∧ (until_iff_final g_AA) ∧ (unique_node_formula g_AA)
     ∧ (flws_sorted g_AA)` by (
       fs[expandAuto_init_def]
       >> qabbrev_tac `G =
            FOLDR (λs g. addFrmlToGraph g s)
                  (empty:(α nodeLabelAA,α edgeLabelAA) gfg)
                  (nub (FLAT (tempDNF_concr f)))`
       >> qabbrev_tac `FS = nub (FLAT (tempDNF_concr f))`
       >> `wfg G
          ∧ (wfg G
             ==> (unique_node_formula G ∧ flws_sorted G
               ∧ (!f. MEM f FS ==> MEM f (graphStates G))))
          ∧ (until_iff_final G)`
           suffices_by metis_tac[EXP_GRAPH_WFG_AND_SOME,SOME_11]
       >> qunabbrev_tac `G` >> rpt strip_tac >> fs[]
       >- metis_tac[empty_is_wfg,ADDFRML_FOLDR_LEMM]
       >- metis_tac[UNIQUE_NODE_FORM_EMPTY,ADDFRML_FOLDR_LEMM,empty_is_wfg]
       >- metis_tac[FLWS_SORTED_EMPTY,ADDFRML_FOLDR_LEMM,empty_is_wfg]
       >- (rename[`MEM f _`]
           >> Q.HO_MATCH_ABBREV_TAC `MEM f (graphStates G)`
           >> `set (graphStates G) = set FS ∪ {}`
             by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg,GRAPHSTATES_EMPTY,
                          LIST_TO_SET,UNION_COMM]
           >> fs[]
          )
       >- (`until_iff_final (empty:(α nodeLabelAA, α edgeLabelAA) gfg)`
             by (
                simp[empty_def,until_iff_final_def] >> rpt strip_tac
                >> metis_tac[lookup_def,NOT_SOME_NONE]
           )
           >> metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg])
   )
   >> qabbrev_tac `addedInit:(α nodeLabelGBA, α edgeLabelGBA) gfg =
          FOLDR (λn g. addNodeToGBA g n) empty
           (MAP
             (λi_list.
               MAP (λl. l.frml)
               (CAT_OPTIONS
                    (MAP (λi. lookup i g_AA.nodeInfo)
                         (nub i_list)))) init)`
   >> qabbrev_tac `final_trans =
        FOLDR
             (λ(id,x) sF.
               case concr_extrTrans g_AA id of
                   NONE => sF
                 | SOME c_t => if is_until x then (x,c_t)::sF else sF) []
             (graphStatesWithId g_AA)`
   >> `!i. MEM i (MAP FST (toAList addedInit.nodeInfo))
             ==> (i ∈ domain addedInit.nodeInfo)` by (
       rpt strip_tac >> qunabbrev_tac `addedInit` >> fs[MEM_MAP]
       >> Cases_on `y` >> fs[]
       >> metis_tac[MEM_toAList,domain_lookup]
   )
   >> `wfg addedInit` by (
       qunabbrev_tac `addedInit` >> fs[]
       >> `!l. wfg (FOLDR (λn g. addNodeToGBA g n)
                          (empty:(α nodeLabelGBA, α edgeLabelGBA) gfg)
                          l)` by (
           Induct_on `l` >> fs[] >> rpt strip_tac
           >> metis_tac[ADDNODE_GBA_WFG]
       )
       >> metis_tac[]
   )
   >> IMP_RES_TAC EXPGBA_SOME_WFG >> first_x_assum (qspec_then `g_AA` mp_tac)
   >> rpt strip_tac >> first_x_assum (qspec_then `final_trans` mp_tac) >> simp[]
   >> rpt strip_tac >> fs[] >> simp[concr2AbstrGBA_def,vwaa2gba_def]
   >> `frml_ad addedInit` by (
       qunabbrev_tac `addedInit` >> fs[]
       >> Q.HO_MATCH_ABBREV_TAC `frml_ad (P init)`
       >> `!ls. frml_ad (P ls) ∧ wfg (P ls)` by (
           Induct_on `ls` >> fs[]
           >- (qunabbrev_tac `P` >> simp[frml_ad_def] >> rpt strip_tac
               >> fs[empty_def]
              )
           >- (rpt strip_tac
               >- (
               qunabbrev_tac `P` >> simp[FOLDR]
               >> Q.HO_MATCH_ABBREV_TAC `frml_ad (addNodeToGBA G (p h))`
               >> fs[]
               >> simp[addNodeToGBA_def]
               >> Cases_on `inGBA G (p h)` >> simp[addNode_def]
               >> simp[frml_ad_def] >> rpt gen_tac
               >> Cases_on `i = G.next`
               >- (rpt strip_tac
                   >> `n = nodeLabelGBA (p h)` by metis_tac[lookup_insert,SOME_11]
                   >> qunabbrev_tac `p` >> fs[]
                   >> `!l:(num option) list.
                          ALL_DISTINCT l
                          ==> ALL_DISTINCT (CAT_OPTIONS l)` by (
                     Induct_on `l` >> fs[CAT_OPTIONS_def] >> rpt strip_tac
                     >> Cases_on `h'` >> simp[CAT_OPTIONS_def]
                     >> simp[CAT_OPTIONS_MEM]
                   )
                   >> qabbrev_tac `frml_diff =
                         λl. !x1 x2. (MEM x1 l ∧ MEM x2 l)
                             ==> ~(x1 = x2) ==> ~(x1.frml = x2.frml)`
                   >> `!l. ALL_DISTINCT l ==>
                            (ALL_DISTINCT
                             (CAT_OPTIONS
                                  (MAP (λi. lookup i g_AA.nodeInfo) l))
                             ∧ frml_diff
                                (CAT_OPTIONS
                                  (MAP (λi. lookup i g_AA.nodeInfo) l)))` by (
                    Induct_on `l` >> qunabbrev_tac `frml_diff`
                    >> fs[ALL_DISTINCT,CAT_OPTIONS_def]
                    >> gen_tac >> strip_tac
                    >> rpt strip_tac
                    >-(rename[`~MEM h l`]
                    >> Cases_on `lookup h g_AA.nodeInfo` >> fs[CAT_OPTIONS_def]
                    >> CCONTR_TAC >> fs[CAT_OPTIONS_MEM,MEM_MAP]
                    >> rename[`SOME x = lookup i g_AA.nodeInfo`]
                    >> Cases_on `MEM i l` >> fs[unique_node_formula_def]
                    >> `MEM (h,x.frml) (graphStatesWithId g_AA)` by (
                        metis_tac[GRAPH_STATES_WITH_ID_LEMM,MEM_toAList]
                    )
                    >> `MEM (i,x.frml) (graphStatesWithId g_AA)` by (
                            metis_tac[GRAPH_STATES_WITH_ID_LEMM,MEM_toAList]
                    )
                    >> metis_tac[]
                      )
                    >- (rename[`~MEM h l`]
                        >> Cases_on `lookup h g_AA.nodeInfo` >> fs[CAT_OPTIONS_def]
                        >> fs[CAT_OPTIONS_MEM]
                        >> rw[] >> fs[MEM_MAP]
                        >> metis_tac[GRAPH_STATES_WITH_ID_LEMM,
                                     MEM_toAList,unique_node_formula_def]
                       )
                    )
                   >> `ALL_DISTINCT
                          (CAT_OPTIONS
                          (MAP (λi. lookup i g_AA.nodeInfo) (nub h)))`
                      by metis_tac[all_distinct_nub]
                   >> `!s. (ALL_DISTINCT s ∧ frml_diff s)
                          ==> ALL_DISTINCT (MAP (λl. l.frml) s)` by (
                       Induct_on `s` >> fs[ALL_DISTINCT] >> rpt strip_tac
                       >> qunabbrev_tac `frml_diff` >> fs[MEM_MAP]
                       >> metis_tac[]
                   )
                   >> metis_tac[all_distinct_nub]
                  )
               >- (rpt strip_tac
                   >> `lookup i G.nodeInfo = SOME n` by metis_tac[lookup_insert,SOME_11]
                   >> fs[frml_ad_def] >> metis_tac[]
                  )
                )
               >- (qunabbrev_tac `P` >> simp[FOLDR]
                   >> Q.HO_MATCH_ABBREV_TAC `wfg (addNodeToGBA G (p h))`
                   >> metis_tac[ADDNODE_GBA_WFG]
                  )
              )
       )
       >> metis_tac[]
   )
   >> `removeStatesSimpl (ltl2vwaa f) =
          concr2AbstrAA (concrAA g_AA init aP)` by (
       `∀φ.
          case expandAuto_init φ of
              NONE => F
            | SOME concrA =>
              concr2AbstrAA concrA = removeStatesSimpl (ltl2vwaa φ)`
         by metis_tac[EXP_WAA_CORRECT_LEMM]
       >> first_x_assum (qspec_then `f` mp_tac) >> simp[]
   )
   >> `isVeryWeakAlterA (concr2AbstrAA (concrAA g_AA init aP))` by (
       metis_tac[REDUCE_STATE_IS_WEAK, LTL2WAA_ISWEAK,
                 LTL2WAA_ISVALID]
   )
   >> simp[gbaSimplTheory.removeStatesSimpl_def,GBA_component_equality]
   >> qabbrev_tac `abstrAA = removeStatesSimpl (ltl2vwaa f)`
   >> `set aP = props f` by (
       fs[ltl2vwaa_def,ltl2vwaa_free_alph_def,removeStatesSimpl_def]
       >> qunabbrev_tac `abstrAA` >> fs[concr2AbstrAA_def]
       >> metis_tac[POW_11]
   )
   >> `(∀id cT.
         (concr_extrTrans g_AA id = SOME cT)
         ==> ∀ce. MEM ce cT ⇒ MEM_SUBSET ce.pos aP ∧ MEM_SUBSET ce.neg aP)` by (
       rpt gen_tac >> simp[concr_extrTrans_def]
       >> Cases_on `lookup id g_AA.followers` >> simp[] >> strip_tac
       >> strip_tac >> strip_tac
       >> Q.HO_MATCH_ABBREV_TAC `GOAL` >> rw[]
       >> fs[MEM_APPEND,CAT_OPTIONS_MEM,MEM_MAP]
       >- (Cases_on `grp` >> fs[] >> rename[`MEM (edge::sucs) _`]
           >> Cases_on `edge` >> fs[]
           >> `MEM (q,r) (CAT_OPTIONS
                           (MAP
                            (λ(eL,id).
                              case lookup id g_AA.nodeInfo of
                                  NONE => NONE
                                | SOME n => SOME (eL,n.frml)) x))` by (
                Q.HO_MATCH_ABBREV_TAC `MEM (q,r) L`
                >> `MEM (q,r) (FLAT
                              (GROUP_BY
                               (λ(eL1,f1) (eL2,f2). eL1.edge_grp = eL2.edge_grp)
                                L))` suffices_by metis_tac[GROUP_BY_FLAT]
                >> simp[MEM_FLAT] >> qexists_tac `((q,r)::sucs)`
                >> fs[]
            )
           >> fs[CAT_OPTIONS_MEM,MEM_MAP] >> rename[`MEM edge x`]
           >> Cases_on `edge` >> fs[] >> rename[`MEM (eL,id) x`]
           >> Cases_on `lookup id g_AA.nodeInfo` >> fs[] >> rw[]
           >> IMP_RES_TAC EXP_WAA_AP >> qunabbrev_tac `GOAL`
           >> fs[domain_lookup]
           >> `MEM eL (MAP FST x)` by metis_tac[MEM_MAP,FST]
           >> metis_tac[]
          )
       >- (IMP_RES_TAC EXP_WAA_AP >> qunabbrev_tac `GOAL`
           >> fs[concrEdge_component_equality]
          )
   )
   >> Q.HO_MATCH_ABBREV_TAC `STATES ∧ INIT ∧ TRANS ∧ FINAL ∧ ALPH`
   >> `valid_acc aP g_AA final_trans` by (
       simp[valid_acc_def] >> rpt strip_tac
       >- (
        qunabbrev_tac `final_trans`
        >> Q.HO_MATCH_ABBREV_TAC `GOAL`
        >> `!L.
       (!i h. MEM (i,h) L ==> MEM (i,h) (graphStatesWithId g_AA))
       ==> MEM (f',f_trns) (
           FOLDR
               (λ(id,x) sF.
                 case concr_extrTrans g_AA id of
                     NONE => sF
                   | SOME c_t => if is_until x then (x,c_t)::sF else sF)
               []
               L
       ) ==> GOAL` by (
            qunabbrev_tac `GOAL` >> Induct_on `L` >> fs[] >> rpt strip_tac
            >> Cases_on `h` >> fs[]
            >> `MEM (q,r) (graphStatesWithId g_AA)` by fs[]
            >> Cases_on `concr_extrTrans g_AA q` >> fs[]
            >> Cases_on `is_until r` >> fs[] >> qexists_tac `q`
            >> fs[graphStatesWithId_def,MEM_MAP] >> Cases_on `y`
            >> fs[] >> rw[] >> rename[`MEM (id,nL) (toAList g_AA.nodeInfo)`]
            >> qexists_tac `nL` >> strip_tac
            >- metis_tac[UNIQUE_NODE_FIND_LEMM,MEM_toAList,SOME_11]
            >- (rpt strip_tac >> metis_tac[MEM_SUBSET_SET_TO_LIST])
        )
        >> qunabbrev_tac `GOAL` >> metis_tac[MEM]
       )
       >- (
        qunabbrev_tac `final_trans` >> fs[graphStates_def,MEM_MAP]
        >> Cases_on `y` >> rename[`MEM (id,nL) (toAList g_AA.nodeInfo)`]
        >> `?f_trns. concr_extrTrans g_AA id = SOME f_trns` by (
            simp[concr_extrTrans_def]
            >> `?edgs. lookup id g_AA.followers = SOME edgs` by (
                fs[wfg_def]
                >> `id ∈ domain g_AA.nodeInfo`
                     by metis_tac[MEM_toAList,domain_lookup]
                >> metis_tac[domain_lookup]
                >> fs[] >> metis_tac[MEM_toAList]
            )
            >> fs[] >> metis_tac[MEM_toAList,domain_lookup]
        )
        >> qexists_tac `f_trns` >> fs[]
        >> `!L. (MEM (id,nL.frml) L)
               ==> (MEM (nL.frml,f_trns)
                        (FOLDR
                          (λ(id,x) sF.
                            case concr_extrTrans g_AA id of
                                NONE => sF
                              | SOME c_t => if is_until x
                                            then (x,c_t)::sF
                                            else sF) []
                          L))` by (
                Induct_on `L` >> fs[MEM_SUBSET_SET_TO_LIST]
                >> rpt strip_tac >> Cases_on `h` >> fs[]
                >> Cases_on `concr_extrTrans g_AA q` >> fs[]
                >> Cases_on `is_until r` >> fs[]
            )
        >> fs[]
        >> `MEM (id,nL.frml) (graphStatesWithId g_AA)`
                suffices_by metis_tac[]
        >> simp[graphStatesWithId_def,MEM_MAP]
        >> qexists_tac `(id,nL)` >> fs[]
        )
       )
   >> `(set (MAP FST final_trans)) =
          {x | is_until x ∧ MEM x (graphStates g_AA) }` by (
       simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
       >- (fs[valid_acc_def,MEM_MAP] >> Cases_on `y`
           >> metis_tac[FST]
          )
       >- (fs[valid_acc_def,MEM_MAP] >> Cases_on `y`
           >> `∃id nL.
                findNode (λ(i,l). l.frml = q) g_AA = SOME (id,nL)`
               by metis_tac[]
           >> simp[graphStates_def,MEM_MAP]
           >> `(MEM (id,nL) (toAList g_AA.nodeInfo))
              ∧ (λ(i,l). l.frml = q) (id,nL)`
               by metis_tac[findNode_def,FIND_LEMM2]
           >> fs[] >> metis_tac[SND]
          )
       >- (fs[valid_acc_def,MEM_MAP] >> metis_tac[FST])
   )
   >> `!l G id. ((FOLDR (λn g. addNodeToGBA g n)
                (empty:(α nodeLabelGBA, α edgeLabelGBA) gfg)
                  l) = G)
          ∧ (id ∈ domain G.nodeInfo)
          ==> (lookup id G.followers = SOME [])` by (
          Induct_on `l` >> fs[] >> rpt strip_tac
          >- fs[empty_def]
          >- (qabbrev_tac `G_int =
                FOLDR (λn g. addNodeToGBA g n)
                      (empty:(α nodeLabelGBA,α edgeLabelGBA) gfg)
                      l`
              >> simp[addNodeToGBA_def]
              >> Cases_on `inGBA G_int h` >> fs[addNodeToGBA_def]
              >> fs[addNode_def]
              >> Cases_on `id = G_int.next` >> fs[]
              >> metis_tac[lookup_insert]
             )
   )
   >> first_x_assum (qspec_then
      `(MAP
            (λi_list.
                 MAP (λl. l.frml)
                 (CAT_OPTIONS
                      (MAP (λi. lookup i g_AA.nodeInfo) (nub i_list))))
            init)` mp_tac)
   >> strip_tac
   >> first_x_assum (qspec_then `addedInit` mp_tac) >> simp[]
   >> strip_tac
   >> `(trns_correct (MAP FST (toAList addedInit.nodeInfo))
                      abstrAA addedInit) (set aP)
      ∧ (aP_correct abstrAA addedInit aP)
      ∧ (final_correct abstrAA addedInit final_trans)` by (
       rpt conj_tac
       >- (simp[trns_correct_def] >> rpt strip_tac
           >> fs[MEM_MAP] >> first_x_assum (qspec_then `(id,nL)` mp_tac)
           >> simp[] >> metis_tac[MEM_toAList]
          )
       >- (simp[aP_correct_def] >> rpt strip_tac
           >> `lookup id addedInit.followers = SOME []`
               by metis_tac[domain_lookup]
           >> fs[] >> rw[] >> fs[]
          )
       >- (simp[final_correct_def] >> rpt strip_tac
           >> `lookup id addedInit.followers = SOME []`
               by metis_tac[domain_lookup]
           >> fs[] >> rw[] >> fs[]
          )
   )
   >> `(INIT ==> STATES) ∧ INIT
     ∧ (STATES ==> TRANS) ∧ ((STATES ∧ TRANS) ==> FINAL) ∧ ALPH`
       suffices_by metis_tac[]
   >> `aP_correct abstrAA gba aP ∧ final_correct abstrAA gba final_trans ∧
     trns_correct [] abstrAA gba (set aP)` by (
       HO_MATCH_MP_TAC EXPGBA_TRANS_AND_FINAL >> simp[]
       >> qexists_tac `f` >> qexists_tac `init`
       >> qexists_tac `g_AA`
       >> qexists_tac `(MAP FST (toAList addedInit.nodeInfo))`
       >> simp[] >> qexists_tac `addedInit`
       >> fs[] >> rpt strip_tac
       >- metis_tac[]
       >- metis_tac[]
       >- metis_tac[]
       >- metis_tac[]
       >- metis_tac[]
       >- metis_tac[ALL_DISTINCT_MAP_FST_toAList]
       >- (`id ∈ domain addedInit.nodeInfo`
             by metis_tac[domain_lookup,wfg_def]
           >> `lookup id addedInit.followers = SOME []`
             by metis_tac[domain_lookup]
           >> fs[] >> rw[] >> fs[]
          )
   )
   >> rpt strip_tac
   >- (`∀x.
          inGBA addedInit x ⇒
          set x ∈
          reachableFromSetGBA (vwaa2gba abstrAA)
          (vwaa2gba abstrAA).initial` by (
        qunabbrev_tac `INIT` >> rw[] >> simp[vwaa2gba_def,GBA_component_equality]
        >> fs[inGBA_def,EXISTS_MEM,MEM_MAP] >> rename[`MEM y _`]
        >> Cases_on `y` >> fs[] >> rw[] >> rename[`MEM (id,n) _`]
        >> `lookup id gba.nodeInfo = SOME n` by (
            metis_tac[MEM_toAList,domain_lookup]
        )
        >> `set x ∈
             concr2AbstrGBA_init
             (MAP FST (toAList addedInit.nodeInfo))
             gba` suffices_by (
            simp[reachableFromSetGBA_def,reachableFromGBA_def]
            >> metis_tac[RTC_REFL]
        )
        >> PURE_REWRITE_TAC[concr2AbstrGBA_init_def]
        >> simp[CAT_OPTIONS_MEM,MEM_MAP] >> qexists_tac `id` >> fs[]
        >> fs[MEM_EQUAL_SET] >> metis_tac[FST]
       )
       >> `∀x. inGBA addedInit x ⇒ set x ∈ POW abstrAA.states` by (
          rpt strip_tac >> qunabbrev_tac `INIT` >> rw[]
          >> simp[vwaa2gba_def,GBA_component_equality]
          >> fs[inGBA_def,EXISTS_MEM,MEM_MAP] >> rename[`MEM y _`]
          >> Cases_on `y` >> fs[] >> rw[] >> rename[`MEM (id,n) _`]
          >> `lookup id gba.nodeInfo = SOME n` by (
              metis_tac[MEM_toAList,domain_lookup]
          )
          >> `set x ∈
                concr2AbstrGBA_init
                (MAP FST (toAList addedInit.nodeInfo))
                gba` by (
              PURE_REWRITE_TAC[concr2AbstrGBA_init_def]
              >> simp[CAT_OPTIONS_MEM,MEM_MAP]
              >> qexists_tac `id` >> fs[]
              >> fs[MEM_EQUAL_SET] >> metis_tac[FST]
          )
          >> `isValidAlterA (concr2AbstrAA (concrAA g_AA init aP))` by (
              metis_tac[REDUCE_STATE_IS_VALID,LTL2WAA_ISVALID]
          )
          >> POP_ASSUM mp_tac >> simp[isValidAlterA_def]
          >> metis_tac[SUBSET_DEF]
       )
       >> qunabbrev_tac `STATES` >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> strip_tac
       >- (`!x. inGBA gba x
              ==> ((set x ∈ reachableFromSetGBA (vwaa2gba abstrAA)
                        (vwaa2gba abstrAA).initial)
                       ∧ (set x ∈ (vwaa2gba abstrAA).states))` by (
            HO_MATCH_MP_TAC EXPGBA_GRAPH_REACHABLE
            >> simp[] >> qexists_tac `f` >> qexists_tac `init`
            >> qexists_tac `aP` >> qexists_tac `g_AA` >> simp[]
            >> qexists_tac `final_trans`
            >> qexists_tac `MAP FST (toAList addedInit.nodeInfo)`
            >> qexists_tac `addedInit` >> simp[] >> rpt strip_tac
            >> metis_tac[]
           )
           >> rpt strip_tac
           >> fs[concr2AbstrGBA_states_def] >> rename[`SOME q = lookup _ _`]
           >> `inGBA gba q.frmls` by (
                 simp[inGBA_def,EXISTS_MEM,MEM_MAP] >> qexists_tac `q`
                 >> simp[MEM_EQUAL_SET] >> qexists_tac `(n,q)`
                 >> metis_tac[SND,MEM_toAList]
           )
           >> first_x_assum (qspec_then `q.frmls` mp_tac)
           >> simp[vwaa2gba_def]
          )
       >- (rpt strip_tac >> fs[reachableFromSetGBA_def,reachableFromGBA_def]
           >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
           >> Q.HO_MATCH_ABBREV_TAC `
                (stepGBA G)^* x1 x2
                 ==> x1 ∈ init_states
                 ==> x2 ∈ concr2AbstrGBA_states gba`
           >> `!a b. (stepGBA G)^* a b
                 ==> a ∈ init_states
                 ==> b ∈ concr2AbstrGBA_states gba` suffices_by metis_tac[]
           >> HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 >> rpt strip_tac
           >- (qunabbrev_tac `init_states` >> fs[]
               >> `a ∈
                    concr2AbstrGBA_init (MAP FST (toAList addedInit.nodeInfo))
                    gba` by metis_tac[]
               >> POP_ASSUM mp_tac
               >> simp[concr2AbstrGBA_init_def,concr2AbstrGBA_states_def]
               >> simp[CAT_OPTIONS_MEM,MEM_MAP] >> strip_tac
               >> metis_tac[domain_lookup]
              )
           >- (`one_step_closed abstrAA gba` by (
                HO_MATCH_MP_TAC EXPGBA_ALL_REACHABLE
                >> simp[] >> qexists_tac `f`
                >> qexists_tac `init`
                >> qexists_tac `aP` >> qexists_tac `g_AA`
                >> simp[] >> qexists_tac `final_trans`
                >> qexists_tac `MAP FST (toAList addedInit.nodeInfo)`
                >> qexists_tac `addedInit` >> simp[] >> conj_tac
                >- metis_tac[]
                >- (
                 simp[one_step_closed_apart_l_def] >> rpt strip_tac
                 >> fs[MEM_MAP] >> metis_tac[FST,MEM_toAList]
                )
              )
              >> fs[one_step_closed_def,concr2AbstrGBA_states_def]
              >> rename[`b = set q1.frmls`]
              >> `inGBA gba q1.frmls` by (
                  simp[inGBA_def,EXISTS_MEM,MEM_MAP]
                  >> qexists_tac `q1` >> simp[MEM_EQUAL_SET]
                  >> qexists_tac `(n,q1)` >> simp[]
                  >> metis_tac[MEM_toAList]
              )
              >> first_x_assum (qspec_then `q1.frmls` mp_tac) >> simp[]
              >> strip_tac
              >> `FINITE b'` by (
                   fs[stepGBA_def] >> qunabbrev_tac `G` >> fs[]
                   >> `(a',b') ∈ (vwaa2gba abstrAA).trans b` by (
                       fs[vwaa2gba_def] >> metis_tac[]
                   )
                   >> `FINITE
                        (concr2AbstrAA (concrAA g_AA init aP)).states` by (
                     simp[concr2AbstrAA_def,concr2Abstr_states_def]
                     >> `FINITE {x.frml |
                                 ?n. MEM (n,x) (toAList g_AA.nodeInfo)}`
                        suffices_by (
                        Q.HO_MATCH_ABBREV_TAC `FINITE S1 ==> FINITE S2`
                        >> `S1 = S2` suffices_by fs[]
                        >> qunabbrev_tac `S1` >> qunabbrev_tac `S2`
                        >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                        >> metis_tac[MEM_toAList,domain_lookup]
                     )
                     >> `{x.frml | ∃n. MEM (n,x) (toAList g_AA.nodeInfo)} =
                       IMAGE (λ(i,n). n.frml) (set (toAList g_AA.nodeInfo))`
                        by (
                      simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                      >- (qexists_tac `(n',x''')` >> fs[])
                      >- (fs[] >> Cases_on `x'''` >> fs[] >> metis_tac[])
                     )
                    >> metis_tac[FINITE_LIST_TO_SET,IMAGE_FINITE]
                   )
                   >> `isValidGBA (vwaa2gba abstrAA)` by (
                    HO_MATCH_MP_TAC WAA2GBA_ISVALID
                    >> fs[]
                    >> metis_tac[REDUCE_STATE_IS_VALID,LTL2WAA_ISVALID]
                   )
                   >> fs[isValidGBA_def]
                   >> `b ∈ (vwaa2gba abstrAA).states` by (
                       qunabbrev_tac `abstrAA` >> simp[vwaa2gba_def] >> rw[]
                   )
                   >> `b' ∈ (vwaa2gba abstrAA).states` by metis_tac[SUBSET_DEF]
                   >> POP_ASSUM mp_tac >> simp[vwaa2gba_def]
                   >> simp[concr2AbstrAA_def,concr2Abstr_states_def,IN_POW]
                   >> strip_tac
                   >> `FINITE {x.frml |
                               ?n. MEM (n,x) (toAList g_AA.nodeInfo)}`
                      suffices_by (
                       Q.HO_MATCH_ABBREV_TAC `FINITE S1 ==> FINITE S2`
                       >> `S2 ⊆ S1`
                            suffices_by metis_tac[PSUBSET_DEF,PSUBSET_FINITE]
                       >> qunabbrev_tac `S1` >> qunabbrev_tac `S2`
                       >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                       >> fs[SUBSET_DEF]
                       >> metis_tac[MEM_toAList,domain_lookup,SUBSET_DEF]
                   )
                  >> `{x.frml | ∃n. MEM (n,x) (toAList g_AA.nodeInfo)} =
                       IMAGE (λ(i,n). n.frml) (set (toAList g_AA.nodeInfo))`
                      by (
                       simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                           >- (qexists_tac `(n',x''')` >> fs[])
                           >- (fs[] >> Cases_on `x'''` >> fs[] >> metis_tac[])
                   )
                 >> metis_tac[FINITE_LIST_TO_SET,IMAGE_FINITE]
               )
              >> qabbrev_tac `q = nodeLabelGBA (SET_TO_LIST b')`
              >> first_x_assum (qspec_then `q.frmls` mp_tac)
              >> `G = vwaa2gba (concr2AbstrAA (concrAA g_AA init aP))` by (
                 qunabbrev_tac `G` >> fs[] >> simp[vwaa2gba_def]
              )
              >> `b' = set q.frmls` by (
                   qunabbrev_tac `q` >> simp[]
                   >> metis_tac[SET_TO_LIST_INV]
              )
              >> `stepGBA
                   (vwaa2gba (concr2AbstrAA (concrAA g_AA init aP)))
                   (set q1.frmls)
                   (set q.frmls)` by (
                   simp[] >> metis_tac[]
              )
              >> simp[] >> simp[inGBA_def,EXISTS_MEM,MEM_MAP] >> strip_tac
              >> Cases_on `y` >> fs[] >> qexists_tac `r` >> rw[]
              >- fs[MEM_EQUAL_SET]
              >- metis_tac[MEM_toAList,domain_lookup]
              )
          )
      )
   >- (qunabbrev_tac `INIT` >> simp[concr2AbstrAA_def,concr2Abstr_init_def]
       >> qunabbrev_tac `addedInit`
       >> Q.HO_MATCH_ABBREV_TAC `
             concr2AbstrGBA_init
             (MAP FST
                  (toAList (G_int init).nodeInfo)) gba =
           I_SET init`
       >> Q.HO_MATCH_ABBREV_TAC `P init`
       >> `!ls.  (!l i. MEM l ls ∧ MEM i l
                     ==> i ∈ domain g_AA.nodeInfo)
                 ∧ (!i. i ∈ domain (G_int ls).nodeInfo
                     ==> (lookup i (G_int ls).nodeInfo = lookup i gba.nodeInfo)
                   )
                 ∧ (!i. i ∈ domain (G_int ls).nodeInfo
                        ==> i ∈ domain gba.nodeInfo)
                     ==> P ls` by (
            qunabbrev_tac `P` >> fs[] >> Induct_on `ls` >> fs[]
            >- (qunabbrev_tac `I_SET` >> qunabbrev_tac `G_int`
                >> simp[concr2AbstrGBA_init_def,toAList_def,foldi_def,empty_def]
                >> simp[CAT_OPTIONS_def])
            >- (rpt strip_tac
                >> qunabbrev_tac `G_int` >> qunabbrev_tac `I_SET`
                >> simp[]
                >> qabbrev_tac
                   `G_int =
                     FOLDR (λn g. addNodeToGBA g n)
                       (empty:(α nodeLabelGBA, α edgeLabelGBA) gfg)
                       (MAP
                            (λi_list.
                                 MAP (λl. l.frml)
                                 (CAT_OPTIONS
                                      (MAP (λi. lookup i g_AA.nodeInfo)
                                           (nub i_list)))) ls)`
               >> qabbrev_tac `NEW_L =
                     (MAP (λl. l.frml)
                       (CAT_OPTIONS
                        (MAP (λi. lookup i g_AA.nodeInfo) (nub h))))`
                >> qabbrev_tac `OLD_S =
                    set
                    (MAP
                        (λl.
                          {x.frml |
                           MEM x (CAT_OPTIONS (MAP (λn. lookup n g_AA.nodeInfo) l))}) ls)`
                >> fs[]
                >> `wfg G_int` by (
                     qunabbrev_tac `G_int`
                     >> Q.HO_MATCH_ABBREV_TAC `wfg (A ls)`
                     >> `!j. wfg (A j)` by (
                         Induct_on `j` >> qunabbrev_tac `A` >> fs[]
                                   >> strip_tac >> metis_tac[ADDNODE_GBA_WFG]
                     )
                     >> fs[]
                 )
                >> `(∀i.
                      i ∈ domain G_int.nodeInfo ⇒
                      lookup i G_int.nodeInfo = lookup i gba.nodeInfo) ∧
                    (∀i. i ∈ domain G_int.nodeInfo
                      ⇒ i ∈ domain gba.nodeInfo)` by (
                   rpt strip_tac
                   >- (
                     `~(G_int.next <= i)` by metis_tac[wfg_def]
                     >> `~(G_int.next = i)` by fs[]
                     >> `i ∈ domain (addNodeToGBA G_int NEW_L).nodeInfo`
                          by (
                         PURE_REWRITE_TAC[addNodeToGBA_def]
                         >> Cases_on `inGBA G_int NEW_L` >> fs[]
                         >> simp[addNode_def]
                     )
                     >> `lookup i G_int.nodeInfo =
                          lookup i (addNodeToGBA G_int NEW_L).nodeInfo`
                         suffices_by metis_tac[]
                     >> PURE_REWRITE_TAC[addNodeToGBA_def]
                     >> Cases_on `inGBA G_int NEW_L` >> fs[]
                     >> simp[addNode_def]
                     >> metis_tac[lookup_insert]
                   )
                   >- (
                    `i ∈ domain (addNodeToGBA G_int NEW_L).nodeInfo`
                      by (
                        PURE_REWRITE_TAC[addNodeToGBA_def]
                        >> Cases_on `inGBA G_int NEW_L` >> fs[]
                        >> simp[addNode_def]
                       )
                    >> metis_tac[]
                   )
                 )
                >> `concr2AbstrGBA_init
                    (MAP FST (toAList G_int.nodeInfo)) gba = OLD_S`
                    by (fs[] >> metis_tac[])
                >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                >- (fs[concr2AbstrGBA_init_def,CAT_OPTIONS_MEM,MEM_MAP]
                    >> `{set x | inGBA (addNodeToGBA G_int NEW_L) x} =
                         {set x | inGBA G_int x} ∪ {set NEW_L}` by (
                         metis_tac[ADDNODE_GBA_LEMM,WF_IMP_SUFFWFG]
                     )
                    >> Cases_on `y` >> fs[] >> rw[]
                    >> `n = r` by metis_tac[MEM_toAList,SOME_11,domain_lookup]
                    >> rw[]
                    >> `set n.frmls ∈
                             {set x | inGBA (addNodeToGBA G_int NEW_L) x}` by (
                         `inGBA (addNodeToGBA G_int NEW_L) n.frmls`
                               suffices_by (simp[] >> metis_tac[])
                         >> simp[inGBA_def,EXISTS_MEM,MEM_MAP]
                         >> qexists_tac `n` >> simp[MEM_EQUAL_SET]
                         >> qexists_tac `(i,n)` >> simp[]
                     )
                    >> `set n.frmls ∈
                             {set x | inGBA G_int x} ∪ {set NEW_L}` by metis_tac[]
                    >> fs[IN_UNION]
                    >- (rename[`inGBA G_int x1`]
                        >> `MEM (set x1)
                             (CAT_OPTIONS
                             (MAP
                               (λi.
                                   do n <- lookup i gba.nodeInfo; SOME (set n.frmls) od)
                               (MAP FST (toAList G_int.nodeInfo))))` by (
                          simp[CAT_OPTIONS_MEM,MEM_MAP]
                          >> fs[inGBA_def,EXISTS_MEM,MEM_MAP]
                          >> rw[] >> Cases_on `y'` >> fs[]
                          >> `q ∈ domain G_int.nodeInfo` by (
                              metis_tac[MEM_toAList,domain_lookup]
                          )
                          >> `q ∈ domain (addNodeToGBA G_int NEW_L).nodeInfo`
                             by (simp[addNodeToGBA_def]
                                 >> Cases_on `inGBA G_int NEW_L` >> fs[]
                                 >> simp[addNode_def]
                                )
                          >> qexists_tac `q` >> simp[] >> strip_tac
                          >- (`lookup q (addNodeToGBA G_int NEW_L).nodeInfo =
                               SOME r` by metis_tac[SOME_11,MEM_toAList]
                              >> qexists_tac `r` >> fs[] >> Cases_on `y` >> fs[]
                              >> rw[] >> metis_tac[MEM_toAList,MEM_EQUAL_SET]
                             )
                          >- metis_tac[FST]
                         )
                        >> metis_tac[]
                       )
                    >- (disj1_tac >> fs[] >> rpt strip_tac
                        >- (qunabbrev_tac `NEW_L` >> fs[] >> rw[]
                            >> `MEM x'
                                (MAP (λl. l.frml)
                                 (CAT_OPTIONS
                                      (MAP (λi. lookup i g_AA.nodeInfo)
                                           (nub h))))` by metis_tac[]
                            >> fs[MEM_MAP,CAT_OPTIONS_MEM]
                            >> metis_tac[]
                           )
                        >- (rw[] >> `MEM x''.frml NEW_L` suffices_by fs[]
                            >> qunabbrev_tac `NEW_L`
                            >> simp[MEM_MAP,CAT_OPTIONS_MEM] >> metis_tac[]
                           )
                       )
                   )
                >- (simp[concr2AbstrGBA_init_def,MEM_MAP,CAT_OPTIONS_MEM]
                    >> Cases_on `inGBA G_int NEW_L`
                    >- (
                     simp[addNodeToGBA_def]
                     >> POP_ASSUM mp_tac >> simp[inGBA_def,EXISTS_MEM,MEM_MAP]
                     >> strip_tac >> Cases_on `y` >> rw[]
                     >> rename[`MEM (id,n) _`] >> fs[]
                     >> qexists_tac `id` >> simp[] >> strip_tac
                     >- (qexists_tac `n` >> fs[] >> strip_tac
                      >- metis_tac[MEM_toAList,SOME_11,domain_lookup]
                      >- (`set NEW_L =
                           {x.frml | ∃n. SOME x = lookup n g_AA.nodeInfo
                                                         ∧ MEM n h}`
                          suffices_by metis_tac[MEM_EQUAL_SET]
                          >> qunabbrev_tac `NEW_L`
                          >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                          >> fs[MEM_MAP,CAT_OPTIONS_MEM] >> metis_tac[]
                         )
                        )
                     >- metis_tac[FST]
                     )
                    >- (qexists_tac `G_int.next` >> simp[]
                        >> strip_tac
                        >- (
                         `lookup G_int.next
                            (addNodeToGBA G_int NEW_L).nodeInfo =
                               SOME (nodeLabelGBA NEW_L)` by (
                             simp[addNodeToGBA_def]
                             >> PURE_REWRITE_TAC[addNode_def]
                             >> simp[]
                         )
                         >> qexists_tac `nodeLabelGBA NEW_L` >> simp[]
                         >> strip_tac
                         >- metis_tac[SOME_11,domain_lookup]
                         >- (qunabbrev_tac `NEW_L`
                             >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                             >> fs[MEM_MAP,CAT_OPTIONS_MEM] >> metis_tac[]
                            )
                         )
                        >- (qexists_tac `(G_int.next,nodeLabelGBA NEW_L)`
                            >> simp[addNodeToGBA_def]
                            >> PURE_REWRITE_TAC[addNode_def] >> simp[]
                            >> metis_tac[MEM_toAList,lookup_insert]
                       )
                       )
                   )
                >- (`x ∈ concr2AbstrGBA_init
                           (MAP FST (toAList G_int.nodeInfo)) gba` by fs[]
                    >> fs[concr2AbstrGBA_init_def,CAT_OPTIONS_MEM,MEM_MAP]
                    >> Cases_on `y` >> fs[] >> rw[]
                    >> `n = r` by metis_tac[MEM_toAList,domain_lookup,SOME_11]
                    >> rw[] >> qexists_tac `i` >> fs[]
                    >> qexists_tac `(i,n)` >> fs[]
                    >> `i ∈ domain (addNodeToGBA G_int NEW_L).nodeInfo` by (
                       simp[addNodeToGBA_def] >> PURE_REWRITE_TAC[addNode_def]
                       >> Cases_on `inGBA G_int NEW_L` >> fs[]
                       >> metis_tac[MEM_toAList,domain_lookup]
                    )
                    >> metis_tac[MEM_toAList,domain_lookup]
                   )
               )
        )
       >> first_x_assum (qspec_then `init` mp_tac) >> simp[]
       >> fs[] >> Q.HO_MATCH_ABBREV_TAC `(A ==> P init) ==> P init`
       >> `A` suffices_by fs[] >> qunabbrev_tac `A`
       >> rpt strip_tac
       >- (fs[expandAuto_init_def] >> rw[] >> fs[MEM_MAP,CAT_OPTIONS_MEM]
           >> rw[] >> fs[MEM_MAP, CAT_OPTIONS_MEM]
           >> qabbrev_tac `ADDEDNODES =
                    (FOLDR (λs g. addFrmlToGraph g s)
                           (empty: (α nodeLabelAA, α edgeLabelAA) gfg)
                           (nub (FLAT (tempDNF_concr f))))`
           >> `(∀f'. MEM f' (nub (FLAT (tempDNF_concr f)))
                 ⇒ MEM f' (graphStates ADDEDNODES))
               ==> (set (graphStatesWithId ADDEDNODES)
                        ⊆ set (graphStatesWithId g_AA))`
                 by (
                `wfg ADDEDNODES` by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg]
                >> `unique_node_formula ADDEDNODES`
                  by metis_tac[ADDFRML_FOLDR_LEMM,UNIQUE_NODE_FORM_EMPTY,
                              empty_is_wfg]
                >> `flws_sorted ADDEDNODES`
                  by metis_tac[ADDFRML_FOLDR_LEMM,FLWS_SORTED_EMPTY,
                               empty_is_wfg]
                >> `!g fs. wfg g ∧ unique_node_formula g ∧ flws_sorted g ∧
                      (∀f. MEM f fs ⇒ MEM f (graphStates g)) ⇒
                      ∃g2.
                      (expandGraph g fs = SOME g2 ∧ wfg g2)
                      ∧ set (graphStatesWithId g) ⊆ set (graphStatesWithId g2)`
                   by metis_tac[EXP_GRAPH_WFG_AND_SOME]
                >> first_x_assum (qspec_then `ADDEDNODES` mp_tac)
                >> simp[] >> strip_tac
                >> first_x_assum
                    (qspec_then `nub (FLAT (tempDNF_concr f))` mp_tac)
                >> simp[] >> strip_tac >> strip_tac
            )
            >> `∀f'.
                 MEM f' (nub (FLAT (tempDNF_concr f))) ⇒
                 MEM f' (graphStates ADDEDNODES)` by (
                rpt strip_tac
                >> `set (graphStates (empty:(α nodeLabelAA,α edgeLabelAA) gfg))
                      ∪ set (nub (FLAT (tempDNF_concr f))) =
                     set (graphStates ADDEDNODES)` by (
                  qunabbrev_tac `ADDEDNODES`
                  >> metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg]
                )
                >> fs[GRAPHSTATES_EMPTY]
            )
            >> fs[findNode_def]
            >> `MEM z (toAList ADDEDNODES.nodeInfo)` by metis_tac[FIND_LEMM2]
            >> Cases_on `z` >> fs[]
            >> `MEM (q,r.frml) (graphStatesWithId ADDEDNODES)`
               by metis_tac[GRAPH_STATES_WITH_ID_LEMM]
            >> `MEM (q,r.frml) (graphStatesWithId g_AA)` by fs[SUBSET_DEF]
            >> fs[graphStatesWithId_def,MEM_MAP] >> rename[`MEM y2 _`]
            >> Cases_on `y2` >> fs[]
            >> metis_tac[MEM_toAList,domain_lookup]
          )
       >- metis_tac[domain_lookup]
      )
   >- (qunabbrev_tac `TRANS`
       >> Q.HO_MATCH_ABBREV_TAC `
            extractGBATrans (set aP) gba =
              ABS_TRNS`
       >> `!q. extractGBATrans (props f) gba q =
                ABS_TRNS q`
             suffices_by metis_tac[]
       >> gen_tac >> simp[SET_EQ_SUBSET,SUBSET_DEF]
       >> qunabbrev_tac `ABS_TRNS` >> strip_tac
       >- (simp[extractGBATrans_def] >> rpt strip_tac
           >> `q ∈ concr2AbstrGBA_states gba` by (
             PURE_REWRITE_TAC[concr2AbstrGBA_states_def]
             >> fs[OPTION_TO_LIST_MEM] >> rename[`_ x1 = SOME l`]
             >> Cases_on `x1` >> fs[] >> rw[]
             >> fs[CAT_OPTIONS_MEM,MEM_MAP]
             >> Cases_on `y` >> fs[]
             >> qexists_tac `r` >> fs[]
             >> `MEM (q',r) (toAList gba.nodeInfo)
               ∧ (λ(i,n). set n.frmls = q) (q',r)`
                by metis_tac[findNode_def,FIND_LEMM2]
             >> fs[] >> metis_tac[MEM_toAList,domain_lookup]
            )
           >> `x ∈ gba_trans (concr2AbstrAA (concrAA g_AA init aP)) q`
               suffices_by metis_tac[IN_INTER]
          >> fs[OPTION_TO_LIST_MEM] >> rename[`findNode _ gba = SOME x1`]
          >> Cases_on `x1` >> fs[]
          >> `MEM (q',r) (toAList gba.nodeInfo)
           ∧ (λ(i,n). set n.frmls = q) (q',r)`
              by metis_tac[findNode_def,FIND_LEMM2]
          >> fs[]
          >> `q ∈ POW abstrAA.states` by metis_tac[IN_INTER]
          >> fs[trns_correct_def]
          >> first_x_assum (qspec_then `q'` mp_tac) >> strip_tac
          >> first_x_assum (qspec_then `r` mp_tac) >> strip_tac
          >> first_x_assum (qspec_then `fls` mp_tac) >> simp[]
          >> `(lookup q' gba.nodeInfo = SOME r)
              ∧ (q ∈ POW (concr2AbstrAA (concrAA g_AA init aP)).states)`
             by metis_tac[MEM_toAList]
          >> metis_tac[]
          )
       >- (simp[extractGBATrans_def] >> rpt strip_tac
           >> `q ∈ concr2AbstrGBA_states gba` by (
                metis_tac[MEMBER_NOT_EMPTY,IN_INTER]
            )
           >> `x ∈ gba_trans (concr2AbstrAA (concrAA g_AA init aP)) q`
                by metis_tac[MEMBER_NOT_EMPTY]
           >> simp[OPTION_TO_LIST_MEM]
           >> Q.HO_MATCH_ABBREV_TAC
                `?l. (?x. F1 x ∧ (L x = SOME l)) ∧ (MEM x l)`
           >> `?x. F1 x` by (
                qunabbrev_tac `F1` >> fs[concr2AbstrGBA_states_def]
                >> simp[findNode_def]
                >> `?x. (MEM x (toAList gba.nodeInfo))
                      ∧ (λ(i,n). set n.frmls = set x'.frmls) x`
                   suffices_by metis_tac[FIND_LEMM]
                >> qexists_tac `(n,x')` >> fs[]
                >> metis_tac[MEM_toAList]
            )
           >> `?l. L x' = SOME l` by (
                qunabbrev_tac `L` >> qunabbrev_tac `F1` >> fs[]
                >> Cases_on `x'` >> simp[]
                >> `MEM (q',r) (toAList gba.nodeInfo)`
                    by metis_tac[findNode_def,FIND_LEMM2]
                >> metis_tac[wfg_def,domain_lookup,MEM_toAList]
            )
           >> qexists_tac `l` >> fs[] >> conj_tac
           >- metis_tac[]
           >- (
            qunabbrev_tac `L` >> qunabbrev_tac `F1` >> fs[]
            >> fs[trns_correct_def]
            >> `q ∈ POW abstrAA.states` by metis_tac[IN_INTER]
            >> Cases_on `x'`
            >> `MEM (q',r) (toAList gba.nodeInfo)
             ∧ (λ(i,n). set n.frmls = q) (q',r)`
                 by metis_tac[findNode_def,FIND_LEMM2]
            >> first_x_assum (qspec_then `q'` mp_tac) >> strip_tac
            >> first_x_assum (qspec_then `r` mp_tac) >> strip_tac
            >> `?fls. lookup q' gba.followers = SOME fls`
                 by metis_tac[MEM_toAList,domain_lookup,wfg_def]
            >> first_x_assum (qspec_then `fls` mp_tac) >> simp[]
            >> `(lookup q' gba.nodeInfo = SOME r)
              ∧ (q ∈ POW (concr2AbstrAA (concrAA g_AA init aP)).states)`
                by metis_tac[MEM_toAList]
            >> fs[] >> metis_tac[]
            )
          )
      )
   >- (`!l u ce. MEM u (get_acc_set l ce)
                 ==> MEM u (MAP FST l)` by (
        Induct_on `l` >> fs[get_acc_set_def,CAT_OPTIONS_def]
        >> rpt strip_tac >> fs[CAT_OPTIONS_MEM]
        >> Cases_on `h` >> fs[MEM_MAP] >> Cases_on `y` >> fs[]
        >> metis_tac[FST]
       )
       >> `!id q. (lookup id gba.nodeInfo = SOME q)
                 ==> set q.frmls ∈ concr2AbstrGBA_states gba` by (
           rpt strip_tac >> fs[]
           >> PURE_REWRITE_TAC[concr2AbstrGBA_states_def]
           >> simp[] >> qexists_tac `q` >> metis_tac[domain_lookup]
       )
       >> qunabbrev_tac `FINAL` >> simp[concr2AbstrGBA_final_def]
       >> `∀ce u aE.
            (aE = concr2AbstractEdge (set aP) ce) ∧ is_until u
            ∧ MEM u (graphStates g_AA) ∧ MEM_SUBSET ce.pos aP
            ∧ MEM_SUBSET ce.neg aP ∧ MEM_SUBSET ce.sucs (graphStates g_AA) ⇒
            ∀qs2.
            qs2 ∈ POW abstrAA.states ⇒
            (MEM u (get_acc_set final_trans ce) ⇔
                 (qs2,FST aE,SND aE) ∈ acc_cond abstrAA u)` by (
            HO_MATCH_MP_TAC CONCR_ACC_SETS
            >> simp[] >> metis_tac[]
        )
       >> fs[final_correct_def]
       >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
       >> qabbrev_tac `realTrans =
             {(e,a,e') | (a,e') ∈ gba_trans abstrAA e ∧ e ∈ POW abstrAA.states}`
       >- (rename[`MEM u (graphStates g_AA)`]
           >> qexists_tac `acc_cond abstrAA u ∩ realTrans`
           >> rpt strip_tac
           >- (rename[`t ∈ x`]
            >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
            >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
            >> first_x_assum (qspec_then `t` mp_tac)
            >> Cases_on `t` >> simp[] >> Cases_on `r` >> rpt strip_tac
            >> fs[] >> rename[`(e,a,e') ∈ x`] >> simp[]
            >> rpt strip_tac
            >- (
             first_x_assum
                 (qspec_then `concrEdge eL.pos_lab eL.neg_lab q2.frmls` mp_tac)
             >> simp[] >> strip_tac
             >> first_x_assum (qspec_then `u` mp_tac)
             >> first_x_assum (qspec_then `id1` mp_tac) >> simp[]
             >> first_x_assum (qspec_then `id1` mp_tac) >> simp[] >> strip_tac
             >> first_x_assum (qspec_then `eL` mp_tac) >> simp[] >> strip_tac
             >> first_x_assum (qspec_then `id2` mp_tac) >> simp[]
             >> `set q1.frmls ∈
                  concr2AbstrGBA_states gba` by (
                 PURE_REWRITE_TAC[concr2AbstrGBA_states_def]
                 >> simp[] >> qexists_tac `q1`
                 >> metis_tac[MEM_toAList,domain_lookup]
             )
             >> `set q1.frmls ∈
                   POW (concr2AbstrAA (concrAA g_AA init aP)).states` by (
                 metis_tac[IN_INTER]
             )
             >> simp[] >> strip_tac
             >> first_x_assum (qspec_then `u` mp_tac) >> simp[] >> strip_tac
             >> `MEM u (MAP FST (final_trans))` by metis_tac[]
             >> fs[MEM_MAP] >> Cases_on `y` >> fs[]
             >> `∃id nL.
                   (findNode (λ(i,l). l.frml = u) g_AA = SOME (id,nL))
                   ∧ is_until u` by metis_tac[valid_acc_def,FST]
             >> `is_until u ∧ MEM u (graphStates g_AA)` by (
                 simp[graphStates_def,MEM_MAP]
                 >> `MEM (id,nL) (toAList g_AA.nodeInfo)
                   ∧ (λ(i,l). l.frml = u) (id,nL)`
                     by metis_tac[FIND_LEMM2,findNode_def]
                 >> fs[] >> qexists_tac `(id,nL)` >> fs[]
             )
             >> simp[]
             >> `MEM_SUBSET eL.pos_lab aP ∧
                   MEM_SUBSET eL.neg_lab aP` by metis_tac[aP_correct_def]
             >> simp[]
             >> `MEM_SUBSET q2.frmls (graphStates g_AA)` by (
                `set q2.frmls ∈ concr2AbstrGBA_states gba` by (
                    PURE_REWRITE_TAC[concr2AbstrGBA_states_def]
                    >> simp[] >> qexists_tac `q2`
                     >> metis_tac[MEM_toAList,domain_lookup]
                )
                >> `set q2.frmls ∈
                     POW (concr2AbstrAA (concrAA g_AA init aP)).states`
                    by metis_tac[IN_INTER]
                >> fs[concr2AbstrAA_def,concr2Abstr_states_def]
                >> fs[IN_POW] >> simp[MEM_SUBSET_SET_TO_LIST]
                >> simp[graphStates_def,SUBSET_DEF] >> strip_tac
                >> simp[MEM_MAP] >> strip_tac
                >> `x' ∈
                     {x.frml |
                      ∃n. SOME x = lookup n g_AA.nodeInfo
                         ∧ n ∈ domain g_AA.nodeInfo}` by fs[SUBSET_DEF]
                >> fs[] >> qexists_tac `(n,x'')` >> simp[]
                >> metis_tac[MEM_toAList]
             )
             >> simp[] >> rw[]
             >> first_x_assum (qspec_then `set q1.frmls` mp_tac) >> simp[]
             >> simp[concr2AbstractEdge_def]
                )
            >- (qunabbrev_tac `realTrans` >> fs[]
                >> `set q1.frmls ∈ POW abstrAA.states ∩
                     (reachableFromSetGBA
                     (GBA (POW (concr2AbstrAA (concrAA g_AA init aP)).states)
                          (concr2AbstrAA (concrAA g_AA init aP)).initial
                          (gba_trans (concr2AbstrAA (concrAA g_AA init aP)))
                          (gba_accTrans (concr2AbstrAA (concrAA g_AA init aP)))
                          (concr2AbstrAA (concrAA g_AA init aP)).alphabet)
                     (concr2AbstrAA (concrAA g_AA init aP)).initial)` by (
                    `set q1.frmls ∈ concr2AbstrGBA_states gba`
                       suffices_by metis_tac[IN_INTER]
                    >> PURE_REWRITE_TAC[concr2AbstrGBA_states_def]
                    >> simp[] >> qexists_tac `q1`
                    >> metis_tac[MEM_toAList,domain_lookup]
                 )
                >> fs[] >> conj_tac
                >- (fs[trns_correct_def]
                    >> `set
                        (CAT_OPTIONS
                         (MAP
                          (λ(eL,i).
                            do
                            s_nL <- lookup i gba.nodeInfo;
                           SOME
                               (transformLabel (set aP) eL.pos_lab
                                               eL.neg_lab,set s_nL.frmls)
                               od) fls)) = gba_trans abstrAA (set q1.frmls)`
                        by metis_tac[]
                   >> `MEM (transformLabel (props f) eL.pos_lab eL.neg_lab,
                        set q2.frmls)
                          (CAT_OPTIONS
                           (MAP
                            (λ(eL,i).
                              do
                              s_nL <- lookup i gba.nodeInfo;
                             SOME
                             (transformLabel (set aP) eL.pos_lab eL.neg_lab,
                              set s_nL.frmls)
                             od) fls))` suffices_by metis_tac[]
                   >> simp[CAT_OPTIONS_MEM,MEM_MAP]
                   >> qexists_tac `(eL,id2)` >> fs[]
                   )
                >- metis_tac[]
               )
            >- metis_tac[IN_INTER]
            )
           >- (fs[trns_correct_def]
               >> `e ∈ POW abstrAA.states`
                   by (qunabbrev_tac `realTrans` >> fs[])
               >> `e ∈ concr2AbstrGBA_states gba` by metis_tac[IN_INTER]
               >> POP_ASSUM mp_tac
               >> PURE_REWRITE_TAC[concr2AbstrGBA_states_def] >> simp[]
               >> strip_tac
               >> `?fls. lookup n gba.followers = SOME fls`
                   by metis_tac[wfg_def,domain_lookup]
               >> `(a,e') ∈ gba_trans abstrAA e`
                 by (qunabbrev_tac `realTrans` >> fs[] >> metis_tac[])
               >> `MEM (a,e')
                     (CAT_OPTIONS
                      (MAP
                       (λ(eL,i).
                         do
                         s_nL <- lookup i gba.nodeInfo;
                        SOME
                            (transformLabel (set aP) eL.pos_lab
                                            eL.neg_lab,set s_nL.frmls)
                            od) fls))` by metis_tac[]
               >> fs[CAT_OPTIONS_MEM,MEM_MAP] >> Cases_on `y` >> fs[]
               >> fs[]
               >> first_x_assum (qspec_then
                                 `concrEdge q.pos_lab q.neg_lab s_nL.frmls`
                                 mp_tac)
               >> strip_tac
               >> first_x_assum (qspec_then `u` mp_tac) >> simp[]
               >> simp[]
               >> `MEM_SUBSET q.pos_lab aP ∧ MEM_SUBSET q.neg_lab aP`
                  by metis_tac[aP_correct_def]
               >> simp[]
             >> `MEM_SUBSET s_nL.frmls (graphStates g_AA)` by (
                `set s_nL.frmls ∈ concr2AbstrGBA_states gba` by (
                    PURE_REWRITE_TAC[concr2AbstrGBA_states_def]
                    >> simp[] >> qexists_tac `s_nL`
                     >> metis_tac[MEM_toAList,domain_lookup]
                )
                >> `set s_nL.frmls ∈
                     POW (concr2AbstrAA (concrAA g_AA init aP)).states`
                    by metis_tac[IN_INTER]
                >> fs[concr2AbstrAA_def,concr2Abstr_states_def]
                >> fs[IN_POW] >> simp[MEM_SUBSET_SET_TO_LIST]
                >> simp[graphStates_def,SUBSET_DEF] >> strip_tac
                >> simp[MEM_MAP] >> strip_tac
                >> `x''' ∈
                     {x.frml |
                      ∃n. SOME x = lookup n g_AA.nodeInfo
                         ∧ n ∈ domain g_AA.nodeInfo}` by fs[SUBSET_DEF]
                >> fs[] >> qexists_tac `(n',x'''')` >> simp[]
                >> metis_tac[MEM_toAList]
             )
             >> simp[] >> strip_tac
             >> first_x_assum (qspec_then `set x''.frmls` mp_tac)
             >> `set x''.frmls ∈
                     POW (concr2AbstrAA (concrAA g_AA init aP)).states` by (
                `set x''.frmls ∈ concr2AbstrGBA_states gba` by (
                   PURE_REWRITE_TAC[concr2AbstrGBA_states_def]
                   >> simp[] >> qexists_tac `x''`
                   >> metis_tac[MEM_toAList,domain_lookup]
                )
               >> metis_tac[IN_INTER]
                )
             >> simp[concr2AbstractEdge_def] >> fs[] >> strip_tac
             >> `MEM u
                  (get_acc_set final_trans
                   (concrEdge q.pos_lab q.neg_lab s_nL.frmls))`
                by metis_tac[concr2AbstrAA_def]
             >> first_x_assum (qspec_then `(set x''.frmls,a,e')` mp_tac)
             >> simp[]
             >> Q.HO_MATCH_ABBREV_TAC `(A ==> B) ==> B` >> `A` suffices_by fs[]
             >> qunabbrev_tac `A` >> qexists_tac `x''` >> simp[]
             >> qexists_tac `q` >> fs[] >> qexists_tac `s_nL` >> fs[]
             >> strip_tac
             >- metis_tac[concr2AbstrAA_def]
             >- metis_tac[]
              )
           >- (simp[gba_accTrans_def] >> qexists_tac `u` >> simp[]
               >> qunabbrev_tac `realTrans` >> fs[]
               >> simp[concr2AbstrAA_def,concr2Abstr_final_def]
               >> fs[graphStates_def,EXISTS_MEM,MEM_MAP]
               >> qexists_tac `SND y` >> simp[]
               >> fs[] >> Cases_on `y` >> fs[] >> conj_tac
               >- metis_tac[MEM_toAList,domain_lookup]
               >- (fs[until_iff_final_def,is_until_def]
                   >> Cases_on `u`
                   >> metis_tac[MEM_toAList,is_until_def]
                  )
              )
          )
       >- (fs[gba_accTrans_def] >> rename[`u ∈ _.final`]
           >> qexists_tac `u` >> fs[] >> rpt strip_tac
           >- (POP_ASSUM mp_tac >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
               >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
               >> first_x_assum (qspec_then `x'` mp_tac)
               >> Cases_on `x' ∈ x` >> fs[] >> rpt strip_tac
               >> fs[trns_correct_def]
               >> `e ∈ POW abstrAA.states`
                   by (qunabbrev_tac `realTrans` >> fs[])
               >> `e ∈ concr2AbstrGBA_states gba` by metis_tac[IN_INTER]
               >> POP_ASSUM mp_tac
               >> PURE_REWRITE_TAC[concr2AbstrGBA_states_def] >> simp[]
               >> strip_tac
               >> `?fls. lookup n gba.followers = SOME fls`
                   by metis_tac[wfg_def,domain_lookup]
               >> `(a,e') ∈ gba_trans abstrAA e`
                 by (qunabbrev_tac `realTrans` >> fs[] >> metis_tac[])
               >> `MEM (a,e')
                     (CAT_OPTIONS
                      (MAP
                       (λ(eL,i).
                         do
                         s_nL <- lookup i gba.nodeInfo;
                        SOME
                            (transformLabel (set aP) eL.pos_lab
                                            eL.neg_lab,set s_nL.frmls)
                            od) fls))` by metis_tac[]
               >> fs[CAT_OPTIONS_MEM,MEM_MAP] >> Cases_on `y` >> fs[]
               >> fs[]
               >> first_x_assum (qspec_then
                                 `concrEdge q.pos_lab q.neg_lab s_nL.frmls`
                                 mp_tac)
               >> strip_tac
               >> first_x_assum (qspec_then `u` mp_tac) >> simp[]
               >> `MEM u (graphStates g_AA)` by (
                    fs[concr2AbstrAA_def,concr2Abstr_final_def]
                    >> simp[graphStates_def,EXISTS_MEM,MEM_MAP]
                    >> metis_tac[SND,MEM_toAList]
                )
               >> simp[]
               >> `MEM_SUBSET q.pos_lab aP ∧ MEM_SUBSET q.neg_lab aP`
                  by metis_tac[aP_correct_def]
               >> simp[]
             >> `MEM_SUBSET s_nL.frmls (graphStates g_AA)` by (
                `set s_nL.frmls ∈ concr2AbstrGBA_states gba` by (
                    PURE_REWRITE_TAC[concr2AbstrGBA_states_def]
                    >> simp[] >> qexists_tac `s_nL`
                     >> metis_tac[MEM_toAList,domain_lookup]
                )
                >> `set s_nL.frmls ∈
                     POW (concr2AbstrAA (concrAA g_AA init aP)).states`
                    by metis_tac[IN_INTER]
                >> fs[concr2AbstrAA_def,concr2Abstr_states_def]
                >> fs[IN_POW] >> simp[MEM_SUBSET_SET_TO_LIST]
                >> simp[graphStates_def,SUBSET_DEF] >> strip_tac
                >> simp[MEM_MAP] >> strip_tac
                >> `x''' ∈
                     {x.frml |
                      ∃n. SOME x = lookup n g_AA.nodeInfo
                         ∧ n ∈ domain g_AA.nodeInfo}` by fs[SUBSET_DEF]
                >> fs[] >> qexists_tac `(n',x'''')` >> simp[]
                >> metis_tac[MEM_toAList]
             )
             >> `is_until u` by (
                  fs[concr2AbstrAA_def,concr2Abstr_final_def]
                  >> Cases_on `u` >> metis_tac[until_iff_final_def,is_until_def]
                )
             >> simp[]
             >> `set x''.frmls ∈
                     POW (concr2AbstrAA (concrAA g_AA init aP)).states` by (
                `set x''.frmls ∈ concr2AbstrGBA_states gba` by (
                   PURE_REWRITE_TAC[concr2AbstrGBA_states_def]
                   >> simp[] >> qexists_tac `x''`
                   >> metis_tac[MEM_toAList,domain_lookup]
                )
               >> metis_tac[IN_INTER]
                )
             >> strip_tac
             >> first_x_assum (qspec_then `set x''.frmls` mp_tac)
             >> simp[concr2AbstractEdge_def] >> fs[] >> strip_tac
             >> `MEM u
                  (get_acc_set final_trans
                   (concrEdge q.pos_lab q.neg_lab s_nL.frmls))`
                by metis_tac[concr2AbstrAA_def]
             >> qexists_tac `x''` >> simp[]
             >> qexists_tac `q` >> fs[] >> qexists_tac `s_nL` >> fs[]
             >> strip_tac
             >- metis_tac[concr2AbstrAA_def]
             >- metis_tac[]
              )
           >- (first_x_assum (qspec_then `x'` mp_tac) >> simp[]
               >> Q.HO_MATCH_ABBREV_TAC `(A ==> B) ==> B`
               >> `A` suffices_by fs[] >> qunabbrev_tac `A`
               >> `set q1.frmls ∈ concr2AbstrGBA_states gba` by (
                    PURE_REWRITE_TAC[concr2AbstrGBA_states_def]
                    >> simp[] >> qexists_tac `q1`
                    >> metis_tac[MEM_toAList,domain_lookup]
                )
               >> `(set q1.frmls ∈
                    POW (concr2AbstrAA (concrAA g_AA init aP)).states)
                   ∧ set q1.frmls ∈
                   reachableFromSetGBA
                   (GBA (POW (concr2AbstrAA (concrAA g_AA init aP)).states)
                        (concr2AbstrAA (concrAA g_AA init aP)).initial
                        (gba_trans (concr2AbstrAA (concrAA g_AA init aP)))
                        {acc_cond (concr2AbstrAA (concrAA g_AA init aP)) f ∩
                         {(e,a,e') |
                          (a,e') ∈
                           gba_trans (concr2AbstrAA (concrAA g_AA init aP)) e
                        ∧ e ∈
                        POW (concr2AbstrAA (concrAA g_AA init aP)).states} |
                         f |
                         f ∈ (concr2AbstrAA (concrAA g_AA init aP)).final}
                        (concr2AbstrAA (concrAA g_AA init aP)).alphabet)
                   (concr2AbstrAA (concrAA g_AA init aP)).initial`
                    by metis_tac[IN_INTER]
               >> simp[]
             >> first_x_assum
                 (qspec_then `concrEdge eL.pos_lab eL.neg_lab q2.frmls` mp_tac)
             >> simp[] >> strip_tac
             >> first_x_assum (qspec_then `u` mp_tac)
             >> first_x_assum (qspec_then `id1` mp_tac) >> simp[]
             >> first_x_assum (qspec_then `id1` mp_tac) >> simp[] >> strip_tac
             >> first_x_assum (qspec_then `eL` mp_tac) >> simp[] >> strip_tac
             >> first_x_assum (qspec_then `id2` mp_tac) >> simp[]
             >> `set q1.frmls ∈
                  concr2AbstrGBA_states gba` by (
                 PURE_REWRITE_TAC[concr2AbstrGBA_states_def]
                 >> simp[] >> qexists_tac `q1`
                 >> metis_tac[MEM_toAList,domain_lookup]
             )
             >> `set q1.frmls ∈
                   POW (concr2AbstrAA (concrAA g_AA init aP)).states` by (
                 metis_tac[IN_INTER]
             )
             >> simp[] >> strip_tac
             >> first_x_assum (qspec_then `u` mp_tac) >> simp[] >> strip_tac
             >> `MEM u (MAP FST (final_trans))` by metis_tac[]
             >> fs[MEM_MAP] >> Cases_on `y` >> fs[]
             >> `∃id nL.
                   (findNode (λ(i,l). l.frml = u) g_AA = SOME (id,nL))
                   ∧ is_until u` by metis_tac[valid_acc_def,FST]
             >> `is_until u ∧ MEM u (graphStates g_AA)` by (
                 simp[graphStates_def,MEM_MAP]
                 >> `MEM (id,nL) (toAList g_AA.nodeInfo)
                   ∧ (λ(i,l). l.frml = u) (id,nL)`
                     by metis_tac[FIND_LEMM2,findNode_def]
                 >> fs[] >> qexists_tac `(id,nL)` >> fs[]
             )
             >> simp[]
             >> `MEM_SUBSET eL.pos_lab aP ∧
                   MEM_SUBSET eL.neg_lab aP` by metis_tac[aP_correct_def]
             >> simp[]
             >> `MEM_SUBSET q2.frmls (graphStates g_AA)` by (
                 `set q2.frmls ∈ concr2AbstrGBA_states gba` by (
                 PURE_REWRITE_TAC[concr2AbstrGBA_states_def]
                 >> simp[] >> qexists_tac `q2`
                 >> metis_tac[MEM_toAList,domain_lookup]
                 )
                >> `set q2.frmls ∈
                    POW (concr2AbstrAA (concrAA g_AA init aP)).states`
                       by metis_tac[IN_INTER]
                >> fs[concr2AbstrAA_def,concr2Abstr_states_def]
                >> fs[IN_POW] >> simp[MEM_SUBSET_SET_TO_LIST]
                >> simp[graphStates_def,SUBSET_DEF] >> strip_tac
                >> simp[MEM_MAP] >> strip_tac
                >> `x'' ∈
                    {x.frml |
                       ∃n. SOME x = lookup n g_AA.nodeInfo
                       ∧ n ∈ domain g_AA.nodeInfo}` by fs[SUBSET_DEF]
                >> fs[] >> qexists_tac `(n,x''')` >> simp[]
                >> metis_tac[MEM_toAList]
                )
             >> simp[] >> rw[]
             >> first_x_assum (qspec_then `set q1.frmls` mp_tac) >> simp[]
             >> simp[concr2AbstractEdge_def]
             >> strip_tac
             >> fs[trns_correct_def]
             >> first_x_assum (qspec_then `id1` mp_tac) >> simp[] >> strip_tac
             >> `MEM (transformLabel (props f) eL.pos_lab eL.neg_lab,
                     set q2.frmls)
                   (CAT_OPTIONS
                        (MAP
                             (λ(eL',i).
                               do
                               s_nL <- lookup i gba.nodeInfo;
                              SOME
                                  (transformLabel (props f) eL'.pos_lab
                                                  eL'.neg_lab,set s_nL.frmls)
                                  od) fls))` suffices_by metis_tac[]
             >> simp[CAT_OPTIONS_MEM,MEM_MAP]
             >> qexists_tac `(eL,id2)` >> fs[]
              )
           >- (fs[concr2AbstrAA_def,concr2Abstr_final_def]
               >> Cases_on `u` >> metis_tac[until_iff_final_def,is_until_def]
              )
           >- (fs[concr2AbstrAA_def,concr2Abstr_final_def]
               >> simp[graphStates_def,MEM_MAP]
               >> qexists_tac `(n,x')` >> fs[] >> metis_tac[MEM_toAList]
              )
          )
      )
   >- (qunabbrev_tac `ALPH` >> fs[] >> simp[concr2AbstrAA_def])
  );

val EXPGBA_CORRECT = store_thm
  ("EXPGBA_CORRECT",
  ``!f concr_AA abstrAA.
  (expandAuto_init f = SOME concr_AA)
  ∧ (abstrAA = concr2AbstrAA concr_AA)
  ==> ?c_gba.
       (expandGBA_init concr_AA = SOME c_gba)
       ∧ (concr2AbstrGBA c_gba =
          removeStatesSimpl (vwaa2gba abstrAA))``,
  rpt gen_tac >> strip_tac
  >> `case expandGBA_init concr_AA of
        NONE => F
        | SOME c_gba =>
         concr2AbstrGBA c_gba = removeStatesSimpl (vwaa2gba abstrAA)`
     by (Cases_on `concr_AA` >> fs[] >> metis_tac[EXPGBA_CORRECT_LEMM])
  >> Cases_on `expandGBA_init concr_AA` >> fs[]
  );

val _ = export_theory()
