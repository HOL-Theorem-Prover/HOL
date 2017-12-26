open HolKernel Parse bossLib boolLib gfgTheory listTheory optionTheory pred_setTheory relationTheory pairTheory prim_recTheory set_relationTheory arithmeticTheory rich_listTheory

open sptreeTheory ltlTheory generalHelpersTheory concrGBArepTheory concrRepTheory waa2baTheory buechiATheory gbaSimplTheory alterATheory ltl2waaTheory waaSimplTheory

val _ = monadsyntax.temp_add_monadsyntax();
val _ = overload_on("monad_bind",``OPTION_BIND``);

val CONCR_ACC_SETS = store_thm
  ("CONCR_ACC_SETS",
   ``!h g_AA init acc aP.
  let abstrAA = concr2AbstrAA (concrAA g_AA init aP)
  in
     (abstrAA = removeStatesSimpl (ltl2waa h))
     ∧ (!f f_trns. MEM (f,f_trns) acc ==>
         ?id nL. (findNode (λ(i,l). l.frml = f) g_AA = SOME (id,nL))
               ∧ (SOME f_trns = concr_extrTrans g_AA id)
       )
     ∧ (!f. (is_until f ∧ MEM f (graphStates g_AA))
            ==> ?f_trns. MEM (f,f_trns) acc)
     ∧ wfg g_AA ∧ flws_sorted g_AA ∧ unique_node_formula g_AA
     ==>
     !ce u.
     let W_FINAL =
           λcE.
            (cE,
             CAT_OPTIONS
                 (MAP
                      (λ(f,f_trans).
                        if acc_cond_concr cE f f_trans then SOME f
                        else NONE) acc))
     in let aE = concr2AbstractEdge (set aP) ce
     in !qs.
         (aE ∈ d_conj_set {(q,abstrAA.trans q) | MEM q qs} (POW (set aP)))
         ∧ (!q. MEM q qs ==> MEM q (graphStates g_AA))
         ∧ (is_until u ∧ MEM u (graphStates g_AA))
         ∧ MEM_SUBSET ce.pos aP ∧ MEM_SUBSET ce.neg aP
         ==>
         (!qs. qs ∈ POW abstrAA.states
           ==> (MEM u ((SND o W_FINAL) ce) =
                ((qs,FST aE,SND aE) ∈ acc_cond abstrAA u)))``,
   fs[] >> rpt strip_tac >> simp[EQ_IMP_THM] >> rpt strip_tac
   >> fs[CAT_OPTIONS_MEM,MEM_MAP]
   >> qabbrev_tac `aa_red = removeStatesSimpl (ltl2waa h)`
   >> `(aa_red).alphabet = POW (set aP)`
       by fs[concr2AbstrAA_def,ALTER_A_component_equality]
   >> `isValidAlterA (aa_red)` by (
       metis_tac[LTL2WAA_ISVALID,REDUCE_STATE_IS_VALID]
   )
   >- (
    simp[acc_cond_def] >> qexists_tac `FST (concr2AbstractEdge (set aP) ce)`
    >> qexists_tac `SND (concr2AbstractEdge (set aP) ce)` >> fs[]
    >> `!q. MEM q qs ==> q ∈ aa_red.states` by (
        rpt strip_tac >> fs[concr2AbstrAA_def,ALTER_A_component_equality]
        >> fs[concr2Abstr_states_def]
        >> `q ∈ {x.frml |
                 ∃n. (SOME x = lookup n g_AA.nodeInfo)
                  ∧ n ∈ domain g_AA.nodeInfo}` suffices_by metis_tac[]
        >> simp[] >> `MEM q (graphStates g_AA)` by fs[]
        >> POP_ASSUM mp_tac >> PURE_REWRITE_TAC[graphStates_def]
        >> rpt strip_tac >> fs[MEM_MAP] >> qexists_tac `SND y'`
        >> fs[] >> Cases_on `y'` >> metis_tac[MEM_toAList,domain_lookup,SND]
    )
    >> rpt strip_tac
    >- (simp[IN_POW,SUBSET_DEF] >> rpt strip_tac >> fs[]
        >> `concr2AbstractEdge (set aP) ce ∈
              d_gen (aa_red) (set qs)`
             by simp[d_gen_def]
        >> `∃q' a' e'. q' ∈ set qs
              ∧ (a',e') ∈ (aa_red).trans q'
              ∧ x ∈ e'` by (
           Cases_on `concr2AbstractEdge (set aP) ce` >> fs[]
           >> metis_tac[D_GEN_A_E_LEMM3,FINITE_LIST_TO_SET])
        >> fs[isValidAlterA_def]
        >> `q' ∈ aa_red.states` by metis_tac[]
        >> metis_tac[IN_POW,SUBSET_DEF]
       )
    >- (simp[IN_POW,SUBSET_DEF] >> rpt strip_tac >> fs[]
        >> `concr2AbstractEdge (set aP) ce ∈
              d_gen (aa_red) (set qs)`
            by simp[d_gen_def]
        >> Cases_on `concr2AbstractEdge (set aP) ce` >> fs[]
        >> Cases_on `ce` >> fs[concr2AbstractEdge_def]
        >> metis_tac[TRANSFORMLABEL_AP,SUBSET_DEF,IN_POW]
       )
    >- (Cases_on `u ∈ SND (concr2AbstractEdge (set aP) ce)` >> fs[]
        >> Cases_on `y` >> fs[] >> rw[]
        >> rename[`MEM (f,f_trns) acc`] >> fs[acc_cond_concr_def]
        >- (Cases_on `ce` >> fs[concr2AbstractEdge_def])
        >- (Cases_on `EXISTS (λp. MEM p ce.neg) ce.pos` >> fs[]
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
            >- (fs[EXISTS_MEM]
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
         >- (`EXISTS
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
   >- (`?u_trns. MEM (u,u_trns) acc` by metis_tac[]
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
           >> qexists_tac `y` >> fs[] >> Cases_on `ce` >> Cases_on `y`
           >> fs[concr2AbstractEdge_def, MEM_SUBSET_SET_TO_LIST]
           >> `a ⊆ α` by rw[]
           >> 

 >> Cases_on `a` >> Cases_on

)




)



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
             expandGBA g_AA acc (ids ++ new_ids) G2
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
       >> qabbrev_tac `t_with_acc =
             MAP
                 (λcE.
                      (cE,
                       CAT_OPTIONS
                           (MAP
                                (λ(f,f_trans).
                                  if acc_cond_concr cE f f_trans
                                  then SOME f
                                  else NONE) acc))) t`
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
                    (ONLY_MINIMAL tlg_concr t_with_acc))`
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
        )
      )
   );

val expandGBA_init_def = Define`
  expandGBA_init (concrAA g_AA initAA props) =
    let initNodes = MAP (λi_list.
                          let suc_nLabels = MAP (λi. lookup i g_AA.nodeInfo) i_list
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
         | SOME graph => SOME (concrGBA graph initIds props)
         | NONE => NONE `;


val EXPGBA_SOME_WFG = store_thm
  ("EXPGBA_SOME_WFG",
   ``!g_AA acc ids G.
        wfg G
        ∧ (!i. MEM i ids ==> i ∈ (domain G.nodeInfo))
        ==> (?gba. (expandGBA g_AA acc ids G = SOME gba) ∧ wfg gba)``,
   HO_MATCH_MP_TAC (theorem "expandGBA_ind")
   >> rpt strip_tac >> fs[expandGBA_def]
   >> Q.HO_MATCH_ABBREV_TAC
      `?gba. ((case lookup id G.nodeInfo of
          | NONE => NONE
          | SOME current_node =>
            (λ(new_ids,G1).
              do G2 <- FOLDR ADDE (SOME G1) (MAP toEL (TRNS current_node)) ;
                 expandGBA g_AA acc (ids ++ new_ids) G2
              od)
             (FOLDR ADDN ([],G)
                 (FILTER (λqs. ~inGBA G qs)
                    (MAP (λ(cE,fs). cE.sucs) (TRNS current_node))))) = SOME gba)
          ∧ wfg gba`
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
   >> `∃gba. expandGBA g_AA acc (ids ⧺ new_ids) G2 = SOME gba ∧ wfg gba`
       by metis_tac[]
   >> metis_tac[]
  );

val EXPGBA_GRAPH_REACHABLE = store_thm
  ("EXPGBA_GRAPH_REACHABLE",
   ``!f init aP g_AA acc ids g.
      let abstrAA = concr2AbstrAA (concrAA g_AA init aP)
      in
         isWeakAlterA abstrAA ∧ isValidAlterA abstrAA
       ∧ (FINITE abstrAA.states) ∧ (abstrAA = removeStatesSimpl (ltl2waa f))
       ∧ (abstrAA.alphabet = POW (set aP)) ∧ (wfg g_AA)
       ∧ (unique_node_formula g_AA) ∧ (flws_sorted g_AA)
       ==>
     (!g2.
       (!i x. MEM i ids ∧ (lookup i g.nodeInfo = SOME x)
            ==> set x.frmls ∈
                 reachableFromSetGBA (waa2gba abstrAA) {set q | inGBA g q})
       ∧ (!x. inGBA g x
              ==> set x ∈ reachableFromSetGBA
                       (waa2gba abstrAA) (waa2gba abstrAA).initial)
       ∧ (!i. MEM i ids ==> i ∈ domain g.nodeInfo)
       ∧ (expandGBA g_AA acc ids g = SOME g2)
       ∧ (wfg g)
       ∧ (!x. inGBA g x ==> (set x ∈ POW abstrAA.states))
       ∧ (!i n. i ∈ (domain g.nodeInfo) ∧ (lookup i g.nodeInfo = SOME n)
             ==> ALL_DISTINCT n.frmls
         )
       ==> (!x. inGBA g2 x
                ==> ((set x ∈ reachableFromSetGBA (waa2gba abstrAA)
                        (waa2gba abstrAA).initial)
                         ∧ (set x ∈ (waa2gba abstrAA).states))))``,
    gen_tac >> gen_tac >> gen_tac
    >> HO_MATCH_MP_TAC (theorem "expandGBA_ind") >> rpt strip_tac
    >- (fs[] >> rpt strip_tac >> fs[expandGBA_def]
        >> first_x_assum (qspec_then `x` mp_tac) >> simp[] >> rpt strip_tac
        >> fs[reachableFromSetGBA_def]
        >> qabbrev_tac `abstr_gba =
               waa2gba (concr2AbstrAA (concrAA g_AA init aP))`
        >> `isValidGBA abstr_gba` by metis_tac[WAA2GBA_ISVALID]
        >> `abstr_gba.initial ⊆ abstr_gba.states` by metis_tac[isValidGBA_def]
        >> metis_tac[SUBSET_DEF,REACHABLE_GBA_LEMM]
       )
    >- (fs[] >> strip_tac >> strip_tac >> strip_tac >> gen_tac
        >> strip_tac
        >> `?node. lookup id g.nodeInfo = SOME node` by metis_tac[domain_lookup]
        >> first_x_assum (qspec_then `node` mp_tac) >> simp[]
        >> strip_tac
        >> qabbrev_tac `TRNS =
             ONLY_MINIMAL tlg_concr
              (MAP
               (λcE.
                 (cE,
                  CAT_OPTIONS
                      (MAP
                           (λ(f,f_trans).
                             if acc_cond_concr cE f f_trans then
                                 SOME f
                             else NONE) acc)))
               (gba_trans_concr
                    (CAT_OPTIONS
                         (MAP (concr_extrTrans g_AA)
                              (CAT_OPTIONS
                                   (MAP
                                        (λf.
                                             OPTION_MAP FST
                                             (findNode
                                                  (λ(i,l). l.frml = f)
                                                  g_AA))
                                        node.frmls))))))`
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
        >> rename[`wfg G2`] >> first_x_assum (qspec_then `G2` mp_tac) >> simp[]
        >> strip_tac >> first_x_assum (qspec_then `g2` mp_tac) >> simp[]
        >> Q.HO_MATCH_ABBREV_TAC `(A ==> B) ==> C`
        >> `B ==> C` by metis_tac[]
        >> `A` suffices_by fs[] >> qunabbrev_tac `A` >> fs[]
        >> qabbrev_tac `abstr_gba =
             waa2gba (concr2AbstrAA (concrAA g_AA init aP))`
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
        >> rpt conj_tac
        >- (rpt gen_tac >> Cases_on `i ∈ (domain g.nodeInfo)`
            >> rpt strip_tac
            >- metis_tac[]
            >- (rename[`lookup i G2.nodeInfo = SOME n`]
                >> `lookup i g.nodeInfo = SOME n` by metis_tac[]
                >> `MEM n.frmls NEW_NODES` by metis_tac[SOME_11]
                >> qunabbrev_tac `NEW_NODES` >> fs[MEM_FILTER]
                >> qunabbrev_tac `TRNS` >> fs[MEM_MAP,ONLY_MINIMAL_MEM]
                >> Q.HO_MATCH_ABBREV_TAC `
                    set cE.sucs ∈
                      reachableFromSetGBA
                      (waa2gba (removeStatesSimpl (ltl2waa f)))
                      (IN_G ∪ (set (MAP set (FILTER (λqs. ~inGBA g qs)
                                                    (MAP TO_SUCS
                                                    (ONLY_MINIMAL tlg_concr
                                                     (MAP W_FINAL TRNS)))))))`
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
                            POW (removeStatesSimpl (ltl2waa f)).states`
                           by metis_tac[]
                       >> fs[concr2AbstrAA_def]
                       >> `f' ∈ (removeStatesSimpl (ltl2waa f)).states`
                          by metis_tac[MEM,IN_POW,SUBSET_DEF]
                       >> `f' ∈ concr2Abstr_states g_AA` by fs[ALTER_A_component_equality]
                       >> fs[concr2Abstr_states_def,findNode_def]
                       >> `(λ(i,l). l.frml = f') (n',x')` by fs[]
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
                    by metis_tac[]
                >> `abstr_ce ∈
                    d_conj_set
                     (set (MAP (λ(q,d).
                              (q,set (MAP
                                       (concr2AbstractEdge (set aP)) d))) zpd))
                       (POW (set aP))`
                     by metis_tac[MAP_ZIP,LENGTH_COUNT_LIST,GBA_TRANS_LEMM]
                >> simp[reachableFromSetGBA_def,reachableFromGBA_def,
                        stepGBA_def]
                >> simp[waa2gba_def,gba_trans_def]
                >> simp[d_gen_def,removeStatesSimpl_def]
                >> qexists_tac `set node.frmls` >> simp[] >> strip_tac
                >- (
                 Q.HO_MATCH_ABBREV_TAC `Q^* (set node.frmls) (set cE.sucs)`
                 >> `Q (set node.frmls) (set cE.sucs)`
                       suffices_by metis_tac[RTC_SUBSET]
                 >> qunabbrev_tac `Q` >> simp[] >> qexists_tac `FST abstr_ce`
                 >> simp[minimal_elements_rrestrict]
                 >> simp[minimal_elements_def] (* >> rpt strip_tac *)
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
                 >> `{(q,(removeStatesSimpl (ltl2waa f)).trans q) |
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
                 >> rpt strip_tac
                 >- (
                   qunabbrev_tac `abstr_ce` >> fs[]
                   >> Cases_on `cE` >> fs[concrEdge_component_equality]
                   >> fs[concr2AbstractEdge_def] >> metis_tac[]
                 )
                 >- (
                   rename[`(FST abstr_ce,set cE.sucs) = edge`]
                   >> `edge ∈
                        d_conj_set
                        (set
                          (MAP (λ(q,d). (q,set (MAP (concr2AbstractEdge (set aP)) d)))
                               zpd)) (POW (set aP))` by metis_tac[]
                   >> fs[]
                   >> `edge ∈
                        set (MAP (concr2AbstractEdge (set aP)) TRNS)` by (
                      IMP_RES_TAC GBA_TRANS_LEMM
                      >> first_x_assum (qspec_then `set aP` mp_tac) >> fs[]
                      >> rpt strip_tac >> qunabbrev_tac `TRNS` >> fs[]
                      >> metis_tac[MAP_ZIP]
                   )
                   >> POP_ASSUM mp_tac >> simp[MEM_MAP] >> strip_tac
                   >> rename[`MEM c_edge TRNS`] >> fs[]
                   >> `c_edge = cE \/ ~tlg_concr y (W_FINAL c_edge)` by (
                       first_x_assum (qspec_then `W_FINAL c_edge` mp_tac)
                       >> simp[]>> rpt strip_tac >> fs[]
                       >> qunabbrev_tac `W_FINAL` >> fs[]
                       >> Cases_on `c_edge = cE` >> fs[]
                   )
                   >- (rw[] >> qunabbrev_tac `abstr_ce` >> fs[]
                       >> Cases_on `cE` >> fs[concrEdge_component_equality]
                       >> fs[concr2AbstractEdge_def] >> metis_tac[]
                      )
                   >- (
                   POP_ASSUM mp_tac >> simp[tlg_concr_def] >> 
)

)




                 >> qexists_tac `(q_i,concr_extrTrans)
)
)
)

                 >> strip_tac
                 >- ()
                 >- (simp[removeStatesSimpl_def])


)
                >- (disj1_tac >> qunabbrev_tac `IN_G` >> fs[]
                    >> `inGBA g node.frmls` by (
                         simp[inGBA_def,EXISTS_MEM]
                         >> qexists_tac `node` >> simp[MEM_EQUAL_SET,MEM_MAP]
                         >> metis_tac[MEM_toAList,SND]
                     )
                    >> metis_tac[]
                   )


(*                ) *)
(* ) *)


(*                >> `MEM n.frml *)
(*                      (gba_trans_concr *)
(*                                                     (CAT_OPTIONS *)
(*                                                          (MAP (concr_extrTrans g_AA) *)
(*                                                               (CAT_OPTIONS *)
(*                                                                    (MAP *)
(*                                                                         (λf. *)
(*                                                                              OPTION_MAP FST *)
(*                                                                              (findNode (λ(i,l). l.frml = f) *)
(*                                                                                        g_AA)) node.frmls))))) *)

(* ) *)


(* ) *)



(* val EXPGBA_CORRECT = store_thm *)
(*   ("EXPGBA_CORRECT", *)
(*    ``!g_AA initAA aP. *)
(*     let c_AA = concrAA g_AA initAA aP *)
(*     in let abstr_AA = concr2AbstrAA c_AA *)
(*     in wfg g_AA ∧ isWeakAlterA abstr_AA *)
(*         ==> *)
(*         case expandGBA_init c_AA of *)
(*           | NONE => F *)
(*           | SOME c_gba => (concr2AbstrGBA c_gba = waa2gba (concr2AbstrAA c_AA))``, *)
(*    fs[] >> rpt strip_tac >> simp[expandGBA_init_def] *)
(*    >> qabbrev_tac `addedInit:(α nodeLabelGBA, α edgeLabelGBA) gfg = *)
(*         FOLDR (λn g. addNodeToGBA g n) empty *)
(*               (MAP *)
(*                    (λi_list. *)
(*                         MAP (λl. l.frml) *)
(*                         (CAT_OPTIONS *)
(*                              (MAP (λi. lookup i g_AA.nodeInfo) *)
(*                                   i_list))) initAA)` *)
(*    >> qabbrev_tac `final_trans = *)
(*         FOLDR *)
(*              (λ(id,x) sF. *)
(*                case concr_extrTrans g_AA id of *)
(*                    NONE => sF *)
(*                  | SOME c_t => if is_until x then (x,c_t)::sF else sF) [] *)
(*              (graphStatesWithId g_AA)` *)
(*    >> `!i. MEM i (MAP FST (toAList addedInit.nodeInfo)) *)
(*              ==> (i ∈ domain addedInit.nodeInfo)` by ( *)
(*        rpt strip_tac >> qunabbrev_tac `addedInit` >> fs[MEM_MAP] *)
(*        g>> Cases_on `y` >> fs[] *)
(*        >> metis_tac[MEM_toAList,domain_lookup] *)
(*    ) *)
(*    >> `wfg addedInit` by ( *)
(*        qunabbrev_tac `addedInit` >> fs[] *)
(*        >> `!l. wfg (FOLDR (λn g. addNodeToGBA g n) *)
(*                           (empty:(α nodeLabelGBA, α edgeLabelGBA) gfg) *)
(*                           l)` by ( *)
(*            Induct_on `l` >> fs[] >> rpt strip_tac *)
(*            >> metis_tac[ADDNODE_GBA_WFG] *)
(*        ) *)
(*        >> metis_tac[] *)
(*    ) *)
(*    >> IMP_RES_TAC EXPGBA_SOME_WFG >> first_x_assum (qspec_then `g_AA` mp_tac) *)
(*    >> rpt strip_tac >> first_x_assum (qspec_then `final_trans` mp_tac) >> simp[] *)
(*    >> rpt strip_tac >> fs[] >> simp[concr2AbstrGBA_def] *)
(*    >> simp[waa2gba_def] *)
(*    >> Q.HO_MATCH_ABBREV_TAC `STATES ∧ INIT ∧ TRANS ∧ FINAL ∧ ALPH` *)
(*    >> rpt strip_tac *)
(*    >- ( *)
    
(* ) *)


(* ) *)


