open HolKernel Parse bossLib boolLib gfgTheory listTheory optionTheory pred_setTheory relationTheory pairTheory prim_recTheory set_relationTheory arithmeticTheory

open sptreeTheory ltlTheory generalHelpersTheory concrGBArepTheory

val _ = monadsyntax.temp_add_monadsyntax();
val _ = overload_on("monad_bind",``OPTION_BIND``);

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

(*TODO: prove termination*)
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
                          let suc_nLabels = MAP (λn. lookup i g_AA.nodeInfo)
                          in MAP (λl. l.frml) (CAT_OPTIONS suc_nLabels)
                        ) initAA
    in let G0 = FOLDR addNodeToGraph empty initNodes
    in let initIds = MAP FST (toAList G0)
    in let acc_sets = FILTER is_until (graphStates g_AA)
    in let graph = expandGBA g_AA acc_sets initIds G0
    in concrGBA graph initIds props`;
