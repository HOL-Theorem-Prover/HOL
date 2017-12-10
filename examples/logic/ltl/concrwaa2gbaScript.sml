open HolKernel Parse bossLib boolLib gfgTheory listTheory optionTheory pred_setTheory relationTheory pairTheory

open sptreeTheory ltlTheory generalHelpersTheory concrGBArepTheory

val _ = monadsyntax.temp_add_monadsyntax();
val _ = overload_on("monad_bind",``OPTION_BIND``);

val possibleGBA_states_def = Define`
  possibleGBA_states g_AA =
     {qs | !q. MEM q qs ==> MEM q (graphStates g_AA) ∧ ALL_DISTINCT qs }`;

val decr_expGBA_rel_def = Define `
  decr_expGBA_rel (g_AA1,acc1,ids1,G1) (g_AA2,acc2,ids2,G2) =
     let m =
      λg. {x | inGBA g x } ∩ possibleGBA_states g_AA1
     in
      (g_AA1 = g_AA2)
    ∧ (NoNodeProcessedTwice
          (possibleGBA_states g_AA1) m (G1,ids1) (G2,ids2))`;

val DECR_EXPGBA_REL_WF = store_thm
  ("DECR_EXPGBA_REL_WF",
   ``WF decr_expGBA_rel``,
   qabbrev_tac `
      lifted_NNPT =
         λB:(α ltl_frml list -> bool)
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
                 (λg. {x | inGBA g x } ∩ B)
                 (m,l) (m2,l2)`
   >> `!B. FINITE B ==> WF (lifted_NNPT B)` by (
        rpt strip_tac
        >> `lifted_NNPT B =
             inv_image
              (NoNodeProcessedTwice B (λg.{x | inGBA g x} ∩ B))
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
       >> `{qs | ∀q'. MEM q' qs ⇒ MEM q' (graphStates q) ∧ ALL_DISTINCT qs} =
            {qs | MEM_SUBSET qs (graphStates q) ∧ ALL_DISTINCT qs}` by (
           simp[SET_EQ_SUBSET,SUBSET_DEF,MEM_SUBSET_SET_TO_LIST]
           >> rpt strip_tac >> Cases_on `x` >> fs[ALL_DISTINCT]
       )
       >> rw[] >> metis_tac[SET_OF_SUBLISTS_FINITE]
   )
   >> simp[] >> rpt strip_tac
   >> `!x y. C x y ==> B x y` suffices_by metis_tac[WF_SUBSET]
   >> qunabbrev_tac `B` >> qunabbrev_tac `C` >> rpt strip_tac >> fs[]
   >> Cases_on `x` >> Cases_on `y` >> qunabbrev_tac `lifted_NNPT` >> fs[]
   >> Cases_on `r` >> Cases_on `r'` >> fs[] >> Cases_on `r` >> Cases_on `r''`
   >> fs[] >> fs[decr_expGBA_rel_def]
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
   )`
  (WF_REL_TAC `decr_expGBA_rel`
   >- (metis_tac[DECR_EXPGBA_REL_WF])
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
       >> Q.HO_MATCH_ABBREV_TAC
           `(M G2 ⊂ M G) \/ (M G2 = M  G ∧ EQ_LENGTH)`
       >> `M G2 ⊆ M G` by (
            qunabbrev_tac `M` >> fs[]
            >> `{x | inGBA G x} ⊆ {x | inGBA G2 x}` suffices_by (
                simp[SUBSET_DEF] >> rpt strip_tac >> fs[]
                >> metis_tac[]
            )
            >> 

)

)

)
;

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
