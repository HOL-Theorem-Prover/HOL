open HolKernel Parse bossLib boolLib gfgTheory listTheory optionTheory pred_setTheory

open alterATheory sptreeTheory ltlTheory generalHelpersTheory

val _ = new_theory "concrRep";

val _ = monadsyntax.temp_add_monadsyntax();
val _ = overload_on("monad_bind",``OPTION_BIND``);

val _ = Datatype`
  nodeLabelAA = <| frml : α ltl_frml ;
                   is_final : bool
                 |>`;

val _ = Datatype`
  edgeLabelAA = <| edge_grp : num ;
                   pos_lab : (α list) ;
                   neg_lab : (α list)
                 |>`;

val _ = Datatype`
  concrAA = <| graph : (α nodeLabelAA, α edgeLabelAA) gfg ;
               init : (num list) list ;
               atomicProp : α list
            |>`;

val concr2Abstr_states_def = Define`
  concr2Abstr_states graph =
     { x.frml | SOME x ∈
                (IMAGE (\n. lookup n graph.nodeInfo) (domain graph.nodeInfo))}`;

val concr2Abstr_init_def = Define`
  concr2Abstr_init concrInit graph =
     LIST_TO_SET
         (MAP
          (\l. {x.frml |
                MEM x (CAT_OPTIONS (MAP (\n. lookup n graph.nodeInfo) l)) })
          concrInit)`;

val concr2Abstr_final_def = Define`
  concr2Abstr_final graph =
     {x.frml | SOME x ∈
                 (IMAGE (\n. lookup n graph.nodeInfo) (domain graph.nodeInfo))
               ∧ x.is_final}`;

val _ = Datatype`
  concrEdge = <| pos : (α list) ;
                 neg : (α list) ;
                 sucs : (α ltl_frml) list |>`;

val transformLabel_def = Define`
  transformLabel aP pos neg =
   FOLDR (\a sofar. (char (POW aP) a) ∩ sofar)
         (FOLDR (\a sofar. (char_neg (POW aP) a) ∩ sofar) (POW aP) neg) pos`;

val concr2AbstractEdge_def = Define`
  concr2AbstractEdge aP (concrEdge pos neg sucs) =
      (transformLabel aP pos neg, set sucs)`;

val extractTrans_def = Define`
  extractTrans graph s =
     let sucs = OPTION_TO_LIST
                 (do node <- findNode (λ(n,l). l.frml = s) graph ;
                     lookup node graph.followers
                  od
                 )
     in { edge | ?label.
                 let labelSucs =
                     { suc.frml
                     | ?sucId. MEM (label,sucId) sucs
                        ∧ SOME suc = lookup sucId graph.nodeInfo
                     }
                 in (edge = (label.edge_grp, label.pos_lab,
                             label.neg_lab, labelSucs)) }`;

val concr2AbstrAA = Define`
  concr2AbstrAA (concrAA g init prop) =
    ALTER_A
        (concr2Abstr_states g)
        (concr2Abstr_init init g)
        (concr2Abstr_final g)
        (POW (LIST_TO_SET prop))
        (\f. IMAGE (λ(i,p,n,e). (transformLabel (props f) p n,e))
                   (extractTrans g f))`;

val graphStates_def = Define
 `graphStates g = MAP ((\l. l.frml) o SND) (toAList g.nodeInfo)`;

val GRAPHSTATES_EMPTY = store_thm
  ("GRAPHSTATES_EMPTY",
   ``graphStates empty = []``,
   simp[graphStates_def,toAList_def,empty_def,foldi_def]
  );

val GRAPHSTATES_CONCR_LEMM = store_thm
  ("GRAPHSTATES_CONCR_LEMM",
   ``!g. set (graphStates g) = concr2Abstr_states g``,
   rpt strip_tac >> simp[graphStates_def,concr2Abstr_states_def]
   >> simp[SET_EQ_SUBSET,SUBSET_DEF,MEM_MAP] >> rpt strip_tac
    >- (qexists_tac `SND y` >> simp[]
        >> fs[MEM_toAList,domain_lookup] >> rw[]
        >> Cases_on `y` >> fs[MEM_toAList] >> metis_tac[]
       )
    >- (qexists_tac `(n,x')` >> simp[] >> simp[MEM_toAList])
  );

val autoStates_def = Define`
  autoStates (concrAA g i aP) = graphStates g`;

val inAuto_def = Define`
  inAuto aut f = MEM f (autoStates aut)`;

val IN_AUTO_FINITE = store_thm
  ("IN_AUTO_FINITE",
   ``!aut. FINITE (LIST_TO_SET (autoStates aut))``,
   rpt strip_tac >> metis_tac[FINITE_LIST_TO_SET]
  );

val addFrmlToGraph_def = Define`
   (addFrmlToGraph g (U f1 f2) =
       if MEM (U f1 f2) (MAP ((λl. l.frml) ∘ SND) (toAList g.nodeInfo))
       then g
       else addNode <| frml := (U f1 f2); is_final := T |> g)
 ∧ (addFrmlToGraph g f =
       if MEM f (MAP ((λl. l.frml) ∘ SND) (toAList g.nodeInfo))
       then g
       else addNode <| frml := f; is_final := F |> g)`;

val ADDFRML_LEMM = store_thm
  ("ADDFRML_LEMM",
   ``!g f. MEM f (graphStates (addFrmlToGraph g f))``,
   rpt strip_tac >> Cases_on `MEM f (graphStates g)`
    >- (Cases_on `f` >> fs[addFrmlToGraph_def,graphStates_def])
    >- (Cases_on `?f1 f2. f = U f1 f2`
         >- (fs[addFrmlToGraph_def] >> rw[]
             >> fs[graphStates_def,MEM_MAP]
             >> Cases_on `∃y. U f1 f2 = (SND y).frml
                        ∧ MEM y (toAList g.nodeInfo)` >> fs[]
              >- metis_tac[]
              >- (fs[addNode_def,MEM_toAList]
                  >> qexists_tac `(g.next,<|frml := U f1 f2; is_final := T|>)`
                  >> fs[MEM_toAList] >> rw[] >> metis_tac[])
            )
         >- (qabbrev_tac `el = (g.next,<|frml := f; is_final := F|>)`
             >> Cases_on `f` >> fs[addFrmlToGraph_def, graphStates_def,MEM_MAP]
             >> fs[addNode_def,MEM_toAList]
             >> qexists_tac `el` >> qunabbrev_tac `el` >> fs[MEM_toAList]
             >> rw[] >> metis_tac[]
            )
       )
  );

val ADDFRML_LEMM_AUT = store_thm
  ("ADDFRML_LEMM_AUT",
   ``!g i aP f. inAuto (concrAA (addFrmlToGraph g f) i aP) f``,
   metis_tac[inAuto_def,autoStates_def,ADDFRML_LEMM]
  );

val addEdgeToGraph_def = Define`
  addEdgeToGraph f (concrEdge pos neg sucs) g =
    let sucIds = CAT_OPTIONS (MAP (\s. findNode (λ(n,l). l.frml = s) g) sucs)
    in do nodeId <- findNode (λ(n,l). l.frml = f) g;
           oldSucPairs <- lookup nodeId g.followers ;
           oldSucs <- SOME (MAP FST oldSucPairs);
           lstGrpId <- SOME (if oldSucs = [] then 0 else (HD oldSucs).edge_grp) ;
           unfolded_edges <- SOME
             (MAP (\i. (<| edge_grp := lstGrpId + 1;
                          pos_lab := pos ;
                          neg_lab := neg ; |>,i)) sucIds);
           FOLDR (\e g_opt. do g_int <- g_opt ;
                               newGraph <- addEdge nodeId e g_int;
                               SOME newGraph
                            od)
                 (SOME g) unfolded_edges
        od`;

val ADDFRML_WFG = store_thm
  ("ADDFRML_WFG",
   ``!g f. wfg g ==> wfg (addFrmlToGraph g f)``,
   rpt strip_tac >> Cases_on `MEM f (graphStates g)`
   >> Cases_on `f` >> fs[addFrmlToGraph_def,graphStates_def]
  );

val until_iff_final_def = Define`
    until_iff_final g =
           !id node. (lookup id g.nodeInfo = SOME node)
               ==> ((?f1 f2. node.frml = U f1 f2) = node.is_final)`;

val ADDFRML_LEMM2 = store_thm
  ("ADDFRML_LEMM2",
   ``!g f. wfg g ==>
      (set (graphStates (addFrmlToGraph g f)) = set (graphStates g) ∪ {f}
    ∧ (!id. IS_SOME (lookup id g.nodeInfo)
            ==> (lookup id g.nodeInfo
                 = lookup id (addFrmlToGraph g f).nodeInfo))
    ∧ (until_iff_final g ==> until_iff_final (addFrmlToGraph g f)))``,
   simp[SET_EQ_SUBSET] >> rpt strip_tac
    >- (simp[SUBSET_DEF,UNION_DEF] >> rpt strip_tac
        >> Cases_on `MEM x (graphStates g)` >> fs[]
        >> `!q b. MEM q
                 (graphStates (addNode <|frml := f; is_final := b|> g))
                 ==> ((q = f) \/ MEM q (graphStates g))` by (
             rpt strip_tac >> fs[graphStates_def,MEM_MAP] >> Cases_on `y'`
             >> fs[MEM_toAList] >> Cases_on `r.frml = f` >> fs[]
             >> qexists_tac `(q',r)`
             >> simp[] >> fs[MEM_toAList,addNode_def]
             >> fs[lookup_insert] >> Cases_on `q' = g.next` >> fs[]
             >> fs[theorem "nodeLabelAA_component_equality"]
         )
        >> Cases_on `MEM f (graphStates g)` >> fs[]
        >> Cases_on `f` >> fs[addFrmlToGraph_def,inAuto_def]
        >> metis_tac[]
       )
    >- (simp[SUBSET_DEF] >> rpt strip_tac >> Cases_on `MEM f (graphStates g)`
        >- (Cases_on `f` >> fs[addFrmlToGraph_def,graphStates_def])
        >- (Cases_on `f` >> fs[addFrmlToGraph_def,addNode_def,graphStates_def]
            >> `~(g.next ∈ domain g.nodeInfo)` by (
                  fs[wfg_def] >> metis_tac[]
             )
            >> fs[insert_def,MEM_MAP] >> qexists_tac `y` >> simp[]
            >> Cases_on `y` >> rw[MEM_toAList]
            >> Cases_on `q = g.next` >> fs[lookup_insert,MEM_toAList]
            >> (`lookup q g.nodeInfo = NONE` by metis_tac[lookup_NONE_domain]
                >> rw[] >> fs[MEM_toAList])
           )
       )
    >- (`wfg (addFrmlToGraph g f)` by metis_tac[ADDFRML_WFG]
        >> metis_tac[ADDFRML_LEMM]
       )
    >- (Cases_on `f` >> simp[addFrmlToGraph_def] >> rw[]
        >> `?node. lookup id g.nodeInfo = SOME node` by fs[IS_SOME_EXISTS]
        >> `id ∈ domain g.nodeInfo` by fs[domain_lookup]
        >> simp[addNode_def,lookup_insert] >> fs[wfg_def]
        >> `~ (id = g.next)` by (
             first_x_assum (qspec_then `id` mp_tac) >> simp[]
         )
        >> fs[]
       )
    >- (fs[until_iff_final_def] >> rpt strip_tac
        >> Cases_on `MEM f (MAP ((λl. l.frml) ∘ SND) (toAList g.nodeInfo))`
          >- (Cases_on `f`
              >> fs[addFrmlToGraph_def] >> metis_tac[]
             )
          >- (Cases_on `id = g.next`
              >- (Cases_on `f`
                  >> fs[addFrmlToGraph_def,addNode_def,lookup_insert]
                  >> Cases_on `node.frml` >> rw[] >> fs[]
                 )
              >- (Cases_on `f`
                  >> fs[addFrmlToGraph_def,addNode_def,lookup_insert]
                  >> metis_tac[]
                 )
             )
       )
  );

val ADDFRML_FOLDR_LEMM = store_thm
  ("ADDFRML_FOLDR_LEMM",
   ``!g fs. wfg g ==>
      (set (graphStates g) ∪ set fs =
         set (graphStates (FOLDR (\f g. addFrmlToGraph g f) g fs))
         ∧ wfg (FOLDR (\f g. addFrmlToGraph g f) g fs)
         ∧ (!id. IS_SOME (lookup id g.nodeInfo)
                 ==> (lookup id g.nodeInfo
                      = lookup id
                          (FOLDR (\f g. addFrmlToGraph g f) g fs).nodeInfo))
         ∧ (until_iff_final g
             ==> until_iff_final (FOLDR (\f g. addFrmlToGraph g f) g fs)))``,
   gen_tac >> Induct_on `fs` >> rpt strip_tac
   >> fs[FOLDR]
    >- (`set (graphStates
                  (addFrmlToGraph (FOLDR (λf g. addFrmlToGraph g f) g fs) h))
        = set (graphStates ((FOLDR (λf g. addFrmlToGraph g f) g fs))) ∪ {h}`
          by metis_tac[ADDFRML_LEMM2]
       >> `set (graphStates g) ∪ (h INSERT (set fs))
           = set (graphStates g) ∪ set fs  ∪ {h}` suffices_by metis_tac[]
       >> fs[INSERT_DEF,UNION_DEF] >> simp[SET_EQ_SUBSET,SUBSET_DEF]
       >> rpt strip_tac >> metis_tac[]
      )
     >- metis_tac[ADDFRML_WFG]
     >- metis_tac[ADDFRML_LEMM2]
     >- metis_tac[ADDFRML_LEMM2]
  );

(* val ADDEDGE_LEMM = store_thm *)
(*   ("ADDEDGE_LEMM", *)
(*    ``!g f e aP. wfg g ∧ MEM f (graphStates g) *)
(*         ==> (?g2. (addEdgeToGraph f e g = SOME g2) ∧ wfg g2 *)
(*           ∧ (g.nodeInfo = g2.nodeInfo) *)
(*           ∧ (?i. extractTrans g2 f *)
(*                  = extractTrans g f ∪ { (i, e.pos,e.neg,set e.sucs) }))``, *)
(*    rpt strip_tac >> Cases_on `e` >> fs[addEdgeToGraph_def] *)
(*    >> fs[graphStates_def,MEM_MAP] >> simp[findNode_def] *)
(*    >> Q.HO_MATCH_ABBREV_TAC *)
(*        `?x. (?nodeId. A nodeId ∧ ?oSP. P oSP x nodeId) ∧ Q x` *)
(*    >> `?nodeId. A nodeId ∧ ?oSP x. P oSP x nodeId ∧ Q x` *)
(*        suffices_by metis_tac[SWAP_EXISTS_THM] *)
(*    >> qunabbrev_tac `P` >> qunabbrev_tac `A` >> fs[] *)
(*    >> `?q. (FIND (λ(n,l). l.frml = (SND y).frml) (toAList g.nodeInfo) = SOME q) *)
(*          ∧ ((λ(n,l). l.frml = (SND y).frml) q)` by ( *)
(*        qabbrev_tac `P = (λ(n:num,l). l.frml = (SND y).frml)` *)
(*        >> `P y` by (qunabbrev_tac `P` >> Cases_on `y` >> fs[]) *)
(*        >> metis_tac[FIND_LEMM] *)
(*    ) *)
(*    >> Cases_on `q` >> rename[`_ = SOME (nId,frml)`] *)
(*    >> qexists_tac `nId` >> rpt strip_tac *)
(*     >- (qexists_tac `(nId,frml)` >> fs[]) *)
(*     >- (`nId ∈ domain g.followers` by ( *)
(*          `nId ∈ domain g.nodeInfo` suffices_by metis_tac[wfg_def] *)
(*          >> `MEM (nId, frml) (toAList g.nodeInfo)` by metis_tac[FIND_LEMM2] *)
(*          >> fs[MEM_toAList] >> metis_tac[domain_lookup] *)
(*        ) *)
(*        >> fs[domain_lookup] *)
(*        >> Q.HO_MATCH_ABBREV_TAC *)
(*            `?x. FOLDR addSingleEdge a_init ls = SOME x ∧ Q x` *)
(*        >> `!lab x. MEM (lab,x) ls ==> ?h. MEM (x,h) (toAList g.nodeInfo)` by ( *)
(*          rpt strip_tac >> qunabbrev_tac `ls` >> fs[MEM_MAP] *)
(*          >> qabbrev_tac *)
(*              `func = λs. *)
(*                          OPTION_MAP FST *)
(*                          (FIND (λ(n,l). l.frml = s) (toAList g.nodeInfo))` *)
(*          >> `?a. MEM a l1 ∧ SOME x = func a` by metis_tac[CAT_OPTIONS_MAP_LEMM] *)
(*          >> qunabbrev_tac `func` >> fs[] *)
(*          >> `MEM z (toAList g.nodeInfo)` by metis_tac[FIND_LEMM2] *)
(*          >> qexists_tac `SND z` >> fs[] *)
(*        ) *)
(*        >> qabbrev_tac `LABEL = *)
(*             <|edge_grp := (if v = [] then 0 else (HD (MAP FST v)).edge_grp) + 1; *)
(*               pos_lab := l; *)
(*               neg_lab := l0|>` *)
(*        >> qabbrev_tac ` *)
(*             TO_LABELS = λl. *)
(*                 MAP (λi. (LABEL,i)) *)
(*                 (CAT_OPTIONS *)
(*                    (MAP *)
(*                     (λs. *)
(*                      OPTION_MAP FST *)
(*                      (FIND (λ(n,l). l.frml = s) (toAList g.nodeInfo))) l))` *)
(*        >> `ls = TO_LABELS l1` by (qunabbrev_tac `TO_LABELS` >> simp[]) *)
(*        >> `!qs fs. ((!lab x. MEM (lab,x) qs *)
(*                           ==> (?h. MEM (x,h) (toAList g.nodeInfo) *)
(*                                 ∧ (lab = LABEL))) *)
(*                   ∧ (qs = TO_LABELS fs)) *)
(*              ==> ?m. (FOLDR addSingleEdge a_init qs = SOME m) *)
(*                    ∧ (g.nodeInfo = m.nodeInfo) *)
(*                    ∧ (wfg m) *)
(*                    ∧ (?e. ((LABEL.edge_grp,l,l0,e) ∈ extractTrans m frml.frml) *)
(*                          ∧ (!x. MEM (LABEL, x) qs *)
(*                              ==> ?node. (lookup x m.nodeInfo = SOME node) *)
(*                                       ∧ (node.frml ∈ e))) *)
(*                    ∧ (?i. extractTrans m frml.frml *)
(*                             = extractTrans g frml.frml ∪ {(i,l,l0,set fs)})` by ( *)
(*            Induct_on `qs` >> fs[] *)
(*             >- (qunabbrev_tac `a_init` >> simp[extractTrans_def] >> rpt strip_tac *)
(*                 >- (qexists_tac `LABEL` >> qunabbrev_tac `LABEL` >> fs[]) *)
(*                 >- () *)
(*                ) *)
(*             >- (rpt strip_tac *)
(*                 >> `∀lab x. MEM (lab,x) qs *)
(*                       ⇒ (∃h. MEM (x,h) (toAList g.nodeInfo) ∧ (lab = LABEL))` *)
(*                     by metis_tac[] *)
(*                 >> `∃m. (FOLDR addSingleEdge a_init qs = SOME m) *)
(*                       ∧ (g.nodeInfo = m.nodeInfo) *)
(*                       ∧ (wfg m) *)
(*                       ∧ (∃e. *)
(*                           (LABEL.edge_grp,l,l0,e) ∈ extractTrans m frml.frml *)
(*                           ∧ ∀x. *)
(*                            MEM (LABEL,x) qs ⇒ *)
(*                            ∃node. lookup x m.nodeInfo = SOME node *)
(*                                 ∧ node.frml ∈ e)` *)
(*                      by metis_tac[] *)
(*                 >> `?m2. (addSingleEdge h (SOME m) = SOME m2) *)
(*                        ∧ (g.nodeInfo = m2.nodeInfo) *)
(*                        ∧ (wfg m2) *)
(*                        ∧ (∃e. (LABEL.edge_grp,l,l0,e) *)
(*                                 ∈ extractTrans m2 (SND y).frml *)
(*                              ∧ ∀x. *)
(*                                (LABEL,x) = h ∨ MEM (LABEL,x) qs ⇒ *)
(*                                  ∃node. lookup x m2.nodeInfo = SOME node *)
(*                                       ∧ node.frml ∈ e)` *)
(*                      suffices_by fs[] *)
(*                 >> qunabbrev_tac `addSingleEdge` >> Cases_on `h` *)
(*                 >> simp[] *)
(*                 >> `?nG. addEdge nId (q,r) m = SOME nG` by ( *)
(*                      simp[addEdge_def] *)
(*                      >> Q.HO_MATCH_ABBREV_TAC `?nG. P ∧ A nG` *)
(*                      >> `P ∧ (P ==> ?nG. A nG)` suffices_by fs[] *)
(*                      >> qunabbrev_tac `P` >> qunabbrev_tac `A` *)
(*                      >> rpt strip_tac *)
(*                       >- (`MEM (nId,frml) (toAList g.nodeInfo)` *)
(*                              by metis_tac[FIND_LEMM2] *)
(*                           >> fs[MEM_toAList,domain_lookup] *)
(*                           >> metis_tac[] *)
(*                          ) *)
(*                       >- (`∃h. MEM (r,h) (toAList g.nodeInfo)` by metis_tac[] *)
(*                           >> fs[MEM_toAList,domain_lookup] *)
(*                           >> metis_tac[] *)
(*                          ) *)
(*                       >- (`nId ∈ domain m.followers` by metis_tac[wfg_def] *)
(*                           >> `?fol_o. lookup nId m.followers = SOME fol_o` *)
(*                              by metis_tac[domain_lookup] *)
(*                           >> fs[] *)
(*                          ) *)
(*                  ) *)
(*                 >> qexists_tac `nG` >> simp[] *)
(*                 >> `wfg nG` by metis_tac[addEdge_preserves_wfg] *)
(*                 >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac *)
(*                 >> simp[addEdge_def] >> rpt strip_tac *)
(*                 >> Cases_on `m` >> fs[gfg_fn_updates] *)
(*                 >> fs[gfg_component_equality] *)
(*                 >> `?node. lookup r nG.nodeInfo = SOME node` *)
(*                    by metis_tac[domain_lookup] *)
(*                 >> qexists_tac `e ∪ {node.frml}` *)
(*                 >> rpt strip_tac *)
(*                 >- (fs[extractTrans_def] *)
(*                     >> qexists_tac `LABEL` >> simp[SET_EQ_SUBSET,SUBSET_DEF] *)
(*                     >> rpt strip_tac *)
(*                     >- (qunabbrev_tac `LABEL` >> fs[]) *)
(*                     >- (qunabbrev_tac `LABEL` >> fs[]) *)
(*                     >- ( *)
(*                      qexists_tac `suc` >> simp[] >> qexists_tac `sucId` *)
(*                      >> simp[] *)
(*                      >> Q.HO_MATCH_ABBREV_TAC ` *)
(*                          MEM (LABEL,sucId) (OPTION_TO_LIST M_L)` *)
(*                      >> qabbrev_tac `M_L0 = *)
(*                          do node <- *)
(*                               findNode (λ(n',l). l.frml = (SND y).frml) *)
(*                                        (gfg nG.nodeInfo s0 nG.preds nG.next); *)
(*                             lookup node s0 *)
(*                          od` *)
(*                      >> `IS_SOME M_L0` *)
(*                            by metis_tac[MEM,OPTION_TO_LIST_def, *)
(*                                         NOT_IS_SOME_EQ_NONE] *)
(*                      >> `IS_SOME M_L` by ( *)
(*                          qunabbrev_tac `M_L` >> POP_ASSUM mp_tac *)
(*                          >> qunabbrev_tac `M_L0` >> simp[IS_SOME_EXISTS] *)
(*                          >> rpt strip_tac >> Cases_on `node' = nId` *)
(*                          >- (qexists_tac `((q,r)::followers_old)` *)
(*                              >> qexists_tac `nId` >> fs[findNode_def] *)
(*                              >> metis_tac[lookup_insert] *)
(*                             ) *)
(*                          >- (qexists_tac `x'` >> qexists_tac `node'` *)
(*                              >> fs[findNode_def] >> metis_tac[lookup_insert] *)
(*                             ) *)
(*                      ) *)
(*                      >> fs[IS_SOME_EXISTS,OPTION_TO_LIST_def] *)
(*                      >> `MEM (label',sucId) x'` by metis_tac[OPTION_TO_LIST_def] *)
(*                      >> qunabbrev_tac `M_L` >> qunabbrev_tac `M_L0` >> fs[] *)
(*                      >> `node' = node''` by ( *)
(*                           Cases_on `nG` >> fs[findNode_def] *)
(*                           >> rw[] >> metis_tac[SOME_11] *)
(*                      ) *)
(*                      >> `LABEL = label'` by ( *)
(*                          qunabbrev_tac `LABEL` *)
(*                          >> fs[theorem "edgeLabelAA_component_equality"] *)
(*                      ) *)
(*                      >> rw[] >> Cases_on `node' = nId` >> fs[] *)
(*                      >- (rw[] *)
(*                          >> `x'' = (q,r)::followers_old` *)
(*                             by metis_tac[lookup_insert,SOME_11] *)
(*                          >> metis_tac[MEM] *)
(*                         ) *)
(*                      >- (rw[] >> metis_tac[lookup_insert,SOME_11]) *)
(*                      ) *)
(*                     >- (rw[] >> qexists_tac `node` >> simp[] >> qexists_tac `r` *)
(*                         >> simp[] *)
(*                         >> Q.HO_MATCH_ABBREV_TAC ` *)
(*                             MEM (LABEL,r) (OPTION_TO_LIST M_L)` *)
(*                         >> `IS_SOME M_L` by ( *)
(*                             simp[IS_SOME_EXISTS] >> qunabbrev_tac `M_L` *)
(*                             >> qexists_tac `(q,r)::followers_old` >> fs[] *)
(*                             >> qexists_tac `nId` >> fs[findNode_def] *)
(*                             >> rpt strip_tac >>  metis_tac[lookup_insert] *)
(*                          ) *)
(*                         >> fs[IS_SOME_EXISTS] *)
(*                         >> `MEM (LABEL,r) x` suffices_by *)
(*                               metis_tac[OPTION_TO_LIST_def,NOT_IS_SOME_EQ_NONE] *)
(*                         >> qunabbrev_tac `M_L` >> fs[findNode_def] *)
(*                         >> `node' = nId` by fs[] >> rw[] *)
(*                         >> `q = LABEL` by metis_tac[] >> rw[] *)
(*                         >> metis_tac[lookup_insert,SOME_11,MEM] *)
(*                        ) *)
(*                     >- (Cases_on `x = node.frml` >> fs[] *)
(*                         >> `LABEL = label'` by ( *)
(*                              qunabbrev_tac `LABEL` *)
(*                              >> fs[theorem "edgeLabelAA_component_equality"] *)
(*                          ) *)
(*                         >> rw[] >> qexists_tac `suc` >> fs[] *)
(*                         >> qexists_tac `sucId` >> fs[] *)
(*                         >> Q.HO_MATCH_ABBREV_TAC ` *)
(*                               MEM (LABEL,sucId) (OPTION_TO_LIST M_0)` *)
(*                         >> qabbrev_tac ` *)
(*                             M_L =  do *)
(*                                      node <- findNode *)
(*                                               (λ(n,l). l.frml = (SND y).frml) *)
(*                                               nG; *)
(*                                      lookup node nG.followers *)
(*                                     od` *)
(*                         >> `IS_SOME M_L` *)
(*                               by metis_tac[MEM,OPTION_TO_LIST_def, *)
(*                                            NOT_IS_SOME_EQ_NONE] *)
(*                         >> `IS_SOME M_0` by ( *)
(*                              qunabbrev_tac `M_L` >> POP_ASSUM mp_tac *)
(*                              >> qunabbrev_tac `M_0` >> simp[IS_SOME_EXISTS] *)
(*                              >> rpt strip_tac >> Cases_on `node' = nId` *)
(*                              >- (qexists_tac `followers_old` *)
(*                                  >> qexists_tac `nId` >> fs[findNode_def] *)
(*                                 ) *)
(*                              >- (qexists_tac `x` >> qexists_tac `node'` *)
(*                                  >> fs[findNode_def] >> metis_tac[lookup_insert] *)
(*                                 ) *)
(*                          ) *)
(*                         >> fs[IS_SOME_EXISTS,OPTION_TO_LIST_def] *)
(*                         >> `MEM (LABEL,sucId) x` by metis_tac[OPTION_TO_LIST_def] *)
(*                         >> qunabbrev_tac `M_L` >> qunabbrev_tac `M_0` >> fs[] *)
(*                         >> `node' = node''` by ( *)
(*                              Cases_on `nG` >> fs[findNode_def] *)
(*                              >> rw[] >> metis_tac[SOME_11] *)
(*                          ) *)
(*                         >> rw[] *)
(*                         >> Cases_on `node' = nId` >> fs[] *)
(*                         >- (rw[] *)
(*                             >> `x = (q,r)::followers_old` by metis_tac[lookup_insert,SOME_11] *)
(*                             >> `~(sucId = r)` by ( *)
(*                                 `~(node = suc)` suffices_by metis_tac[SOME_11] *)
(*                                 >> fs[theorem "nodeLabelAA_component_equality"] *)
(*                              ) *)
(*                             >> `~((LABEL,sucId) = (q,r))` by fs[] *)
(*                             >> metis_tac[MEM] *)
(*                            ) *)
(*                         >- (rw[] >> metis_tac[lookup_insert,SOME_11]) *)
(*                        ) *)
(*                    ) *)
(*                     >- fs[] *)
(*                     >- (fs[] >> metis_tac[]) *)
(*                    ) *)
(*                ) *)
(*        >> `!qs.  *)



(*        >> `∀lab x. *)
(*              MEM (lab,x) ls ⇒ *)
(*              ∃h. MEM (x,h) (toAList g.nodeInfo) ∧ lab = LABEL` by ( *)
(*                rpt strip_tac >> qunabbrev_tac `ls` >> fs[MEM_MAP] *)
(*        ) >> qunabbrev_tac `Q` *)
(*        >> first_x_assum (qspec_then `ls` mp_tac) >> simp[] *)
(*        >> rpt strip_tac >> qexists_tac `m` >> simp[] *)
(*        >>  *)

(*        >>  *)

(*  qexists_tac *)
(*  >> metis_tac[] *)
(*              ) *)
(*   ); *)

val _ = export_theory ();
