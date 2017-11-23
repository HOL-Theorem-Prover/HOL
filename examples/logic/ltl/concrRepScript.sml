open HolKernel Parse bossLib boolLib gfgTheory listTheory optionTheory pred_setTheory rich_listTheory

open alterATheory sptreeTheory ltlTheory generalHelpersTheory

val _ = new_theory "concrRep";

val _ = monadsyntax.temp_add_monadsyntax();
val _ = overload_on("monad_bind",``OPTION_BIND``);

val _ = Datatype`
  edgeLabelAA = <| edge_grp : num ;
                   pos_lab : (α list) ;
                   neg_lab : (α list)
                 |>`;

val _ = Datatype`
nodeLabelAA = <| frml : α ltl_frml ;
                 is_final : bool ;
                 true_labels : (α edgeLabelAA) list
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
     let sucs =
            OPTION_TO_LIST
               (do (nId,nodeLabel) <- findNode (λ(n,l). l.frml = s) graph ;
                   lookup nId graph.followers
                od
               )
     in let trueLabels =
              OPTION_TO_LIST
              (do (nId, nodeLabel) <- findNode (λ(n,l). l.frml = s) graph ;
                  SOME nodeLabel.true_labels
               od
              )
     in { edge | ?label labelSucs. 0 < label.edge_grp
                 ∧ labelSucs =
                     { suc.frml
                     | ?sucId. MEM (label,sucId) sucs
                        ∧ SOME suc = lookup sucId graph.nodeInfo
                     }
                 ∧ ~(labelSucs = {})
                 ∧ edge = (label.edge_grp, label.pos_lab,
                           label.neg_lab, labelSucs) }
      ∪ { (0,l.pos_lab,l.neg_lab,{}) | MEM l trueLabels }`;


val concr2AbstrAA = Define`
  concr2AbstrAA (concrAA g init prop) =
    ALTER_A
        (concr2Abstr_states g)
        (concr2Abstr_init init g)
        (concr2Abstr_final g)
        (POW (LIST_TO_SET prop))
        (\f. IMAGE (λ(i,p,n,e). (transformLabel (props f) p n,e))
                   (extractTrans g f))`;

val graphStatesWithId_def = Define`
  graphStatesWithId g =
        MAP (λ(id,label). (id, label.frml)) (toAList g.nodeInfo)`;

val GRAPH_STATES_WITH_ID_LEMM = store_thm
  ("GRAPH_STATES_WITH_ID_LEMM",
   ``!g id q. MEM (id,q) (toAList g.nodeInfo)
                ==> MEM (id,q.frml) (graphStatesWithId g)``,
   rpt strip_tac >> fs[graphStatesWithId_def,MEM_MAP]
   >> qexists_tac `(id,q)` >> fs[]
  );

val unique_node_formula_def = Define`
  unique_node_formula g =
   ∀id h.
    MEM (id,h) (graphStatesWithId g) ⇒
     ∀oId. MEM (oId,h) (graphStatesWithId g) ⇒ (id = oId)`;

val UNIQUE_NODE_FORM_LEMM = store_thm
  ("UNIQUE_NODE_FORM_LEMM",
   ``!g f. unique_node_formula g
             ==> (OPTION_MAP (λ(id,label). (id,label.frml))
                      (findNode (λ(n,l). l.frml = f) g)
                   = FIND (λa. SND a = f) (graphStatesWithId g))``,
   rpt strip_tac >> fs[findNode_def,graphStatesWithId_def]
   >> Cases_on
       `FIND (λa. SND a = f)
             (MAP (λ(id,label). (id,label.frml))
                  (toAList g.nodeInfo))`
   >- (fs[]
       >> `!x. MEM x (MAP (λ(id,label). (id,label.frml)) (toAList g.nodeInfo))
               ==> ~((λa. SND a = f) x)` by (
          Q.HO_MATCH_ABBREV_TAC `!x. MEM x L ==> ~P x`
          >> rpt strip_tac
          >> `?z. FIND P L = SOME z` by metis_tac[FIND_LEMM]
          >> fs[]
        )
       >> Q.HO_MATCH_ABBREV_TAC `FIND P L = NONE`
       >> `!x. MEM x L ==> ~P x` by (
          rpt strip_tac
          >> first_x_assum
               (qspec_then `(λ(id,label). (id,label.frml)) x` mp_tac)
          >> fs[MEM_MAP] >> rpt strip_tac
          >- (qunabbrev_tac `P` >> fs[] >> metis_tac[])
          >- (qunabbrev_tac `P` >> Cases_on `x` >> fs[])
        )
       >> `!x. ~(FIND P L = SOME x)` by (
            rpt strip_tac >> metis_tac[FIND_LEMM2]
        )
       >> Cases_on `FIND P L` >> fs[]
      )
   >- (`MEM x (MAP
                (λ(id,label). (id,label.frml))
                (toAList g.nodeInfo))
      ∧ (λa. SND a = f) x`
         by (Q.HO_MATCH_ABBREV_TAC `MEM x L ∧ P x` >> metis_tac[FIND_LEMM2])
       >> `?y.(FIND (λ(n,l). l.frml = f) (toAList g.nodeInfo)) = SOME y
         ∧ (λ(id,label). (id,label.frml)) y = x` suffices_by (
          fs[] >> rpt strip_tac >> fs[]
       )
       >> fs[unique_node_formula_def,graphStatesWithId_def]
       >> `?z. MEM z (toAList g.nodeInfo) ∧ (λ(n,l). l.frml = f) z`
          by (fs[MEM_MAP] >> qexists_tac `y` >> Cases_on `y` >> fs[] >> rw[])
       >> `?a. FIND (λ(n,l). l.frml = f) (toAList g.nodeInfo) = SOME a`
          by metis_tac[FIND_LEMM]
       >> qexists_tac `a` >> fs[] >> Cases_on `a` >> Cases_on `x`
       >> fs[] >> first_x_assum (qspec_then `q'` mp_tac) >> strip_tac
       >> first_x_assum (qspec_then `f` mp_tac) >> simp[] >> strip_tac
       >> first_x_assum (qspec_then `q` mp_tac) >> strip_tac
       >> `MEM (q,r) (toAList g.nodeInfo) ∧ (λ(n,l). l.frml = f) (q,r)`
          by metis_tac[FIND_LEMM2] >> fs[]
       >> `MEM (q,f)
            (MAP (λ(id,label). (id,label.frml)) (toAList g.nodeInfo))` by (
          simp[MEM_MAP] >> qexists_tac `(q,r)` >> fs[]
       )
       >> metis_tac[]
      )
  );

val UNIQUE_NODE_FORM_LEMM2 = store_thm
  ("UNIQUE_NODE_FORM_LEMM",
   ``!g. unique_node_formula g
         ==> (!f x. (SND x = f) ∧ MEM x (graphStatesWithId g)
               ==> !y. (SND y = f) ∧ MEM y (graphStatesWithId g)
                    ==> (x = y))``,
   rpt strip_tac >> fs[graphStatesWithId_def,unique_node_formula_def]
   >> Cases_on `x` >> Cases_on `y`
   >> first_x_assum (qspec_then `q` mp_tac) >> rpt strip_tac
   >> first_x_assum (qspec_then `f` mp_tac)
   >> `MEM (q,f)
         (MAP (λ(id,label). (id,label.frml)) (toAList g.nodeInfo))`
      by (fs[MEM_MAP] >> qexists_tac `y` >> Cases_on `y` >> fs[])
   >> simp[] >> strip_tac
   >> first_x_assum (qspec_then `q'` mp_tac)
   >> `MEM (q',f) (MAP (λ(id,label). (id,label.frml)) (toAList g.nodeInfo))`
      by (fs[MEM_MAP] >> qexists_tac `y'` >> Cases_on `y'` >> fs[])
   >> simp[] >> fs[]
  );

val EXTR_TRANS_LEMM = store_thm
  ("EXTR_TRANS_LEMM",
   ``!g sucId suc id label fls q.
       (lookup id g.nodeInfo = SOME q)
     ∧ (lookup id g.followers = SOME fls)
     ∧ (lookup sucId g.nodeInfo = SOME suc)
     ∧ (MEM (label,sucId) fls)
     ∧ (unique_node_formula g)
     ∧ (0 < label.edge_grp)
     ==> (?s. (label.edge_grp,label.pos_lab,label.neg_lab,s)
                 ∈ extractTrans g q.frml
            ∧ (suc.frml ∈ s))``,
   rpt strip_tac >> simp[extractTrans_def] >> CCONTR_TAC
   >> fs[]
   >> qabbrev_tac `P = λlabel:α edgeLabelAA.
       {suc.frml |
        ∃sucId.
         MEM (label,sucId)
         (OPTION_TO_LIST
              do
              (nId,nodeLabel) <-
              findNode (λ(n,l). l.frml = q.frml) g;
          lookup nId g.followers
                 od) ∧ SOME suc = lookup sucId g.nodeInfo}`
   >> `findNode (λ(n,l). l.frml = q.frml) g = SOME (id,q)` by (
       `?x. findNode (λ(n,l). l.frml = q.frml) g = SOME x` by (
         fs[findNode_def]
         >> `(λ(n,l). l.frml = q.frml) (id,q)` by fs[]
         >> metis_tac[FIND_LEMM,MEM_toAList]
       )
       >> Cases_on `x` >> fs[]
       >> `(λ(n,l). l.frml = q.frml) (id,q)
         ∧ (MEM (id,q) (toAList g.nodeInfo))` by fs[MEM_toAList]
       >> `(λ(n,l). l.frml = q.frml) (q',r)
         ∧ (MEM (q',r) (toAList g.nodeInfo))`
           by metis_tac[FIND_LEMM2,findNode_def]
       >> `q' = id` by (
           fs[unique_node_formula_def]
           >> metis_tac[GRAPH_STATES_WITH_ID_LEMM]
       )
       >> rw[] >> metis_tac[MEM_toAList,SOME_11]
   )
   >> `~(P label = {})` by (
       `?n. n ∈ P label` suffices_by metis_tac[MEMBER_NOT_EMPTY]
       >> qunabbrev_tac `P` >> fs[] >> qexists_tac `suc` >> qexists_tac `sucId`
       >> simp[OPTION_TO_LIST_MEM] >> qexists_tac `fls` >> fs[]
       >> qexists_tac `(id,q)` >> fs[]
   )
   >> first_x_assum (qspec_then `P label` mp_tac) >> simp[]
   >> rpt strip_tac >> fs[]
   >- (qexists_tac `label` >> fs[])
   >- (qunabbrev_tac `P` >> fs[] >> qexists_tac `suc` >> fs[]
       >> qexists_tac `sucId` >> fs[OPTION_TO_LIST_MEM]
       >> qexists_tac `fls` >> fs[]
      )
  );


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
    if sucs = []
    then do (nodeId,nodeLabel) <- findNode (λ(n,l). l.frml = f) g;
            newlabel <- SOME (nodeLabelAA
                                nodeLabel.frml
                                nodeLabel.is_final
                                ((edgeLabelAA 0 pos neg)
                                  :: nodeLabel.true_labels)) ;
            updateNode nodeId newlabel g
         od
    else
    let sucIds = MAP FST
                  (CAT_OPTIONS (MAP (\s. findNode (λ(n,l). l.frml = s) g) sucs))
    in do (nodeId,nodeLabel) <- findNode (λ(n,l). l.frml = f) g;
           oldSucPairs <- lookup nodeId g.followers ;
           oldSucs <- SOME (MAP FST oldSucPairs);
           lstGrpId <- SOME (if oldSucs = [] then 1 else (HD oldSucs).edge_grp) ;
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

val first_flw_has_max_counter_def = Define`
  first_flw_has_max_counter g =
     (!x_id fls fl. x_id ∈ domain g.nodeInfo
               ∧ (lookup x_id g.followers = SOME (fl::fls))
               ==> (!y. MEM y fls
                        ==> ((FST y).edge_grp <= (FST fl).edge_grp)))`;

val FIRST_FLW_LEMM = store_thm
  ("FIRST_FLW_LEMM",
   ``!g g2. (g.followers = g2.followers)
          ∧ (domain g.nodeInfo = domain g2.nodeInfo)
            ==> (first_flw_has_max_counter g
                 = first_flw_has_max_counter g2)``,
   simp[first_flw_has_max_counter_def,EQ_IMP_THM] >> rpt strip_tac
   >> metis_tac[]
  );

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

val ADD_0EDGE_LEMM = store_thm
  ("ADD_0EDGE_LEMM",
   ``!g g2 nId lab edge.
        let NEW_LAB =
              nodeLabelAA lab.frml lab.is_final (edge::lab.true_labels)
        in
        (lookup nId g.nodeInfo = SOME lab)
        ∧ unique_node_formula g
        ∧ (updateNode nId NEW_LAB g = SOME g2)
        ==> unique_node_formula g2``,
   fs[unique_node_formula_def,updateNode_def,graphStatesWithId_def]
   >> rpt strip_tac >> fs[MEM_MAP]
   >> first_x_assum (qspec_then `id` mp_tac) >> rpt strip_tac
   >> qabbrev_tac `nodeInfo2 =
                    insert nId
                     (nodeLabelAA lab.frml lab.is_final
                      (edge::lab.true_labels)) g.nodeInfo`
   >> Cases_on `y` >> Cases_on `y'` >> fs[] >> rw[]
   >> first_x_assum (qspec_then `r.frml` mp_tac) >> simp[] >> rpt strip_tac
   >> `(lookup id nodeInfo2 = SOME r) ∧ (lookup oId nodeInfo2 = SOME r')`
      by metis_tac[MEM_toAList]
   >> `?z1. (lookup id g.nodeInfo = SOME z1) ∧ (z1.frml = r.frml)` by (
       qunabbrev_tac `nodeInfo2` >> Cases_on `id = nId`
       >> fs[lookup_insert] >> Cases_on `r` >> fs[]
   )
   >> `?z2. (lookup oId g.nodeInfo = SOME z2) ∧ (z2.frml = r.frml)` by (
       qunabbrev_tac `nodeInfo2` >> Cases_on `oId = nId`
       >> fs[lookup_insert] >> Cases_on `r'` >> fs[]
   )
   >> `∃y.
         (id,r.frml) = (λ(id,label). (id,label.frml)) y
        ∧ MEM y (toAList g.nodeInfo)` by (
       qexists_tac `(id,z1)` >> fs[MEM_toAList]
   )
   >> `∀oId'.
        (∃y.
          (oId',r.frml) = (λ(id,label). (id,label.frml)) y
        ∧ MEM y (toAList g.nodeInfo)) ⇒ (id = oId')` by metis_tac[]
   >> first_x_assum (qspec_then `oId` mp_tac) >> simp[]
   >> `∃y.
        (oId,r.frml) = (λ(id,label). (id,label.frml)) y
        ∧ MEM y (toAList g.nodeInfo)` by (
       qexists_tac `(oId,z2)` >> fs[MEM_toAList]
   ) >> metis_tac[]
  );

val ADDEDGE_COUNTER_LEMM = store_thm
  ("ADDEDGE_COUNTER_LEMM",
   ``!g e f g2.
       (addEdgeToGraph f e g = SOME g2) ∧ first_flw_has_max_counter g ∧ wfg g
          ==> first_flw_has_max_counter g2``,
   rpt strip_tac >> Cases_on `e`
   >> fs[addEdgeToGraph_def,first_flw_has_max_counter_def]
   >> Cases_on `l1 = []` >> rpt strip_tac >> fs[]
   >- (Cases_on `x` >> fs[]
       >> metis_tac[updateNode_preserves_domain, updateNode_preserves_edges]
      )
   >- (Cases_on `x` >> fs[]
       >> qabbrev_tac `LABEL =
           <|edge_grp :=
              (if oldSucPairs = [] then 1n
               else (HD (MAP FST oldSucPairs)).edge_grp) + 1;
             pos_lab := l; neg_lab := l0|>`
       >> qabbrev_tac `addSingleEdge =
                       (λe:(α edgeLabelAA # num)
                         g_opt:((α nodeLabelAA, α edgeLabelAA) gfg) option.
                          do g_int <- g_opt;
                             newGraph <- addEdge q e g_int;
                             SOME newGraph
                          od)`
       >> qabbrev_tac `TO_LABELS = λl.
                       (MAP (λi. (LABEL,i))
                        (MAP FST
                         (CAT_OPTIONS
                          (MAP (λs. findNode (λ(n,l). l.frml = s) g) l))))`
       >> `!ls. ?m. (FOLDR addSingleEdge (SOME g) (TO_LABELS ls) = SOME m)
                  ∧ (first_flw_has_max_counter m)
                  ∧ (!fl fls. lookup q m.followers = SOME (fl::fls)
                               ==> (FST fl).edge_grp <= LABEL.edge_grp
                    )
                  ∧ (!id. ~(id = q)
                          ==> (lookup id m.followers = lookup id g.followers))
                  ∧ (g.nodeInfo = m.nodeInfo)
                  ∧ wfg m` by (
            Induct_on `ls`
            >- (fs[first_flw_has_max_counter_def] >> rpt strip_tac
                >> `TO_LABELS [] = []` by (
                 qunabbrev_tac `TO_LABELS` >> fs[CAT_OPTIONS_def]
                )
                >> fs[] >> strip_tac
                >- metis_tac[]
                >- (Cases_on `oldSucPairs` >> fs[] >> qunabbrev_tac `LABEL`
                    >> fs[]
                   )
               )
            >- (gen_tac
                >> Cases_on `findNode (λ(n,l). l.frml = h) g`
                >- (fs[]
                    >> `TO_LABELS (h::ls) = TO_LABELS ls` by (
                      qunabbrev_tac `TO_LABELS` >> fs[CAT_OPTIONS_def]
                    )
                    >> metis_tac[]
                   )
                >- (Cases_on `x`
                    >> `TO_LABELS (h::ls) = (LABEL,q')::(TO_LABELS ls)` by (
                         qunabbrev_tac `TO_LABELS` >> fs[CAT_OPTIONS_def]
                     )
                    >> rw[]
                    >> `?k. addSingleEdge (LABEL,q') (SOME m) = SOME k
                          ∧ (k.nodeInfo = m.nodeInfo)
                          ∧ wfg k` by (
                        qunabbrev_tac `addSingleEdge` >> fs[]
                        >> `∃k. addEdge q (LABEL,q') m = SOME k`
                            suffices_by metis_tac[addEdge_preserves_nodeInfo,
                                                  addEdge_preserves_wfg]
                        >> simp[addEdge_def]
                        >> `q ∈ domain g.nodeInfo ∧ q' ∈ domain g.nodeInfo` by (
                            fs[findNode_def]
                            >> `MEM (q,r) (toAList g.nodeInfo)
                              ∧ MEM (q',r') (toAList g.nodeInfo)`
                                by metis_tac[FIND_LEMM2]
                            >> metis_tac[MEM_toAList,domain_lookup]
                        )
                        >> Q.HO_MATCH_ABBREV_TAC `?k. A ∧ ?j. B j k`
                        >> `A ∧ ?j k. B j k` suffices_by metis_tac[]
                        >> qunabbrev_tac `A` >> qunabbrev_tac `B` >> fs[]
                        >> `∃j. lookup q m.followers = SOME j` by (
                            fs[wfg_def] >> metis_tac[domain_lookup]
                        )
                        >> metis_tac[]
                     )
                    >> qexists_tac `k` >> fs[]
                    >> qunabbrev_tac `addSingleEdge` >> fs[addEdge_def]
                    >> fs[gfg_component_equality,
                          first_flw_has_max_counter_def]
                    >> rpt strip_tac >> rw[]
                    >> Cases_on `x_id' = q` >> rw[]
                    >- (`(fl'::fls') = (LABEL,q')::followers_old`
                          by metis_tac[lookup_insert,SOME_11]
                        >> rw[] >> Cases_on `fls'` >> fs[]
                        >> `(FST y').edge_grp ≤ (FST h').edge_grp`
                           by metis_tac[]
                        >> fs[]
                       )
                    >- (`lookup x_id' m.followers = SOME (fl'::fls')`
                              by metis_tac[lookup_insert]
                        >> `x_id' ∈ domain m.nodeInfo`
                              by metis_tac[domain_lookup,wfg_def]
                        >> metis_tac[]
                       )
                    >- (`(fl'::fls') = (LABEL,q')::followers_old`
                         by metis_tac[lookup_insert,SOME_11]
                        >> rw[] >> fs[]
                       )
                    >- (`(fl'::fls') = (LABEL,q')::followers_old`
                         by metis_tac[lookup_insert,SOME_11]
                        >> rw[] >> fs[]
                       )
                    >- metis_tac[lookup_insert]
                    >- metis_tac[lookup_insert]
                   )
               )
        )
       >> first_x_assum (qspec_then `l1` mp_tac)
       >> qunabbrev_tac `TO_LABELS` >> simp[] >> rpt strip_tac
       >> fs[first_flw_has_max_counter_def] >> metis_tac[]
      )
  );

val ADDEDGE_LEMM = store_thm
  ("ADDEDGE_LEMM",
   ``!g f e aP. wfg g ∧ MEM f (graphStates g)
            ∧ unique_node_formula g
            ∧ (!x. MEM x e.sucs ==> MEM x (graphStates g))
            ∧ (first_flw_has_max_counter g)
        ==> (?g2. (addEdgeToGraph f e g = SOME g2) ∧ wfg g2
          ∧ (set (graphStatesWithId g) = set (graphStatesWithId g2))
          ∧ (unique_node_formula g2)
          ∧ (!h.
                 if h = f
                 then ?i. extractTrans g2 h
                        = extractTrans g h ∪ { (i, e.pos,e.neg,set e.sucs) }
                 else extractTrans g2 h = extractTrans g h)
          ∧ (first_flw_has_max_counter g2))``,
   rpt strip_tac >> Cases_on `e` >> fs[addEdgeToGraph_def]
   >> fs[graphStates_def,MEM_MAP] (* >> simp[findNode_def] *)
   >> `l1 = [] \/ ?h t. l1 = SNOC h t` by metis_tac[SNOC_CASES]
   (* >> Cases_on `l1` >> fs[] >> rpt strip_tac *)
   >> `?q. (findNode (λ(n,l). l.frml = (SND y).frml) g = SOME q)
        ∧ ((λ(n,l). l.frml = (SND y).frml) q)` by (
       simp[findNode_def]
       >> qabbrev_tac `P = (λ(n:num,l). l.frml = (SND y).frml)`
       >> `P y` by (qunabbrev_tac `P` >> Cases_on `y` >> fs[])
       >> metis_tac[FIND_LEMM]
   )
   >- (
     Cases_on `q` >> fs[]
     (* >> Q.HO_MATCH_ABBREV_TAC *)
     (*   `?g2. (?nodeId. A nodeId ∧ P g2 nodeId) ∧ Q g2` *)
     (* >> `?nodeId. A nodeId ∧ ?g2. P g2 nodeId ∧ Q g2` suffices_by metis_tac[] *)
     (* >> qunabbrev_tac `A` >> qunabbrev_tac `P` >> fs[] *)
     >> (* Cases_on `q` >> fs[] >>  *)rename[`_ = SOME (nId,frml)`]
     >> Q.HO_MATCH_ABBREV_TAC
         `?g2. updateNode nId NEW_LAB g = SOME g2 ∧ Q g2`
     >> `∃x. updateNode nId NEW_LAB g = SOME x` by (
         simp[updateNode_def] >> fs[findNode_def]
         >> `MEM (nId, frml) (toAList g.nodeInfo)` by metis_tac[FIND_LEMM2]
         >> fs[MEM_toAList] >> metis_tac[domain_lookup]
     )
     >> `g.followers = x.followers`
        by fs[updateNode_def,gfg_component_equality]
     >> qexists_tac `x` >> qunabbrev_tac `Q` >> simp[]
     >> Q.HO_MATCH_ABBREV_TAC `A ∧ B ∧ C`
     >> `A ∧ B ∧ (A ∧ B ==> C)` suffices_by metis_tac[]
     >> qunabbrev_tac `A` >> qunabbrev_tac `B` >> qunabbrev_tac `C`
     >> `lookup nId g.nodeInfo = SOME frml` by (
         fs[unique_node_formula_def,graphStatesWithId_def,findNode_def]
         >> `MEM (nId,frml) (toAList g.nodeInfo)
           ∧ (λ(n,l). l.frml = (SND y).frml) (nId,frml)`
            by metis_tac[FIND_LEMM2]
         >> metis_tac[MEM_toAList]
     )
     >> `unique_node_formula x` by metis_tac[ADD_0EDGE_LEMM]
     (* >> `!n. OPTION_MAP (λ(id,lab). (id,lab.frml)) *)
     (*           (findNode (λ(n,l). l.frml = (SND y).frml) g) *)
     (*          = OPTION_MAP (λ(id,lab). (id,lab.frml)) *)
     (*            (findNode (λ(n,l). l.frml = (SND y).frml) x)` by ( *)
     (*     rpt strip_tac *)
     (*     >> `(OPTION_MAP (λ(id,lab). (id,lab.frml)) *)
     (*          (findNode (λ(n,l). l.frml = (SND y).frml) x)) *)
     (*         = (SOME (nId,f))` suffices_by fs[] *)
     (*     >> `findNode (λ(n,l). l.frml = (SND y).frml) x = SOME (nId,NEW_LAB)` *)
     (*        suffices_by (qunabbrev_tac `NEW_LAB` >> fs[]) *)
     (*     >> fs[findNode_def,updateNode_def] >> rw[] *)
     (*     >> qabbrev_tac `nodeList2 = insert nId NEW_LAB g.nodeInfo` *)
     (*     >> `?id l. MEM (id,l) (toAList nodeList2) *)
     (*              ∧ (λ(n,l). l.frml = (SND y).frml) (id,l)` by ( *)
     (*         fs[MEM_toAList] >> qunabbrev_tac `nodeList2` *)
     (*         >> fs[lookup_insert] >> qexists_tac `nId` >> fs[] *)
     (*         >> qunabbrev_tac `NEW_LAB` >> fs[] *)
     (*     ) *)
     (*     >> `?k. FIND (λ(n,l). l.frml = (SND y).frml) *)
     (*              (toAList nodeList2) = SOME k` by metis_tac[FIND_LEMM] *)
     (*     >> fs[unique_node_formula_def,graphStatesWithId_def] *)
     (*     >> Cases_on `k` *)
     (*     >> first_x_assum (qspec_then `q` mp_tac) >> rpt strip_tac *)
     (*     >> first_x_assum (qspec_then `r.frml` mp_tac) >> rpt strip_tac *)
     (*     >> `MEM (q,r.frml) *)
     (*          (MAP (λ(id,label). (id,label.frml)) (toAList nodeList2))` by ( *)
     (*         simp[MEM_MAP] >> qexists_tac `(q,r)` >> fs[] *)
     (*         >> metis_tac[FIND_LEMM2] *)
     (*     ) *)
     (*     >> `∀oId. *)
     (*          MEM (oId,r.frml) *)
     (*          (MAP (λ(id,label). (id,label.frml)) (toAList nodeList2)) ⇒ *)
     (*          q = oId` by metis_tac[] *)
     (*     >> first_x_assum (qspec_then `nId` mp_tac) >> rpt strip_tac *)
     (*     >> `MEM (nId,r) *)
     (* ) *)
     >> rpt strip_tac
      >- metis_tac[updateNode_preserves_wfg]
      >- (simp[graphStatesWithId_def,SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
          >> fs[MEM_MAP,updateNode_def] >> Cases_on `x'` >> Cases_on `y'`
          >> Cases_on `q = nId` >> fs[findNode_def] >> rw[]
           >- (qexists_tac `(nId, NEW_LAB)` >> qunabbrev_tac `NEW_LAB` >> fs[]
               >> qabbrev_tac `P = (λ(n:num,l). l.frml = (SND y).frml)`
               >> `P (nId,frml) ∧ MEM (nId,frml) (toAList g.nodeInfo)`
                   by metis_tac[FIND_LEMM2]
               >> qunabbrev_tac `P` >> fs[]
               >> `lookup nId g.nodeInfo = SOME r'` by metis_tac[MEM_toAList]
               >> `lookup nId g.nodeInfo = SOME frml` by metis_tac[MEM_toAList]
               >> `r' = frml` by metis_tac[SOME_11] >> rw[]
               >> rw[MEM_toAList] >> fs[gfg_component_equality] >> rw[]
               >> metis_tac[lookup_insert]
              )
           >- (qexists_tac `(q,r')` >> fs[MEM_toAList,gfg_component_equality]
               >> rw[]  >> metis_tac[lookup_insert])
           >- (qexists_tac `(nId,frml)` >> (* qunabbrev_tac `NEW_LAB` >> *) fs[]
               >> qabbrev_tac `P = (λ(n:num,l). l.frml = (SND y).frml)`
               >> `P (nId,frml) ∧ MEM (nId,frml) (toAList g.nodeInfo)`
                  by metis_tac[FIND_LEMM2]
               >> qunabbrev_tac `P` >> fs[]
               >> `lookup nId g.nodeInfo = SOME frml` by metis_tac[MEM_toAList]
               >> fs[gfg_component_equality]
               >> `lookup nId (insert nId NEW_LAB g.nodeInfo) = SOME r'`
                     by metis_tac[MEM_toAList]
               >> fs[lookup_insert] >> qunabbrev_tac `r'` >> fs[]
              )
           >- (qexists_tac `(q,r')` >> fs[MEM_toAList,gfg_component_equality]
              >> metis_tac[lookup_insert])
         )
      >- fs[]
      >- (`?z. findNode (λ(n,l). l.frml = (SND y).frml) x
                         = SOME (nId,NEW_LAB)` by (
            `MEM (nId,frml) (toAList g.nodeInfo)` by metis_tac[MEM_toAList]
            >> fs[graphStatesWithId_def]
            >> `MEM ((λ(id,label). (id,label.frml)) (nId,frml))
                  (MAP (λ(id,label). (id,label.frml)) (toAList x.nodeInfo))`
                      by metis_tac[MEM_MAP]
            >> fs[MEM_MAP] >> Cases_on `y'`
            >> `(λ(n,l). l.frml = (SND y).frml) (q,r)` by fs[]
            >> `?z. (FIND (λ(n,l). l.frml = (SND y).frml)
                   (toAList x.nodeInfo) = SOME z)
                ∧ (λ(n,l). l.frml = (SND y).frml) z` by metis_tac[FIND_LEMM]
            >> Cases_on `z` >> fs[] >> simp[findNode_def]
            >> `MEM (q,r.frml) (graphStatesWithId x)` by (
                simp[graphStatesWithId_def,MEM_MAP]
                >> qexists_tac `(q,r)` >> fs[]
            )
            >> `MEM (q',r'.frml) (graphStatesWithId x)` by (
               simp[graphStatesWithId_def,MEM_MAP]
               >> qexists_tac `(q',r')` >> fs[]
               >> metis_tac[FIND_LEMM2]
            )
            >> fs[unique_node_formula_def]
            >> `q' = q` by metis_tac[]
            >> `MEM (q,r') (toAList x.nodeInfo)` by metis_tac[FIND_LEMM2]
            >> fs[MEM_toAList,updateNode_def,gfg_component_equality]
            >> `lookup q (insert q NEW_LAB g.nodeInfo) = SOME r` by metis_tac[]
            >> metis_tac[lookup_insert,SOME_11]
          )
          >> Cases_on `h = f` >> fs[]
          >- (
            qexists_tac `0` >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
            >> fs[extractTrans_def]
            >- (
             qexists_tac `label` >> fs[] >> rpt strip_tac
             >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
             >- (rw[] >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
                 >> simp[MEMBER_NOT_EMPTY] >> rpt strip_tac
                 >> `?a. a ∈ {suc.frml | ∃sucId.
                                MEM (label,sucId)
                                 (OPTION_TO_LIST (lookup nId x.followers))
                                 ∧ SOME suc = lookup sucId x.nodeInfo}`
                     by metis_tac[MEMBER_NOT_EMPTY]
                 >> fs[OPTION_TO_LIST_MEM]
                 >> `MEM (sucId,suc.frml) (graphStatesWithId g)` by (
                      simp[graphStatesWithId_def,MEM_MAP]
                      >> qexists_tac `(sucId,suc)` >> fs[]
                      >> metis_tac[MEM_toAList]
                  )
                 >> `?a. a ∈ {suc.frml |
                     ∃sucId.
                      (∃l. lookup nId x.followers = SOME l
                      ∧ MEM (label,sucId) l)
                      ∧ SOME suc = lookup sucId g.nodeInfo}` by (
                      qexists_tac `suc.frml` >> fs[]
                      >> fs[graphStatesWithId_def,MEM_MAP]
                      >> Cases_on `y'` >> qexists_tac `r` >> fs[]
                      >> qexists_tac `q` >> metis_tac[MEM_toAList]
                  ) >> metis_tac[MEMBER_NOT_EMPTY]
                )
             >- (
              fs[OPTION_TO_LIST_MEM]
              >> rename[`findNode _ x = SOME x1`]
              >> `SOME ((λ(id,label). (id,label.frml)) x1)
                   = FIND (λa. SND a = (SND y).frml) (graphStatesWithId x)`
                 by metis_tac[OPTION_MAP_DEF,UNIQUE_NODE_FORM_LEMM]
              >> Cases_on `x1` >> fs[]
              >> `MEM (q,r.frml) (graphStatesWithId x)
                  ∧ ((λa. SND a = (SND y).frml) (q,r.frml))`
                 by (Q.HO_MATCH_ABBREV_TAC `MEM A L ∧ P A`
                     >> metis_tac[FIND_LEMM2])
              >> `MEM (q,r.frml) (graphStatesWithId g)` by metis_tac[MEM]
              >> `MEM (nId,frml.frml) (graphStatesWithId g)` by (
                  PURE_REWRITE_TAC[graphStatesWithId_def,MEM_MAP]
                  >> qexists_tac `(nId,frml)` >> fs[]
                  >> metis_tac[MEM_toAList]
              )
              >> `q = nId` by (
                  `SND (q,r.frml) = f` by fs[]
                  >> `SND (nId,r.frml) = f` by fs[]
                  >> IMP_RES_TAC UNIQUE_NODE_FORM_LEMM2 >> fs[]
              )
              >> rw[]
              >> Cases_on `sucId = nId` >> fs[] >> rw[]
              >- (qexists_tac `frml` >> fs[]
                  >> `MEM (nId,suc) (toAList x.nodeInfo)`
                      by metis_tac[MEM_toAList]
                  >> `MEM (nId,suc.frml) (graphStatesWithId x)` by (
                        simp[graphStatesWithId_def,MEM_MAP]
                        >> qexists_tac `(nId,suc)` >> fs[]
                    )
                  >> `MEM (nId,suc.frml) (graphStatesWithId g)` by fs[]
                  >> `suc.frml = frml.frml` by (
                        fs[graphStatesWithId_def,MEM_MAP]
                        >> rename[`(nId,suc.frml) = _ y1`]
                        >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
                        >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
                        >> rename[`(nId,suc.frml) = _ y2`] >> rpt strip_tac
                        >> Cases_on `y1` >> Cases_on `y2` >> fs[] >> rw[]
                        >> metis_tac[MEM_toAList,SOME_11]
                    )
                  >> rw[] >> qexists_tac `nId` >> fs[]
                  >> metis_tac[]
                 )
              >- (
               qexists_tac `suc` >> fs[] >> qexists_tac `sucId`
               >> `∃l. lookup nId g.followers = SOME l ∧ MEM (label,sucId) l`
                  by metis_tac[]
               >> rpt strip_tac >> fs[updateNode_def] >> Cases_on `g`
               >> fs[gfg_component_equality] >> metis_tac[lookup_insert]
              )
             )
             >- (
              fs[OPTION_TO_LIST_MEM] >> Cases_on `sucId = nId` >> fs[]
              >> rw[]
              >- (
                `suc = frml` by metis_tac[SOME_11]
                 >> qexists_tac `NEW_LAB` >> fs[] >> rpt strip_tac
                 >- (qunabbrev_tac `NEW_LAB` >> fs[])
                 >- (qexists_tac `nId`
                     >> fs[updateNode_def,gfg_component_equality]
                     >> metis_tac[lookup_insert]
                    )
              )
              >- (qexists_tac `suc` >> fs[] >> qexists_tac `sucId` >> fs[]
                  >> fs[updateNode_def,gfg_component_equality]
                  >> metis_tac[lookup_insert]
                 )
             )
            )
            >- (`MEM l' (edgeLabelAA 0 l l0::frml.true_labels)` by (
                 fs[OPTION_TO_LIST_MEM] >> fs[] >> rw[] >> fs[]
                 >> qunabbrev_tac `NEW_LAB` >> fs[] >> rw[]
                 >> fs[]
                )
                >> fs[] >> disj1_tac >> fs[] >> disj2_tac
                >> qexists_tac `l'` >> simp[OPTION_TO_LIST_MEM]
               )
            >- (qexists_tac `label` >> fs[] >> rpt strip_tac
                >> simp[SET_EQ_SUBSET,SUBSET_DEF]
                >> rpt strip_tac >> Cases_on `sucId = nId` >> rw[]
                >- (POP_ASSUM mp_tac >> POP_ASSUM mp_tac
                    >> simp[MEMBER_NOT_EMPTY]
                    >> Q.HO_MATCH_ABBREV_TAC `~(A = {}) ==> ~(B = {})`
                    >> rpt strip_tac
                    >> `?a. a ∈ A` by metis_tac[MEMBER_NOT_EMPTY]
                    >> `?b. b ∈ B` suffices_by metis_tac[MEMBER_NOT_EMPTY]
                    >> qunabbrev_tac `A` >> qunabbrev_tac `B`
                    >> fs[OPTION_TO_LIST_MEM]
                    >> `MEM (sucId,suc.frml) (graphStatesWithId g)` by (
                         PURE_REWRITE_TAC[graphStatesWithId_def,MEM_MAP]
                         >> qexists_tac `(sucId,suc)` >> fs[]
                         >> metis_tac[MEM_toAList]
                     )
                    >> `MEM (sucId,suc.frml) (graphStatesWithId x)`
                       by metis_tac[]
                    >> fs[graphStatesWithId_def,MEM_MAP] >> Cases_on `y''`
                    >> fs[] >> metis_tac[MEM_toAList,SOME_11]
                   )
                >- (POP_ASSUM mp_tac >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
                    >> simp[MEMBER_NOT_EMPTY]
                    >> Q.HO_MATCH_ABBREV_TAC `~(A = {}) ==> (B = {}) ==> C`
                    >> rpt strip_tac
                    >> `?a. a ∈ A` by metis_tac[MEMBER_NOT_EMPTY]
                    >> `?b. b ∈ B` suffices_by metis_tac[MEMBER_NOT_EMPTY]
                    >> qunabbrev_tac `A` >> qunabbrev_tac `B`
                    >> fs[OPTION_TO_LIST_MEM]
                    >> `MEM (sucId',suc.frml) (graphStatesWithId g)` by (
                         PURE_REWRITE_TAC[graphStatesWithId_def,MEM_MAP]
                         >> qexists_tac `(sucId',suc)` >> fs[]
                         >> metis_tac[MEM_toAList]
                     )
                    >> `MEM (sucId',suc.frml) (graphStatesWithId x)`
                       by metis_tac[]
                    >> fs[graphStatesWithId_def,MEM_MAP] >> Cases_on `y''`
                    >> fs[] >> metis_tac[MEM_toAList,SOME_11]
                   )
                >- (qexists_tac `NEW_LAB` >> fs[findNode_def]
                    >> `MEM (nId,NEW_LAB) (toAList x.nodeInfo)`
                       by metis_tac[FIND_LEMM2]
                    >> `MEM (nId,frml) (toAList g.nodeInfo)`
                       by metis_tac[FIND_LEMM2]
                    >> `suc = frml` by metis_tac[SOME_11,MEM_toAList]
                    >> `suc.frml = NEW_LAB.frml` by (
                         qunabbrev_tac `NEW_LAB` >> fs[]
                     )
                    >> fs[] >> qexists_tac `nId` >> fs[updateNode_def]
                    >> fs[gfg_component_equality] >> metis_tac[lookup_insert]
                   )
                >- (qexists_tac `suc` >> fs[] >> qexists_tac `sucId` >> fs[]
                    >> fs[updateNode_def,gfg_component_equality]
                    >> metis_tac[lookup_insert]
                   )
                >- (qexists_tac `frml` >> fs[findNode_def]
                    >> `MEM (nId,NEW_LAB) (toAList x.nodeInfo)`
                       by metis_tac[FIND_LEMM2]
                    >> `NEW_LAB = suc` by metis_tac[MEM_toAList,SOME_11] >> rw[]
                    >- (qunabbrev_tac `NEW_LAB` >> fs[])
                    >- (qexists_tac `nId` >> fs[OPTION_TO_LIST_MEM])
                   )
                >- (qexists_tac `suc` >> fs[] >> qexists_tac `sucId` >> fs[]
                    >> fs[updateNode_def,gfg_component_equality]
                    >> metis_tac[lookup_insert])
               )
            >- (`MEM l' frml.true_labels` by (
                 fs[OPTION_TO_LIST_MEM] >> fs[] >> rw[] >> fs[]
                )
                >> disj2_tac >> qunabbrev_tac `NEW_LAB` >> qexists_tac `l'`
                >> fs[OPTION_TO_LIST_MEM]
               )
            >- (disj2_tac >> qexists_tac `edgeLabelAA 0 l l0` >> fs[]
                >> qunabbrev_tac `NEW_LAB` >> fs[OPTION_TO_LIST_MEM]
               )
          )
          >- (
           Cases_on `h = (SND y).frml` >> fs[extractTrans_def]
           >> `findNode  (λ(n,l). l.frml = h) x
                 = findNode (λ(n,l). l.frml = h) g` by (
               simp[findNode_def]
               >> Cases_on `?a b. MEM (a,b) (toAList g.nodeInfo)
                                ∧ b.frml = h` >> fs[]
               >- (
                `MEM (a,h) (graphStatesWithId g)` by (
                  PURE_REWRITE_TAC[graphStatesWithId_def,MEM_MAP]
                  >> qexists_tac `(a,b)` >> fs[]
                )
                >> `MEM (a,h) (graphStatesWithId x)` by metis_tac[]
                >> `?z. FIND (λ(n,l). l.frml = h) (toAList x.nodeInfo) = SOME z`
                   by (
                    fs[graphStatesWithId_def,MEM_MAP] >> Cases_on `y''` >> fs[]
                      >> `(λ(n,l). l.frml = r.frml) (q,r)` by fs[]
                      >> metis_tac[FIND_LEMM]
                )
                >> `?z2. FIND (λ(n,l). l.frml = h) (toAList g.nodeInfo)
                        = SOME z2` by (
                    fs[graphStatesWithId_def,MEM_MAP] >> Cases_on `y'` >> fs[]
                      >> Cases_on `y''` >> fs[]
                      >> `(λ(n,l). l.frml = r.frml) (q,r)` by fs[]
                      >> metis_tac[FIND_LEMM]
                )
                >> Cases_on `z` >> Cases_on `z2`
                >> `lookup q x.nodeInfo = SOME r ∧ (λ(n,l). l.frml = h) (q,r)
                  ∧ lookup q' g.nodeInfo = SOME r'
                  ∧ (λ(n,l). l.frml = h) (q',r')`
                   by metis_tac[FIND_LEMM2,MEM_toAList]
                >> fs[updateNode_def,gfg_component_equality]
                >> `q = a ∧ q' = a` by (
                    fs[unique_node_formula_def]
                    >> `MEM (q,h) (graphStatesWithId x)` by (
                        fs[graphStatesWithId_def,MEM_MAP]
                        >> qexists_tac `(q,r)` >> fs[MEM_toAList]
                    )
                    >> `MEM (q',h) (graphStatesWithId g)` by (
                        PURE_REWRITE_TAC[graphStatesWithId_def,MEM_MAP]
                        >> qexists_tac `(q',r')` >> fs[MEM_toAList]
                    )
                    >> metis_tac[]
                )
                >> rw[]
                >> `~(a = nId)` by (
                  CCONTR_TAC >> fs[findNode_def] >> rw[]
                  >> fs[]
                )
                >> metis_tac[lookup_insert,SOME_11]
               )
               >- (
                fs[]
                >> `∀a b. ¬MEM (a,b) (toAList g.nodeInfo)
                        ∨ ~((λ(n,l). l.frml = h) (a,b))` by fs[]
                >> `!a. ~(FIND (λ(n,l). l.frml = h) (toAList g.nodeInfo)
                          = SOME a)` by (
                    rpt strip_tac >> Cases_on `a`
                    >> first_x_assum (qspec_then `q` mp_tac) >> rpt strip_tac
                    >> first_x_assum (qspec_then `r` mp_tac) >> rpt strip_tac
                    >> metis_tac[FIND_LEMM2]
                )
                >> Cases_on `FIND (λ(n,l). l.frml = h) (toAList g.nodeInfo)`
                >> fs[]
                >> `∀a b. ¬MEM (a,b) (toAList x.nodeInfo) ∨ b.frml ≠ h` by (
                    CCONTR_TAC >> fs[]
                    >> `MEM (a,h) (graphStatesWithId x)` by (
                        PURE_REWRITE_TAC[graphStatesWithId_def,MEM_MAP]
                        >> qexists_tac `(a,b)` >> fs[MEM_toAList]
                    )
                    >> `MEM (a,h) (graphStatesWithId g)` by metis_tac[]
                    >> fs[graphStatesWithId_def,MEM_MAP] >> Cases_on `y''`
                    >> fs[] >> metis_tac[]
                )
                >> Cases_on `FIND (λ(n,l). l.frml = h) (toAList x.nodeInfo)`
                >> fs[] >> Cases_on `x'`
                >> `MEM (q,r) (toAList x.nodeInfo) ∧ (λ(n,l). l.frml = h) (q,r)`
                   by metis_tac[FIND_LEMM2]
                >> fs[] >> metis_tac[]
               )
           ) >> rpt strip_tac
           >> PURE_REWRITE_TAC[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
           >> fs[]
           >- (qexists_tac `label` >> fs[] >> rpt strip_tac
            >- (Cases_on `sucId = nId` >> fs[] >> rw[]
             >- (qexists_tac `frml` >> qexists_tac `nId`
                 >> fs[OPTION_TO_LIST_MEM] >> qexists_tac `l'` >> fs[]
                 >> qexists_tac `x'` >> fs[]
                )
             >- (qexists_tac `suc` >> fs[] >> qexists_tac `sucId` >> fs[]
                >> fs[OPTION_TO_LIST_MEM]
                >> `lookup sucId x.nodeInfo = lookup sucId g.nodeInfo` by (
                     fs[updateNode_def,gfg_component_equality]
                     >> metis_tac[lookup_insert]
                )
                >> fs[] >> qexists_tac `l'` >> fs[] >> qexists_tac `x'` >> fs[]
                )
               )
            >- (simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> fs[]
                >> Cases_on `sucId' = nId` >> fs[] >> rw[]
             >- (qexists_tac `frml` >> fs[]
                 >> `suc' = NEW_LAB` by (
                    fs[updateNode_def,gfg_component_equality]
                    >> metis_tac[lookup_insert,SOME_11]
                  )
                 >> qunabbrev_tac `NEW_LAB` >> fs[gfg_component_equality]
                 >> qexists_tac `nId` >> fs[OPTION_TO_LIST_MEM]
                )
             >- (qexists_tac `suc'` >> fs[] >> qexists_tac `sucId'` >> fs[]
                 >> fs[updateNode_def,gfg_component_equality]
                 >> metis_tac[lookup_insert]
                )
             >- (qexists_tac `NEW_LAB` >> fs[]
                 >> `suc' = frml` by (
                   fs[updateNode_def,gfg_component_equality]
                   >> metis_tac[lookup_insert,SOME_11]
                  )
                 >> `suc'.frml = NEW_LAB.frml` by (
                    qunabbrev_tac `NEW_LAB` >> fs[]
                  )
                 >> fs[] >> qexists_tac `nId` >> fs[updateNode_def]
                 >> fs[gfg_component_equality] >> metis_tac[lookup_insert]
                )
             >- (qexists_tac `suc'` >> fs[] >> qexists_tac `sucId'` >> fs[]
                 >> fs[updateNode_def,gfg_component_equality]
                 >> metis_tac[lookup_insert]
                )
               )
              )
           >- (disj2_tac >> fs[] >> qexists_tac `l'` >> fs[OPTION_TO_LIST_MEM]
               >> metis_tac[]
              )
           >- (qexists_tac `label` >> fs[] >> rpt strip_tac
            >- (Cases_on `sucId = nId` >> fs[] >> rw[]
             >- (qexists_tac `NEW_LAB` >> qexists_tac `nId`
                 >> fs[OPTION_TO_LIST_MEM,updateNode_def,gfg_component_equality]
                 >> metis_tac[lookup_insert]
                )
             >- (qexists_tac `suc` >> fs[] >> qexists_tac `sucId` >> fs[]
                >> fs[OPTION_TO_LIST_MEM,updateNode_def,gfg_component_equality]
                >> metis_tac[lookup_insert]
                )
               )
            >- (simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> fs[]
                >> Cases_on `sucId' = nId` >> fs[] >> rw[]
             >- (qexists_tac `NEW_LAB` >> fs[]
                 >> `suc' = frml` by (
                   fs[updateNode_def,gfg_component_equality]
                   >> metis_tac[lookup_insert,SOME_11]
                  )
                 >> `suc'.frml = NEW_LAB.frml` by (
                    qunabbrev_tac `NEW_LAB` >> fs[]
                  )
                 >> fs[] >> qexists_tac `nId` >> fs[updateNode_def]
                 >> fs[gfg_component_equality] >> metis_tac[lookup_insert]
                )
             >- (qexists_tac `suc'` >> fs[] >> qexists_tac `sucId'` >> fs[]
                             >> fs[updateNode_def,gfg_component_equality]
                             >> metis_tac[lookup_insert]
                )
             >- (qexists_tac `frml` >> fs[]
                 >> `suc' = NEW_LAB` by (
                    fs[updateNode_def,gfg_component_equality]
                    >> metis_tac[lookup_insert,SOME_11]
                  )
                 >> qunabbrev_tac `NEW_LAB` >> fs[gfg_component_equality]
                 >> qexists_tac `nId` >> fs[OPTION_TO_LIST_MEM]
                )
             >- (qexists_tac `suc'` >> fs[] >> qexists_tac `sucId'` >> fs[]
                 >> fs[updateNode_def,gfg_component_equality]
                 >> metis_tac[lookup_insert]
                )
               )
              )
           >- (disj2_tac >> fs[] >> qexists_tac `l'` >> fs[])
         )
         )
      >- metis_tac[FIRST_FLW_LEMM,updateNode_preserves_domain]
   )
   >- (
    (* Q.HO_MATCH_ABBREV_TAC *)
    (*    `?x. (?nodeId. A nodeId ∧ P x nodeId) ∧ Q x` *)
    fs[]
    (* >> Q.HO_MATCH_ABBREV_TAC *)
    (*    `?x. (?nodeId. A nodeId ∧ P x nodeId) ∧ Q x` *)
    (* >> `?nodeId. A nodeId ∧ ?x. P x nodeId ∧ Q x` *)
    (*     suffices_by metis_tac[SWAP_EXISTS_THM] *)
    (* >> qunabbrev_tac `A` >> fs[] *)
    >> Cases_on `q` >> fs[] >> rename[`_ = SOME (nId,frml)`]
    (* >> qunabbrev_tac `P` >> fs[] *)
    >> `nId ∈ domain g.followers` by (
       `nId ∈ domain g.nodeInfo` suffices_by metis_tac[wfg_def]
       >> fs[findNode_def]
       >> `MEM (nId, frml) (toAList g.nodeInfo)` by metis_tac[FIND_LEMM2]
       >> fs[MEM_toAList] >> metis_tac[domain_lookup]
    )
    >> fs[domain_lookup]
    >> Q.HO_MATCH_ABBREV_TAC
        `?x. FOLDR addSingleEdge a_init ls = SOME x ∧ Q x`
    >> `!lab x. MEM (lab,x) ls ==> ?h. MEM (x,h) (toAList g.nodeInfo)` by (
         rpt strip_tac >> qunabbrev_tac `ls` >> fs[MEM_MAP]
         >> fs[CAT_OPTIONS_MEM,findNode_def,MEM_MAP]
         >> `MEM y' (toAList g.nodeInfo)` by metis_tac[FIND_LEMM2]
         >> Cases_on `y'` >> fs[] >> metis_tac[]
       )
    >> qabbrev_tac `LABEL =
            <|edge_grp := (if v = [] then 1 else (HD (MAP FST v)).edge_grp) + 1;
              pos_lab := l;
              neg_lab := l0|>`
    >> qabbrev_tac `
           TO_LABELS = λl.
              MAP (λi. (LABEL,i))
               (MAP FST
                (CAT_OPTIONS
                 ((MAP (λs. findNode (λ(n,l). l.frml = s) g) l)
                 ++ [findNode (λ(n,l). l.frml = h) g])))`
    >> `ls = TO_LABELS t` by (qunabbrev_tac `TO_LABELS` >> simp[])
    >> `?n. findNode (λ(n,l). l.frml = h) g = SOME n` by (
        `∃y. h = (SND y).frml ∧ MEM y (toAList g.nodeInfo)` by metis_tac[]
        >> simp[findNode_def]
        >> `(λ(n,l). l.frml = (SND y').frml) y'` by (Cases_on `y'` >> fs[])
        >> metis_tac[FIND_LEMM]
    )
    >> `!i p n s. (i,p,n,s) ∈ extractTrans g (SND y).frml
                    ==> i < LABEL.edge_grp` by (
        simp[extractTrans_def] >> rpt strip_tac
        >- (Cases_on `v` >> fs[OPTION_TO_LIST_MEM]
            >> `?s_fr. s_fr ∈ s` by fs[MEMBER_NOT_EMPTY]
            >> fs[] >> rw[] >> fs[] >> qunabbrev_tac `LABEL`
            >> fs[theorem "edgeLabelAA_component_equality"] >> rw[]
            >> fs[first_flw_has_max_counter_def] >> rw[]
            >> `∀y. MEM y t' ⇒ (FST y).edge_grp ≤ (FST h').edge_grp`
               by (
               `nId ∈ domain g.nodeInfo` suffices_by metis_tac[]
               >> metis_tac[domain_lookup,wfg_def]
             )
            >> first_x_assum (qspec_then `(label,sucId)` mp_tac) >> simp[]
           )
        >- (qunabbrev_tac `LABEL` >> simp[]
            >> metis_tac[DECIDE``!x. 0 < x + 1``]
           )
    )
    >> `!fs qs. ((!lab x. MEM (lab,x) qs
                    ==> (?h. MEM (x,h) (toAList g.nodeInfo)
                          ∧ (lab = LABEL)))
               ∧ (qs = TO_LABELS fs)
               ∧ (!x. MEM x fs
                      ==> ∃y. x = (SND y).frml ∧ MEM y (toAList g.nodeInfo)))
             ==> ?m. (FOLDR addSingleEdge a_init qs = SOME m)
                   ∧ (g.nodeInfo = m.nodeInfo)
                   ∧ (wfg m)
                   (* ∧ (?e. ((LABEL.edge_grp,l,l0,e) ∈ extractTrans m frml.frml) *)
                   (*       ∧ (!x. MEM (LABEL, x) qs *)
                   (*           ==> ?node. (lookup x m.nodeInfo = SOME node) *)
                   (*                    ∧ (node.frml ∈ e))) *)
                   ∧ (!a.
                       if a = f
                       then extractTrans m a
                             = (extractTrans g a
                                ∪ { (LABEL.edge_grp,l,l0,h INSERT set fs)})
                       else extractTrans m a = extractTrans g a)
                   ∧ (first_flw_has_max_counter m)
                   ∧ (!x id fls q r.
                         findNode (λ(n,l). l.frml = f) m = SOME (q,r)
                       ∧ (lookup q m.followers = SOME fls)
                       ==> ((!f. MEM f fls
                                ==> (FST f).edge_grp <= LABEL.edge_grp)
                           ∧ !o_id. ~(o_id = q)
                                   ==> (lookup o_id m.nodeInfo
                                        = lookup o_id g.nodeInfo)))` by (
       (* HO_MATCH_MP_TAC SNOC_INDUCT >> rpt strip_tac >> fs[] *)
       Induct_on `fs` >> fs[]
       >- (
        qunabbrev_tac `a_init` >> rpt strip_tac
        >> `TO_LABELS [] = [(LABEL,FST n)]` by (
            qunabbrev_tac `TO_LABELS` >> fs[CAT_OPTIONS_def]
        )
        >> fs[]
        >> `?k. addSingleEdge (LABEL,FST n) (SOME g) = SOME k
              ∧ (g.nodeInfo = k.nodeInfo) ∧ (wfg k)` by (
            qunabbrev_tac `addSingleEdge` >> fs[]
            >> `?k. addEdge nId (LABEL,FST n) g = SOME k` suffices_by (
                metis_tac[addEdge_preserves_wfg,addEdge_preserves_nodeInfo]
            )
            >> simp[addEdge_def] >> fs[findNode_def]
            >> `MEM (nId,frml) (toAList g.nodeInfo)
                ∧ MEM (FST n,h') (toAList g.nodeInfo)` by metis_tac[FIND_LEMM2]
            >> metis_tac[MEM_toAList,domain_lookup]
        )
        >> qexists_tac `k`
        >> `∀fls q r.
            findNode (λ(n,l). l.frml = (SND y).frml) k = SOME (q,r)
          ∧ lookup q k.followers = SOME fls
            ==> (∀f. MEM f fls ⇒ (FST f).edge_grp ≤ LABEL.edge_grp
               ∧ ∀o_id. o_id ≠ q
                          ⇒ lookup o_id k.nodeInfo = lookup o_id g.nodeInfo)`
            by (
            qunabbrev_tac `addSingleEdge` >> fs[addEdge_def]
            >> simp[first_flw_has_max_counter_def] >> rpt strip_tac
            >> `(q,r) = (nId,frml)` by fs[findNode_def]
            >> Cases_on `followers_old` >> fs[first_flw_has_max_counter_def]
            >> fs[gfg_component_equality] >> rw[]
            >- (`fls = [(LABEL,FST n)]` by metis_tac[lookup_insert,SOME_11]
                >> fs[]
               )
            >-(`(FST h'').edge_grp <= LABEL.edge_grp` by (
                qunabbrev_tac `LABEL`
                >> fs[theorem "edgeLabelAA_component_equality"]
               )
               >> `fls =  (LABEL,FST n)::h''::t'`
                   by metis_tac[lookup_insert,SOME_11]
               >> rw[] >> fs[]
               >> metis_tac[DECIDE``!x y z. x <= y ∧ y <= z ==> x <= z``])
        )
        >> `first_flw_has_max_counter k` by (
            qunabbrev_tac `addSingleEdge` >> fs[addEdge_def]
            >> simp[first_flw_has_max_counter_def] >> rpt strip_tac
            >> first_x_assum (qspec_then `(LABEL,FST n)::followers_old` mp_tac)
            >> rpt strip_tac
            >> first_x_assum (qspec_then `nId` mp_tac) >> rpt strip_tac
            >> first_x_assum (qspec_then `frml` mp_tac)
            >> `findNode (λ(n,l). l.frml = (SND y).frml) k = SOME (nId,frml)`
               by metis_tac[findNode_def,SOME_11]
            >> `lookup nId k.followers = SOME ((LABEL,FST n)::followers_old)`
               by (fs[gfg_component_equality]
                   >> metis_tac[lookup_insert,SOME_11])
            >> simp[] >> rpt strip_tac
            >> Cases_on `x_id = nId` >> fs[gfg_component_equality]
            >> rw[]
            >> `lookup x_id g.followers = SOME (fl::fls)` by (
                metis_tac[lookup_insert,SOME_11]
            )
            >> fs[first_flw_has_max_counter_def] >> metis_tac[]
        )
        >> fs[] >> rpt strip_tac >> fs[]
        >> Cases_on `(SND y).frml = a` >> fs[]
        >- (
         `findNode (λ(n,l). l.frml = a) k = SOME (nId,frml)`
           by fs[findNode_def]
         >> `!id. lookup id k.followers =
                   if id = nId then SOME ((LABEL,FST n)::v)
                               else lookup id g.followers` by (
           qunabbrev_tac `addSingleEdge` >> fs[addEdge_def]
           >> rpt strip_tac >> Cases_on `id = nId` >> fs[gfg_component_equality]
           >> metis_tac[lookup_insert]
         )
         >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> fs[]
         >- (Cases_on `x = (LABEL.edge_grp,l,l0,{h})` >> fs[]
             >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
             >> simp[extractTrans_def] >> rpt strip_tac
             >- (disj1_tac >> fs[] >> qexists_tac `label` >> fs[]
                 >> `~(LABEL = label)` by (
                      qunabbrev_tac `LABEL` >> Cases_on `x` >> fs[]
                      >> rw[] >> fs[theorem "edgeLabelAA_component_equality"]
                      >> POP_ASSUM mp_tac
                      >> Q.HO_MATCH_ABBREV_TAC `~(H = {h}) ==> A`
                      >> `~A ==> H = {h}` suffices_by metis_tac[]
                      >> qunabbrev_tac `A` >> qunabbrev_tac `H`
                      >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                      >> fs[OPTION_TO_LIST_MEM,findNode_def]
                      >> Cases_on `n` >> rw[] >> fs[]
                      >> rename[`FIND (λ(n,l). l.frml = h) _  = SOME (id,node)`,
                                `MEM (id,h') (toAList k.nodeInfo)`]
                      >- (`(suc = node) ∧ (λ(n,l). l.frml = h) (id,node)`
                            by metis_tac[FIND_LEMM2,MEM_toAList,SOME_11]
                          >> fs[]
                         )
                      >- (qexists_tac `node`
                          >> `(λ(n,l). l.frml = h) (id,node)`
                                by metis_tac[FIND_LEMM2]
                          >> fs[theorem "edgeLabelAA_component_equality"]
                          >> metis_tac[MEM_toAList,FIND_LEMM2]
                         )
                      >- (`suc = node ∧ (λ(n,l). l.frml = h) (id,node)`
                             by metis_tac[FIND_LEMM2,MEM_toAList,SOME_11]
                           >> fs[]
                         )
                      >- (Cases_on `v` >> fs[first_flw_has_max_counter_def]
                       >- (Cases_on `label` >> Cases_on `h''`
                           >> fs[theorem "edgeLabelAA_component_equality"])
                       >- (`∀y. MEM y t'
                               ⇒ (FST y).edge_grp ≤ (FST h'').edge_grp`
                            by (
                              `nId ∈ domain g.nodeInfo`
                                suffices_by metis_tac[wfg_def,domain_lookup]
                               >> metis_tac[domain_lookup,wfg_def]
                            )
                            >> first_x_assum (qspec_then `(label,sucId)` mp_tac)
                            >> simp[]
                          )
                         )
                      >- (qexists_tac `node`
                          >> `(λ(n,l). l.frml = h) (id,node)`
                             by metis_tac[FIND_LEMM2]
                          >> fs[theorem "edgeLabelAA_component_equality"]
                          >> metis_tac[MEM_toAList,FIND_LEMM2]
                         )
                  )
                 >> rpt strip_tac >> simp[SET_EQ_SUBSET,SUBSET_DEF]
                 >> fs[OPTION_TO_LIST_MEM]
                )
             >- metis_tac[]
            )
         >- (`FST x < LABEL.edge_grp` by (
              Cases_on `x` >> Cases_on `r` >> Cases_on `r'`
              >> fs[] >> metis_tac[]
             )
             >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
             >> simp[extractTrans_def] >> rpt strip_tac
             >- (disj1_tac >> qexists_tac `label` >> fs[]
                 >> rpt strip_tac >> simp[SET_EQ_SUBSET,SUBSET_DEF]
                 >- (fs[OPTION_TO_LIST_MEM] >> POP_ASSUM mp_tac
                     >> dsimp[]
                     >> Q.HO_MATCH_ABBREV_TAC `~(A = {})`
                     >> `?a. a ∈ A` suffices_by metis_tac[MEMBER_NOT_EMPTY]
                     >> qunabbrev_tac `A` >> fs[]
                     >> `?a. a ∈
                           {suc.frml |
                            ∃sucId.
                             MEM (label,sucId) v
                             ∧ SOME suc = lookup sucId k.nodeInfo}`
                        by metis_tac[MEMBER_NOT_EMPTY]
                     >> fs[] >> metis_tac[]
                    )
                 >- (rpt strip_tac >> fs[OPTION_TO_LIST_MEM]
                     >- (rw[] >> fs[] >> metis_tac[])
                     >- (Cases_on `x` >> fs[])
                     >- (rw[] >> fs[] >> metis_tac[])
                    )
                )
             >- (disj2_tac >> fs[] >> metis_tac[])
            )
         >- (simp[extractTrans_def] >> qexists_tac `LABEL` >> fs[]
            >> rpt strip_tac
            >- (qunabbrev_tac `LABEL` >> fs[]
                >> metis_tac[DECIDE ``!x. 0 < x + 1``]
               )
            >- (POP_ASSUM mp_tac >> simp[] >> Q.HO_MATCH_ABBREV_TAC `~(A = {})`
                >> `?a. a ∈ A` suffices_by metis_tac[MEMBER_NOT_EMPTY]
                >> qunabbrev_tac `A` >> Cases_on `n` >> qexists_tac `r.frml`
                >> fs[] >> qexists_tac `r` >> fs[OPTION_TO_LIST_MEM]
                >> metis_tac[findNode_def,FIND_LEMM2,MEM_toAList]
               )
            >- (qunabbrev_tac `LABEL` >> fs[])
            >- (qunabbrev_tac `LABEL` >> fs[])
            >- (simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
             >- (Cases_on `n` >> fs[] >> qexists_tac `r`
                 >> fs[findNode_def]
                 >> `(λ(n,l). l.frml = h) (q,r)
                   ∧ MEM (q,r) (toAList k.nodeInfo)`
                   by metis_tac[FIND_LEMM2]
                 >> fs[] >> qexists_tac `q` >> fs[OPTION_TO_LIST_MEM]
                 >> metis_tac[MEM_toAList]
                )
             >- (fs[OPTION_TO_LIST_MEM] >> Cases_on `n` >> fs[]
                 >> fs[findNode_def]
                 >> `(λ(n,l). l.frml = h) (q,r)
                   ∧ MEM (q,r) (toAList k.nodeInfo)`
                     by metis_tac[FIND_LEMM2]
                 >> rw[] >> fs[]
                 >- (`suc = r` by metis_tac[MEM_toAList,SOME_11]
                     >> fs[])
                 >- (qunabbrev_tac `LABEL` >> fs[] >> Cases_on `v`
                     >> fs[] >> Cases_on `h''`
                     >> fs[theorem "edgeLabelAA_component_equality"]
                     >> fs[first_flw_has_max_counter_def]
                     >> `∀y. MEM y t'
                          ⇒ (FST y).edge_grp ≤ (FST (q',r')).edge_grp`
                        by (
                         `nId ∈ domain g.nodeInfo` suffices_by metis_tac[]
                         >> metis_tac[domain_lookup,wfg_def]
                      )
                     >> `q'.edge_grp + 1 <= q'.edge_grp` by (
                        first_x_assum (qspec_then `
                          (<|edge_grp := q'.edge_grp + 1; pos_lab := l;
                           neg_lab := l0|>,sucId)` mp_tac) >> simp[]
                      )
                     >> fs[]
                    )
                )
               )
            )
        )
        >- (`findNode (λ(n,l). l.frml = a) g
              = findNode (λ(n,l). l.frml = a) k` by fs[findNode_def]
            >> Cases_on `findNode (λ(n,l). l.frml = a) g` >> fs[]
            >- (
             `!x b. (findNode (λ(n,l). l.frml = b) x = NONE)
                     ==> (extractTrans x b = {})` by (
                 rpt strip_tac
                 >> `!q. ~ (q ∈ extractTrans x b)`
                   suffices_by metis_tac[MEMBER_NOT_EMPTY]
                 >> simp[extractTrans_def] >> rpt strip_tac
                 >> fs[]
                 >- (disj2_tac >> disj1_tac
                     >> Q.HO_MATCH_ABBREV_TAC `A = {}`
                     >> `!x. ~(x ∈ A)` suffices_by metis_tac[MEMBER_NOT_EMPTY]
                     >> rpt strip_tac >> qunabbrev_tac `A` >> fs[OPTION_TO_LIST_MEM]
                     >> metis_tac[NOT_SOME_NONE]
                    )
                 >- (disj2_tac >> fs[OPTION_TO_LIST_MEM]
                     >> metis_tac[NOT_SOME_NONE])
             )
             >> metis_tac[]
             )
            >- (
             Cases_on `x`
             >> `lookup q k.followers = lookup q g.followers` by (
                 qunabbrev_tac `addSingleEdge` >> fs[addEdge_def]
                 >> `~(q = nId)` by (
                   fs[findNode_def]
                   >> `(λ(n,l). l.frml = a) (q,r)
                       ∧ MEM (q,r) (toAList g.nodeInfo)`
                      by metis_tac[FIND_LEMM2]
                   >> `(λ(n,l). l.frml = (SND y).frml) (nId,frml)
                       ∧ MEM (nId,frml) (toAList g.nodeInfo)`
                       by metis_tac[FIND_LEMM2]
                   >> CCONTR_TAC >> rw[] >> fs[MEM_toAList]
                   >> metis_tac[]
                 )
                 >> fs[gfg_component_equality] >> metis_tac[lookup_insert]
             )
             >> `!x1 x2 b id n.
                  (findNode (λ(n,l). l.frml = b) x1 = SOME (id,n))
                ∧ (findNode (λ(n,l). l.frml = b) x2 = SOME (id,n))
                ∧ (lookup id x1.followers = lookup id x2.followers)
                ∧ (x1.nodeInfo = x2.nodeInfo)
                ==> (extractTrans x1 b ⊆ extractTrans x2 b)` by (
                 simp[extractTrans_def,SUBSET_DEF] >> rpt strip_tac
             )
             >> metis_tac[SET_EQ_SUBSET]
             )
           )
       )
    >- (rpt strip_tac
        >> first_assum (qspec_then `h'` mp_tac) >> rpt strip_tac >> fs[]
        >> rename[`x_new = (SND nodeIdPair).frml`]
        >> Cases_on `nodeIdPair` >> fs[]
        >> rename [`MEM (id,node) (toAList g.nodeInfo)`]
        >> `findNode (λ(n,l). l.frml = x_new) g = SOME (id,node)` by (
             `?q1 r1. findNode (λ(n,l). l.frml = x_new) g = SOME (q1,r1)` by (
                 `(λ(n,l). l.frml = x_new) (id,node)` by fs[]
                 >> simp[findNode_def]
                 >> IMP_RES_TAC FIND_LEMM >> fs[]
                 >> Cases_on `y'` >> fs[]
             )
             >> fs[unique_node_formula_def, findNode_def]
             >> `MEM (q1,r1.frml) (graphStatesWithId g)` by(
                 fs[MEM_MAP,graphStatesWithId_def]
                 >> qexists_tac `(q1,r1)` >> fs[]
                 >> metis_tac[FIND_LEMM2]
             )
             >> `MEM (id,node.frml) (graphStatesWithId g)` by(
                 fs[MEM_MAP,graphStatesWithId_def]
                   >> qexists_tac `(id,node)` >> fs[]
                   >> metis_tac[FIND_LEMM2]
             )
             >> `(λ(n,l). l.frml = x_new) (q1,r1)` by metis_tac[FIND_LEMM2]
             >> fs[]
             >> `q1 = id` by (rw[] >> metis_tac[])
             >> rw[] >> fs[graphStatesWithId_def,MEM_MAP]
             >> `MEM (id,r1) (toAList g.nodeInfo)` by metis_tac[FIND_LEMM2]
             >> `MEM (id,node) (toAList g.nodeInfo)` by metis_tac[FIND_LEMM2]
             >> metis_tac[MEM_toAList,SOME_11]
         )
        >> `TO_LABELS (x_new::fs) = (LABEL,id)::(TO_LABELS fs)` by (
             qunabbrev_tac `TO_LABELS`
             >> fs[CAT_OPTIONS_def,CAT_OPTIONS_MAP_LEMM,CAT_OPTIONS_MEM,
                   MEM_MAP,CAT_OPTIONS_APPEND]
         )
        >> rw[]
        >> `∀lab x.
              MEM (lab,x) (TO_LABELS fs) ⇒
              ∃h. MEM (x,h) (toAList g.nodeInfo) ∧ lab = LABEL`
         by (rpt strip_tac
             >> `MEM (lab,x) (TO_LABELS (node.frml::fs))` by (
                  qunabbrev_tac `TO_LABELS`
                  >> fs[CAT_OPTIONS_MAP_LEMM,CAT_OPTIONS_MEM,MEM_MAP]
                  >> dsimp[] >> metis_tac[]
              )
             >> metis_tac[]
            )
         >> `∃m.
              FOLDR addSingleEdge a_init (TO_LABELS fs) = SOME m
              ∧ g.nodeInfo = m.nodeInfo ∧ wfg m
              ∧ (∀a.
              if a = (SND y).frml then
                  extractTrans m (SND y).frml =
                  extractTrans g (SND y).frml
                               ∪ {(LABEL.edge_grp,l,l0,h INSERT set fs)}
              else extractTrans m a = extractTrans g a)
              ∧ (first_flw_has_max_counter m)
              ∧ (∀fls q r.
                  findNode (λ(n,l). l.frml = (SND y).frml) m = SOME (q,r)
                  ∧ lookup q m.followers = SOME fls
                   ==> (∀f. MEM f fls ⇒ (FST f).edge_grp ≤ LABEL.edge_grp
                      ∧ (∀o_id. o_id ≠ q
                          ⇒ lookup o_id m.nodeInfo = lookup o_id g.nodeInfo)))`
             by metis_tac[]
         >> qabbrev_tac `A = FOLDR addSingleEdge a_init (TO_LABELS fs)`
         >> `?m1. addSingleEdge (LABEL,id) A = SOME m1
                ∧ wfg m1 ∧ (m1.nodeInfo = m.nodeInfo)
                ∧ (∀fls q r.
                   findNode (λ(n,l). l.frml = (SND y).frml) m1 = SOME (q,r)
                 ∧ lookup q m1.followers = SOME fls
                     ==> (∀f. MEM f fls ⇒ (FST f).edge_grp ≤ LABEL.edge_grp
                       ∧ (∀o_id. o_id ≠ q
                           ⇒ lookup o_id m1.nodeInfo = lookup o_id g.nodeInfo)))
                ∧ (first_flw_has_max_counter m1)`
             by (
             qunabbrev_tac `addSingleEdge` >> fs[]
             >> Q.HO_MATCH_ABBREV_TAC `
                 ?m1. addEdge nId (LABEL,id) m = SOME m1 ∧ wfg m1
                    ∧ m1.nodeInfo = m.nodeInfo ∧ B m1 ∧ C m1`
             >> `?m1. addEdge nId (LABEL,id) m = SOME m1
                    ∧ (m1.nodeInfo = m.nodeInfo ==> B m1)
                    ∧ (m1.nodeInfo = m.nodeInfo ∧ B m1 ==> C m1)`
                   suffices_by metis_tac[addEdge_preserves_nodeInfo,
                                         addEdge_preserves_wfg]
             >> simp[addEdge_def] >> fs[]
             >> `nId ∈ domain m.nodeInfo ∧ id ∈ domain m.nodeInfo` by (
                 fs[findNode_def]
             >> metis_tac[MEM_toAList,domain_lookup,FIND_LEMM2]
             )
             >> fs[]
             >> `∃m1.
                 (∃followers_old.
                  lookup nId m.followers = SOME followers_old ∧
                    m with followers updated_by insert nId ((LABEL,id)::followers_old) =
                  m1)` by metis_tac[domain_lookup,wfg_def]
             >> qexists_tac `m1` >> fs[]
             >> qunabbrev_tac `B` >> rpt strip_tac >> fs[] >> rpt strip_tac
             >- (`(q,r) = (nId,frml)` by metis_tac[findNode_def,SOME_11]
                >> rw[] >> fs[]
                >> fs[gfg_component_equality] >> rw[] >> fs[]
                >> metis_tac[findNode_def,SOME_11])
             >- (qunabbrev_tac `C`
                 >> fs[first_flw_has_max_counter_def]
                 >> rpt strip_tac >> fs[]
                 >> first_x_assum (qspec_then `(LABEL,id)::followers_old` mp_tac)
                 >> rpt strip_tac
                 >> first_x_assum (qspec_then `nId` mp_tac) >> rpt strip_tac
                 >> first_x_assum (qspec_then `frml` mp_tac)
                 >> `findNode (λ(n,l). l.frml = (SND y).frml) m1 = SOME (nId,frml)`
                    by metis_tac[findNode_def,SOME_11]
                 >> `lookup nId m1.followers = SOME ((LABEL,id)::followers_old)`
                      by (fs[gfg_component_equality]
                             >> metis_tac[lookup_insert,SOME_11])
                 >> simp[] >> rpt strip_tac
                 >> Cases_on `x_id = nId` >> fs[gfg_component_equality] >> rw[]
                 >> `lookup x_id m.followers = SOME (fl::fls)` by (
                      metis_tac[lookup_insert,SOME_11]
                  )
                 >> fs[first_flw_has_max_counter_def] >> metis_tac[]
                )
         )
         >> qexists_tac `m1` >> fs[] >> rpt strip_tac
         >> Cases_on `a = (SND y).frml` >> fs[]
         >- (first_x_assum (qspec_then `a` mp_tac) >> simp[] >> rw[]
             >> Q.HO_MATCH_ABBREV_TAC `M1 = G ∪ {N}`
             >> `!x. ((x ∈ M1 ∧ ((FST x) = LABEL.edge_grp))
                       ==> (x = N))
                   ∧ (x ∈ M1 ∧ ~((FST x) = LABEL.edge_grp)
                       ==> x ∈ G)
                   ∧ ((!y. (y ∈ M1 ∧ ((FST y) = LABEL.edge_grp))
                          ==> (y = N))
                          ==> (x ∈ G \/ x = N ==> x ∈ M1))` suffices_by (
                  simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                  >> metis_tac[IN_SING]
              )
             >> rpt strip_tac >> qunabbrev_tac `M1` >> qunabbrev_tac `G`
             >> qunabbrev_tac `N`
             >- (qunabbrev_tac `addSingleEdge` >> fs[addEdge_def]
                 >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
                 >> simp[extractTrans_def] >> rpt strip_tac >> fs[]
                 >- (
                   POP_ASSUM mp_tac >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
                   >> Q.HO_MATCH_ABBREV_TAC `~(B = {}) ==> C` >> rpt strip_tac
                   >> `?b. b ∈ B` by metis_tac[MEMBER_NOT_EMPTY]
                   >> first_x_assum (qspec_then `followers_old` mp_tac)
                   >> rpt strip_tac >> fs[]
                   >> `(label.edge_grp = LABEL.edge_grp)
                      ==> (LABEL = label
                       ∧ ((LABEL = label)
                              ==> (B = h INSERT node.frml INSERT set fs)))`
                        suffices_by (
                          qunabbrev_tac `C` >> rpt strip_tac
                          >> qunabbrev_tac `LABEL` >> rw[]
                          >> fs[theorem "edgeLabelAA_component_equality"] >> rw[]
                   )
                   >> rpt strip_tac
                   >- (qunabbrev_tac `B` >> fs[OPTION_TO_LIST_MEM]
                       >> `unique_node_formula m` by (
                            fs[unique_node_formula_def,graphStatesWithId_def]
                            >> metis_tac[]
                        )
                       >> `findNode (λ(n,l). l.frml = (SND y).frml) m = SOME x'`
                          by (fs[findNode_def] >> metis_tac[SOME_11])
                       >> Cases_on `x'` >> fs[] >> Cases_on `nId = q`
                       >> rw[] >> fs[gfg_component_equality]
                       >> rw[] >> fs[]
                       >-(`∃s.
                           (label.edge_grp,label.pos_lab,label.neg_lab,s)
                             ∈ extractTrans m (SND y).frml ∧ suc.frml ∈ s` by (
                           `r.frml = (SND y).frml` by fs[findNode_def,FIND_LEMM]
                           >> `lookup nId m.nodeInfo = SOME r` by (
                               metis_tac[FIND_LEMM2,findNode_def,MEM_toAList,SOME_11]
                           )
                           >> metis_tac[EXTR_TRANS_LEMM]
                          )
                          >> `(label.edge_grp,label.pos_lab,label.neg_lab,s)
                               ∈ extractTrans g (SND y).frml ∪
                                  {(LABEL.edge_grp,l,l0,h INSERT set fs)}`
                              by metis_tac[]
                          >> fs[IN_UNION]
                        >- (
                         `label.edge_grp < LABEL.edge_grp` by metis_tac[]
                         >> fs[])
                        >- (
                         qunabbrev_tac `LABEL` >> rw[]
                         >> fs[theorem "edgeLabelAA_component_equality"]
                        )
                        )
                       >- (
                        `lookup q m.followers = SOME l'`
                          by metis_tac[lookup_insert]
                        >> `∃s.
                             (label.edge_grp,label.pos_lab,label.neg_lab,s)
                             ∈ extractTrans m (SND y).frml ∧ suc.frml ∈ s` by (
                             `r.frml = (SND y).frml` by fs[findNode_def,FIND_LEMM]
                             >> `lookup q m.nodeInfo = SOME r` by (
                                 metis_tac[FIND_LEMM2,findNode_def,MEM_toAList]
                             )
                             >> metis_tac[EXTR_TRANS_LEMM]
                        )
                        >> `(label.edge_grp,label.pos_lab,label.neg_lab,s)
                             ∈ extractTrans g (SND y).frml ∪
                             {(LABEL.edge_grp,l,l0,h INSERT set fs)}`
                              by metis_tac[]
                        >> fs[IN_UNION]
                        >- (`label.edge_grp < LABEL.edge_grp` by metis_tac[]
                            >> fs[])
                        >- (qunabbrev_tac `LABEL` >> rw[]
                            >> fs[theorem "edgeLabelAA_component_equality"]
                           )
                        )
                      )
                   >- (simp[SET_EQ_SUBSET,SUBSET_DEF] >> conj_tac
                       >> qunabbrev_tac `B` >> fs[OPTION_TO_LIST_MEM]
                       >- (rpt strip_tac >> rename[`_ x1 = SOME l1`]
                           >> `x1 = (nId,frml)` by
                             (fs[findNode_def] >> rw[] >> fs[])
                           >> rw[] >> fs[] >> rw[]
                           >> `(LABEL,sucId') = (LABEL,id)
                            \/ (MEM (LABEL,sucId') followers_old)` by fs[]
                           >- (rw[]
                               >> `suc' = node`
                                    by metis_tac[findNode_def,FIND_LEMM2,
                                                 MEM_toAList,SOME_11]
                               >> fs[]
                              )
                           >- (
                            `∃s.
                             (LABEL.edge_grp,LABEL.pos_lab,LABEL.neg_lab,s)
                              ∈ extractTrans m (SND y).frml ∧ suc'.frml ∈ s` by (
                              `unique_node_formula m` by (
                               fs[unique_node_formula_def,graphStatesWithId_def]
                                >> metis_tac[]
                              )
                              >> `lookup nId m.nodeInfo = SOME frml`
                                 by metis_tac[findNode_def,FIND_LEMM2,
                                              MEM_toAList,SOME_11]
                              >> `frml.frml = (SND y).frml` by fs[]
                              >> metis_tac[EXTR_TRANS_LEMM]
                            )
                            >> `(LABEL.edge_grp,LABEL.pos_lab,LABEL.neg_lab,s)
                                ∈ extractTrans g (SND y).frml ∪
                                 {(LABEL.edge_grp,l,l0,h INSERT set fs)}`
                               by metis_tac[]
                            >> fs[IN_UNION] >> fs[]
                            >> `LABEL.edge_grp < LABEL.edge_grp` by metis_tac[]
                            >> fs[]
                            )
                          )
                       >- (
                        rename[`_ x1 = SOME l1`]
                        >> `x1 = (nId,frml)` by
                          (fs[findNode_def] >> rw[] >> fs[])
                        >> `(LABEL.edge_grp,l,l0,h INSERT set fs)
                            ∈ extractTrans m (SND y).frml` by fs[]
                        >> POP_ASSUM mp_tac
                        >> PURE_REWRITE_TAC[extractTrans_def] >> fs[]
                        >> rpt strip_tac >> rw[]
                        >> `LABEL = label'` by (
                            qunabbrev_tac `LABEL`
                            >> fs[theorem "edgeLabelAA_component_equality"]
                        ) >> rw[]
                        >- (
                         POP_ASSUM mp_tac >> POP_ASSUM mp_tac
                         >> Q.HO_MATCH_ABBREV_TAC `
                             h INSERT set fs = A ==> B`
                         >> strip_tac >> `h ∈ A` by metis_tac[IN_INSERT]
                         >> qunabbrev_tac `A` >> qunabbrev_tac `B`
                         >> fs[OPTION_TO_LIST_MEM] >> rw[] >> fs[]
                         >> `x' = (nId,frml)` by fs[findNode_def]
                         >> rw[] >> fs[] >> rw[] >> metis_tac[]
                        )
                        >- (
                         qexists_tac `node` >> fs[] >> qexists_tac `id` >> fs[]
                         >> rw[] >> fs[]
                         >> metis_tac[MEM_toAList,SOME_11]
                        )
                        >- (
                         POP_ASSUM mp_tac >> POP_ASSUM mp_tac
                         >> POP_ASSUM mp_tac
                         >> Q.HO_MATCH_ABBREV_TAC `
                              h INSERT set fs = A ==> MEM x' fs ==> B`
                         >> strip_tac >> strip_tac
                         >> `set fs ⊆ A`
                             by metis_tac[INSERT_SING_UNION,SUBSET_UNION]
                         >> `x' ∈ A` by metis_tac[SUBSET_DEF,MEM]
                         >> qunabbrev_tac `A` >> qunabbrev_tac `B`
                         >> fs[OPTION_TO_LIST_MEM] >> rw[] >> fs[]
                         >> `x'' = (nId,frml)` by fs[findNode_def]
                         >> rw[] >> fs[] >> rw[] >> metis_tac[]
                        )
                        )
                      )
                  )
                   >- (qunabbrev_tac `LABEL`
                       >> fs[theorem "edgeLabelAA_component_equality"]
                       >> `FST x = 0` by (Cases_on `x` >> fs[])
                       >> fs[]
                    )
                )
             >- (`x ∈ extractTrans m (SND y).frml` by (
                   POP_ASSUM mp_tac >> POP_ASSUM mp_tac
                   >> PURE_REWRITE_TAC[extractTrans_def] >> simp[]
                   >> fs[]
                   >> rpt strip_tac
                   >- (
                    disj1_tac >> qexists_tac `label` >> fs[]
                    >> Q.HO_MATCH_ABBREV_TAC `~(A = {}) ∧ B = A`
                    >> `B = A` suffices_by metis_tac[]
                    >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                    >> qunabbrev_tac `A` >> qunabbrev_tac `B`
                    >> fs[OPTION_TO_LIST_MEM]
                    >> qexists_tac `suc` >> fs[] >> qexists_tac `sucId` >> fs[]
                    >> `x'' = (nId,frml)`
                        by metis_tac[findNode_def,SOME_11]
                    >> rw[] >> fs[] >> rw[]
                    >> qunabbrev_tac `addSingleEdge` >> fs[addEdge_def]
                    >> fs[gfg_component_equality] >> rw[]
                    >- (qexists_tac `followers_old` >> fs[] >> rw[]
                        >- (qexists_tac `(nId,frml)` >> fs[]
                             >> metis_tac[findNode_def,SOME_11]
                           )
                        >- (`l' = (LABEL,id)::followers_old`
                              by metis_tac[lookup_insert,SOME_11]
                            >> fs[] >> rw[]
                           )
                       )
                    >- (qexists_tac `(LABEL,id)::l'` >> fs[]
                        >> qexists_tac `(nId,frml)` >> fs[] >> rw[]
                        >- metis_tac[findNode_def,SOME_11]
                        >- metis_tac[lookup_insert,SOME_11]
                       )
                   )
                   >- (disj2_tac >> fs[OPTION_TO_LIST_MEM] >> qexists_tac `l'`
                       >> fs[] >> qexists_tac `l''` >> fs[]
                       >> `x' = (nId,frml)`
                           by metis_tac[findNode_def,SOME_11]
                       >> rw[] >> fs[] >> rw[] >> qexists_tac `(nId,frml)`
                       >> fs[] >> fs[findNode_def]
                      )
                 )
                 >> `x ∈ extractTrans g (SND y).frml ∪
                       {(LABEL.edge_grp,l,l0,h INSERT set fs)}` by metis_tac[]
                 >> fs[IN_UNION] >> Cases_on `x` >> rw[] >> fs[]
                )
             >- (`x ∈ extractTrans m (SND y).frml`
                  by metis_tac[UNION_SUBSET,SUBSET_DEF]
                 >> `FST x < LABEL.edge_grp` by (
                    Cases_on `x` >> Cases_on `r` >> Cases_on `r'` >> fs[]
                    >> metis_tac[]
                 )
                 >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
                 >> PURE_REWRITE_TAC[extractTrans_def] >> fs[] >> rpt strip_tac
                 >- (disj1_tac >> qexists_tac `label` >> fs[]
                     >> Q.HO_MATCH_ABBREV_TAC `~(A = {}) ∧ B = A`
                     >> `B = A` suffices_by metis_tac[]
                     >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                     >> qunabbrev_tac `A` >> qunabbrev_tac `B`
                     >> fs[OPTION_TO_LIST_MEM]
                     >> qexists_tac `suc` >> fs[] >> qexists_tac `sucId` >> fs[]
                     >> qunabbrev_tac `addSingleEdge` >> fs[addEdge_def]
                     >> rw[] >> fs[] >> rw[]
                     >- (
                      `x'' = (nId,frml)`
                         by metis_tac[findNode_def,SOME_11]
                       >> rw[] >> qexists_tac `(LABEL,id)::followers_old`
                       >> fs[] >> rw[]
                       >> qexists_tac `(nId,frml)` >> fs[gfg_component_equality]
                       >> simp[findNode_def] >> metis_tac[findNode_def]
                      )
                     >- (`x'' = (nId,frml)`
                          by (Cases_on `x''` >> fs[findNode_def])
                          >> rw[] >> qexists_tac `followers_old`
                          >> fs[] >> rw[]
                          >- (qexists_tac `(nId,frml)`
                             >> fs[gfg_component_equality]
                             >> simp[findNode_def] >> metis_tac[findNode_def])
                          >- (fs[] >> rw[] >> fs[])
                        )
                    )
                 >- (disj2_tac >> fs[OPTION_TO_LIST_MEM] >> qexists_tac `l'`
                     >> fs[] >> qexists_tac `l''` >> fs[]
                     >> `x' = (nId,frml)`
                         by metis_tac[findNode_def,SOME_11]
                     >> rw[] >> fs[] >> rw[] >> qexists_tac `(nId,frml)`
                     >> fs[] >> fs[findNode_def]>> fs[]
                    )
                )
             >- (qunabbrev_tac `addSingleEdge` >> fs[addEdge_def]
                 >> `unique_node_formula m1` by (
                      fs[unique_node_formula_def,graphStatesWithId_def]
                      >> metis_tac[]
                  )
                 >> `?suc. lookup id m1.nodeInfo = SOME suc`
                     by metis_tac[domain_lookup]
                 >> `MEM (LABEL,id) ((LABEL,id)::followers_old)` by fs[]
                 >> `0 < LABEL.edge_grp` by (
                      qunabbrev_tac `LABEL`
                      >> fs[theorem "edgeLabelAA_component_equality"]
                      >> Cases_on `v` >> fs[]
                  )
                 >> `lookup nId m1.followers = SOME ((LABEL,id)::followers_old)`
                    by (fs[gfg_component_equality] >> metis_tac[lookup_insert])
                 >> `?suc. lookup id m1.nodeInfo = SOME suc`
                    by metis_tac[domain_lookup]
                 >> `lookup nId m1.nodeInfo = SOME frml`
                       by metis_tac[findNode_def,MEM_toAList,SOME_11,FIND_LEMM2]
                 >> `∃s.
                     (LABEL.edge_grp,LABEL.pos_lab,LABEL.neg_lab,s) ∈
                     extractTrans m1 (SND y).frml ∧ suc'.frml ∈ s`
                    by metis_tac[EXTR_TRANS_LEMM]
                 >> first_x_assum
                    (qspec_then `(LABEL.edge_grp,LABEL.pos_lab,LABEL.neg_lab,s)`
                       mp_tac)
                 >> simp[] >> qunabbrev_tac `LABEL` >> rpt strip_tac
                 >> fs[theorem "edgeLabelAA_component_equality"]
                )
            )
         >- (`extractTrans m1 a = extractTrans m a` suffices_by metis_tac[]
             >> `findNode (λ(n,l). l.frml = a) m1
              = findNode (λ(n,l). l.frml = a) m` by fs[findNode_def]
            >> Cases_on `findNode (λ(n,l). l.frml = a) m` >> fs[]
            >- (
             `!x b. (findNode (λ(n,l). l.frml = b) x = NONE)
                     ==> (extractTrans x b = {})` by (
                 rpt strip_tac
                 >> `!q. ~ (q ∈ extractTrans x b)`
                   suffices_by metis_tac[MEMBER_NOT_EMPTY]
                 >> simp[extractTrans_def] >> rpt strip_tac
                 >> fs[]
                 >- (disj2_tac >> disj1_tac
                     >> Q.HO_MATCH_ABBREV_TAC `B = {}`
                     >> `!x. ~(x ∈ B)` suffices_by metis_tac[MEMBER_NOT_EMPTY]
                     >> rpt strip_tac >> qunabbrev_tac `B` >> fs[OPTION_TO_LIST_MEM]
                     >> metis_tac[NOT_SOME_NONE]
                    )
                 >- (disj2_tac >> fs[OPTION_TO_LIST_MEM]
                     >> metis_tac[NOT_SOME_NONE])
             )
             >> metis_tac[]
             )
            >- (
             Cases_on `x`
             >> `lookup q m1.followers = lookup q m.followers` by (
                 qunabbrev_tac `addSingleEdge` >> fs[addEdge_def]
                 >> `~(q = nId)` by (
                   fs[findNode_def]
                   >> `(λ(n,l). l.frml = a) (q,r)
                       ∧ MEM (q,r) (toAList m.nodeInfo)`
                      by metis_tac[FIND_LEMM2]
                   >> `(λ(n,l). l.frml = (SND y).frml) (nId,frml)
                       ∧ MEM (nId,frml) (toAList m.nodeInfo)`
                       by metis_tac[FIND_LEMM2]
                   >> CCONTR_TAC >> rw[] >> fs[MEM_toAList]
                   >> metis_tac[]
                 )
                 >> fs[gfg_component_equality] >> metis_tac[lookup_insert]
             )
             >> `!x1 x2 b id n.
                  (findNode (λ(n,l). l.frml = b) x1 = SOME (id,n))
                ∧ (findNode (λ(n,l). l.frml = b) x2 = SOME (id,n))
                ∧ (lookup id x1.followers = lookup id x2.followers)
                ∧ (x1.nodeInfo = x2.nodeInfo)
                ==> (extractTrans x1 b ⊆ extractTrans x2 b)` by (
                 simp[extractTrans_def,SUBSET_DEF] >> rpt strip_tac
             )
             >> metis_tac[SET_EQ_SUBSET]
             )
           )
       )
    )
    >> first_x_assum (qspec_then `t` mp_tac) >> simp[]
    >> `∀lab x.
         MEM (lab,x) (TO_LABELS t) ⇒
         ∃h. MEM (x,h) (toAList g.nodeInfo) ∧ lab = LABEL` by (
        rpt strip_tac >> fs[] >> qunabbrev_tac `TO_LABELS` >> fs[]
        >> fs[MEM_MAP,CAT_OPTIONS_MAP_LEMM,CAT_OPTIONS_MEM] >> rw[]
        >> Cases_on `y'` >> metis_tac[FIND_LEMM2]
    )
    >> simp[] >> rpt strip_tac >> qexists_tac `m` >> qunabbrev_tac `Q`
    >> fs[]
    >> Q.HO_MATCH_ABBREV_TAC `A ∧ B ∧ C`
    >> `A ∧ (A ==> B) ∧ C` suffices_by fs[]
    >> qunabbrev_tac `A` >> qunabbrev_tac `B` >> qunabbrev_tac `C`
    >> fs[] >> rpt strip_tac
    >- simp[graphStatesWithId_def,MEM_MAP]
    >- (fs[unique_node_formula_def] >> metis_tac[])
    >- (first_x_assum (qspec_then `h'` mp_tac) >> fs[]
        >> Cases_on `h' = (SND y).frml` >> fs[] >> rpt strip_tac
        >> qexists_tac `LABEL.edge_grp`
        >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> fs[]
       )
   )
  );

val _ = export_theory ();
