open HolKernel Parse bossLib boolLib gfgTheory listTheory optionTheory pred_setTheory

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
     in { edge | ?label. 0 < label.edge_grp
                 ∧
                 let labelSucs =
                     { suc.frml
                     | ?sucId. MEM (label,sucId) sucs
                        ∧ SOME suc = lookup sucId graph.nodeInfo
                     }
                 in (edge = (label.edge_grp, label.pos_lab,
                             label.neg_lab, labelSucs)) }
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

val ADDEDGE_LEMM = store_thm
  ("ADDEDGE_LEMM",
   ``!g f e aP. wfg g ∧ MEM f (graphStates g)
            ∧ unique_node_formula g
        ==> (?g2. (addEdgeToGraph f e g = SOME g2) ∧ wfg g2
          ∧ (set (graphStatesWithId g) = set (graphStatesWithId g2))
          ∧ (unique_node_formula g2)
          ∧ (!h.
                 if h = f
                 then ?i. extractTrans g2 h
                        = extractTrans g h ∪ { (i, e.pos,e.neg,set e.sucs) }
                 else extractTrans g2 h = extractTrans g h))``,
   rpt strip_tac >> Cases_on `e` >> fs[addEdgeToGraph_def]
   >> fs[graphStates_def,MEM_MAP] (* >> simp[findNode_def] *)
   >> Cases_on `l1` >> fs[] >> rpt strip_tac
   >> `?q. (findNode (λ(n,l). l.frml = (SND y).frml) g = SOME q)
        ∧ ((λ(n,l). l.frml = (SND y).frml) q)` by (
       simp[findNode_def]
       >> qabbrev_tac `P = (λ(n:num,l). l.frml = (SND y).frml)`
       >> `P y` by (qunabbrev_tac `P` >> Cases_on `y` >> fs[])
       >> metis_tac[FIND_LEMM]
   )
   >- (
     Q.HO_MATCH_ABBREV_TAC
       `?g2. (?nodeId. A nodeId ∧ P g2 nodeId) ∧ Q g2`
     >> `?nodeId. A nodeId ∧ ?g2. P g2 nodeId ∧ Q g2` suffices_by metis_tac[]
     >> qunabbrev_tac `A` >> qunabbrev_tac `P` >> fs[]
     >> Cases_on `q` >> fs[] >> rename[`_ = SOME (nId,frml)`]
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
      >- (Cases_on `h = f` >> fs[]
          >- (qexists_tac `0` >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
            >> fs[extractTrans_def]
            >- (
             qexists_tac `label` >> fs[]
             >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
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
             >- (fs[OPTION_TO_LIST_MEM] >> Cases_on `sucId = nId` >> fs[]
                 >> rw[]
              >- (
               `suc = frml` by metis_tac[SOME_11]
               >> qexists_tac `NEW_LAB` >> fs[] >> rpt strip_tac
               >- (qunabbrev_tac `NEW_LAB` >> fs[])
               >- (qexists_tac `nId` >> fs[]
                   >> `lookup nId x.nodeInfo = SOME NEW_LAB` by (
                        fs[updateNode_def,gfg_component_equality]
                        >> metis_tac[lookup_insert]
                    ) >> fs[]
                   >> qexists_tac `l'` >> fs[] >> qexists_tac `(nId,NEW_LAB)`
                   >> fs[] >> rpt strip_tac
                   >> simp[findNode_def]
                   >> `MEM (nId, NEW_LAB) (toAList x.nodeInfo)`
                      by metis_tac[MEM_toAList]
                   >> `(λ(n,l). l.frml = (SND y).frml) (nId,NEW_LAB)` by (
                        qunabbrev_tac `NEW_LAB` >> fs[]
                    )
                   >> `?z. FIND (λ(n,l). l.frml = (SND y).frml)
                                  (toAList x.nodeInfo) = SOME z`
                      by metis_tac[FIND_LEMM]
                   >> `MEM z (toAList x.nodeInfo)
                    ∧ (λ(n,l). l.frml = (SND y).frml) z`
                      by metis_tac[FIND_LEMM2]
                   >> Cases_on `z`
                   >> `MEM (q,r.frml) (graphStatesWithId g)`
                      by (fs[MEM_MAP,graphStatesWithId_def]
                          >> qexists_tac `(q,r)` >> fs[]
                         )
                   >> `MEM (nId,NEW_LAB.frml) (graphStatesWithId g)`
                      by (fs[MEM_MAP,graphStatesWithId_def]
                          >> qexists_tac `(nId,NEW_LAB)` >> fs[]
                         )
                   >> `NEW_LAB.frml = r.frml`
                        by (qunabbrev_tac `NEW_LAB` >> fs[])
                   >> IMP_RES_TAC UNIQUE_NODE_FORM_LEMM2 >> fs[]
                   >> first_x_assum (qspec_then `(nId,r.frml)` mp_tac)
                   >> simp[] >> rpt strip_tac >> rw[]
                   >> metis_tac[MEM_toAList,SOME_11]
                  )
                  )
              >- (

                  )

)

)
)
)

               )
            >- (
             

)

               >> qexists_tac `suc` >> fs[] >> qexists_tac `sucId` >> fs[]
               >> `q' = nId` suffices_by (
                    rpt strip_tac >> rw[] >> fs[]
)


)


            `MEM (sucId,suc) (toAList x.nodeInfo)`
               by metis_tac[MEM_toAList]
             >> qabbrev_tac `h = (λ(id:num,label). (id,label.frml))`
             >> `MEM (h (sucId,suc)) (MAP h (toAList g.nodeInfo))`
               by metis_tac[MEM_MAP,MEM]
             >> fs[MEM_MAP] >> Cases_on `y'` >> qunabbrev_tac `h` >> fs[]
             >> qexists_tac `r` >> fs[] >> qexists_tac `q`
             >> qabbrev_tac `L = λg:(α nodeLabelAA, α edgeLabelAA) gfg.
                                  do
                                  (nId,nodeLabel)
                                      <- findNode (λ(n,l). l.frml
                                                   = (SND y).frml) g;
                                  lookup nId g.followers
                                  od`
              >> `(MEM (label,q) (OPTION_TO_LIST (L g)))
                ∧ (SOME r = (lookup q g.nodeInfo))` suffices_by fs[]
              >> `MEM (label,q) (OPTION_TO_LIST (L x))` by fs[]
              >> Cases_on `L x`
              >- metis_tac[OPTION_TO_LIST_def,MEM]
              >- (
               rename[`L x = SOME l_x`]
               >> `MEM (label,q) l_x` by fs[OPTION_TO_LIST_def]
               >> Cases_on `L g` >> qunabbrev_tac `L` >> fs[findNode_def]
               >- fs[findNode_def]
               >- (`x.followers = g.followers`
                       by metis_tac[updateNode_preserves_edges]
                   >> rename[`_ (toAList g.nodeInfo) = SOME n2`]
                   >> rename[`_ n1 = SOME l_x`,`FIND _ _ = SOME n1`]
                   >> `~((λ(nId,nodeLabel). lookup nId g.followers) n2 = NONE)`
                      suffices_by fs[]
                   >> rw[] >> fs[updateNode_def]
                   >> `MEM n2 (toAList g.nodeInfo)` by metis_tac[FIND_LEMM2]
                   >> fs[wfg_def] >> Cases_on `n2` >> fs[]
                   >> `~(q' ∈ domain g.followers)` by fs[domain_lookup]
                   >> metis_tac[MEM_toAList,domain_lookup]
                  )
               >- (fs[OPTION_TO_LIST_def] >> rw[]
                   >- (rename[`_ (nId,frml) = SOME x1`]
                       >> fs[]
                       >> rename[`(λ(nId,nodeLabel). lookup nId x.followers) x2
                                           = SOME l_x`]
                       >> Cases_on `x2`
             >> `q = q'` by (
                 `(FIND (λ(n,l). l.frml = (SND y).frml) (toAList x.nodeInfo))
                 = (FIND (λ(n,l). l.frml = (SND y).frml) (toAList g.nodeInfo))`
                 by (fs[updateNode_def,FIND_def] >> rw[] >> fs[]
                     >> Induct_on `g.nodeInfo` >> fs[]
                     >- rw[] >> fs[insert_def]

)
)

)
)
)
)

)

   >> Q.HO_MATCH_ABBREV_TAC
       `?x. (?nodeId. A nodeId ∧ P x nodeId) ∧ Q x`
   (* >> Q.HO_MATCH_ABBREV_TAC *)
   (*     `?x. (?nodeId. A nodeId ∧ ?oSP. P oSP x nodeId) ∧ Q x` *)
   >> `?nodeId. A nodeId ∧ ?x. P x nodeId ∧ Q x`
       suffices_by metis_tac[SWAP_EXISTS_THM]
   >> qunabbrev_tac `P` >> qunabbrev_tac `A` >> fs[]
   >> Cases_on `q` >> fs[] >> rename[`_ = SOME (nId,frml)`]
   (* >> qexists_tac `nId` >> rpt strip_tac *)
   (*  >- (qexists_tac `(nId,frml)` >> fs[]) *)
    >- (`nId ∈ domain g.followers` by (
         `nId ∈ domain g.nodeInfo` suffices_by metis_tac[wfg_def]
         >> `MEM (nId, frml) (toAList g.nodeInfo)` by metis_tac[FIND_LEMM2]
         >> fs[MEM_toAList] >> metis_tac[domain_lookup]
       )
       >> fs[domain_lookup]
       >> Q.HO_MATCH_ABBREV_TAC
           `?x. FOLDR addSingleEdge a_init ls = SOME x ∧ Q x`
       >> `!lab x. MEM (lab,x) ls ==> ?h. MEM (x,h) (toAList g.nodeInfo)` by (
         rpt strip_tac >> qunabbrev_tac `ls` >> fs[MEM_MAP]
         >> qabbrev_tac
             `func = λs. (FIND (λ(n,l). l.frml = s) (toAList g.nodeInfo))`
         >> `?a. MEM a l1 ∧ SOME y' = func a` by metis_tac[CAT_OPTIONS_MAP_LEMM]
         >> qunabbrev_tac `func` >> fs[]
         >> `MEM y' (toAList g.nodeInfo)` by metis_tac[FIND_LEMM2]
         >> qexists_tac `SND y'` >> fs[]
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
                   (MAP
                    (λs.
                     (FIND (λ(n,l). l.frml = s) (toAList g.nodeInfo))) l)))`
       >> `ls = TO_LABELS l1` by (qunabbrev_tac `TO_LABELS` >> simp[])
       >> `!qs fs. ((!lab x. MEM (lab,x) qs
                          ==> (?h. MEM (x,h) (toAList g.nodeInfo)
                                ∧ (lab = LABEL)))
                  ∧ (qs = TO_LABELS fs))
             ==> ?m. (FOLDR addSingleEdge a_init qs = SOME m)
                   ∧ (g.nodeInfo = m.nodeInfo)
                   ∧ (wfg m)
                   (* ∧ (?e. ((LABEL.edge_grp,l,l0,e) ∈ extractTrans m frml.frml) *)
                   (*       ∧ (!x. MEM (LABEL, x) qs *)
                   (*           ==> ?node. (lookup x m.nodeInfo = SOME node) *)
                   (*                    ∧ (node.frml ∈ e))) *)
                   ∧ (?i. extractTrans m frml.frml
                            = extractTrans g frml.frml ∪ {(i,l,l0,set fs)})` by (
           Induct_on `qs` >> fs[]
            >- (qunabbrev_tac `a_init` >> simp[extractTrans_def] >> rpt strip_tac
                >- (qexists_tac `LABEL` >> qunabbrev_tac `LABEL` >> fs[])
                >- ()
               )
            >- (rpt strip_tac
                >> `∀lab x. MEM (lab,x) qs
                      ⇒ (∃h. MEM (x,h) (toAList g.nodeInfo) ∧ (lab = LABEL))`
                    by metis_tac[]
                >> `∃m. (FOLDR addSingleEdge a_init qs = SOME m)
                      ∧ (g.nodeInfo = m.nodeInfo)
                      ∧ (wfg m)
                      ∧ (∃e.
                          (LABEL.edge_grp,l,l0,e) ∈ extractTrans m frml.frml
                          ∧ ∀x.
                           MEM (LABEL,x) qs ⇒
                           ∃node. lookup x m.nodeInfo = SOME node
                                ∧ node.frml ∈ e)`
                     by metis_tac[]
                >> `?m2. (addSingleEdge h (SOME m) = SOME m2)
                       ∧ (g.nodeInfo = m2.nodeInfo)
                       ∧ (wfg m2)
                       ∧ (∃e. (LABEL.edge_grp,l,l0,e)
                                ∈ extractTrans m2 (SND y).frml
                             ∧ ∀x.
                               (LABEL,x) = h ∨ MEM (LABEL,x) qs ⇒
                                 ∃node. lookup x m2.nodeInfo = SOME node
                                      ∧ node.frml ∈ e)`
                     suffices_by fs[]
                >> qunabbrev_tac `addSingleEdge` >> Cases_on `h`
                >> simp[]
                >> `?nG. addEdge nId (q,r) m = SOME nG` by (
                     simp[addEdge_def]
                     >> Q.HO_MATCH_ABBREV_TAC `?nG. P ∧ A nG`
                     >> `P ∧ (P ==> ?nG. A nG)` suffices_by fs[]
                     >> qunabbrev_tac `P` >> qunabbrev_tac `A`
                     >> rpt strip_tac
                      >- (`MEM (nId,frml) (toAList g.nodeInfo)`
                             by metis_tac[FIND_LEMM2]
                          >> fs[MEM_toAList,domain_lookup]
                          >> metis_tac[]
                         )
                      >- (`∃h. MEM (r,h) (toAList g.nodeInfo)` by metis_tac[]
                          >> fs[MEM_toAList,domain_lookup]
                          >> metis_tac[]
                         )
                      >- (`nId ∈ domain m.followers` by metis_tac[wfg_def]
                          >> `?fol_o. lookup nId m.followers = SOME fol_o`
                             by metis_tac[domain_lookup]
                          >> fs[]
                         )
                 )
                >> qexists_tac `nG` >> simp[]
                >> `wfg nG` by metis_tac[addEdge_preserves_wfg]
                >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
                >> simp[addEdge_def] >> rpt strip_tac
                >> Cases_on `m` >> fs[gfg_fn_updates]
                >> fs[gfg_component_equality]
                >> `?node. lookup r nG.nodeInfo = SOME node`
                   by metis_tac[domain_lookup]
                >> qexists_tac `e ∪ {node.frml}`
                >> rpt strip_tac
                >- (fs[extractTrans_def]
                    >> qexists_tac `LABEL` >> simp[SET_EQ_SUBSET,SUBSET_DEF]
                    >> rpt strip_tac
                    >- (qunabbrev_tac `LABEL` >> fs[])
                    >- (qunabbrev_tac `LABEL` >> fs[])
                    >- (
                     qexists_tac `suc` >> simp[] >> qexists_tac `sucId`
                     >> simp[]
                     >> Q.HO_MATCH_ABBREV_TAC `
                         MEM (LABEL,sucId) (OPTION_TO_LIST M_L)`
                     >> qabbrev_tac `M_L0 =
                         do node <-
                              findNode (λ(n',l). l.frml = (SND y).frml)
                                       (gfg nG.nodeInfo s0 nG.preds nG.next);
                            lookup node s0
                         od`
                     >> `IS_SOME M_L0`
                           by metis_tac[MEM,OPTION_TO_LIST_def,
                                        NOT_IS_SOME_EQ_NONE]
                     >> `IS_SOME M_L` by (
                         qunabbrev_tac `M_L` >> POP_ASSUM mp_tac
                         >> qunabbrev_tac `M_L0` >> simp[IS_SOME_EXISTS]
                         >> rpt strip_tac >> Cases_on `node' = nId`
                         >- (qexists_tac `((q,r)::followers_old)`
                             >> qexists_tac `nId` >> fs[findNode_def]
                             >> metis_tac[lookup_insert]
                            )
                         >- (qexists_tac `x'` >> qexists_tac `node'`
                             >> fs[findNode_def] >> metis_tac[lookup_insert]
                            )
                     )
                     >> fs[IS_SOME_EXISTS,OPTION_TO_LIST_def]
                     >> `MEM (label',sucId) x'` by metis_tac[OPTION_TO_LIST_def]
                     >> qunabbrev_tac `M_L` >> qunabbrev_tac `M_L0` >> fs[]
                     >> `node' = node''` by (
                          Cases_on `nG` >> fs[findNode_def]
                          >> rw[] >> metis_tac[SOME_11]
                     )
                     >> `LABEL = label'` by (
                         qunabbrev_tac `LABEL`
                         >> fs[theorem "edgeLabelAA_component_equality"]
                     )
                     >> rw[] >> Cases_on `node' = nId` >> fs[]
                     >- (rw[]
                         >> `x'' = (q,r)::followers_old`
                            by metis_tac[lookup_insert,SOME_11]
                         >> metis_tac[MEM]
                        )
                     >- (rw[] >> metis_tac[lookup_insert,SOME_11])
                     )
                    >- (rw[] >> qexists_tac `node` >> simp[] >> qexists_tac `r`
                        >> simp[]
                        >> Q.HO_MATCH_ABBREV_TAC `
                            MEM (LABEL,r) (OPTION_TO_LIST M_L)`
                        >> `IS_SOME M_L` by (
                            simp[IS_SOME_EXISTS] >> qunabbrev_tac `M_L`
                            >> qexists_tac `(q,r)::followers_old` >> fs[]
                            >> qexists_tac `nId` >> fs[findNode_def]
                            >> rpt strip_tac >>  metis_tac[lookup_insert]
                         )
                        >> fs[IS_SOME_EXISTS]
                        >> `MEM (LABEL,r) x` suffices_by
                              metis_tac[OPTION_TO_LIST_def,NOT_IS_SOME_EQ_NONE]
                        >> qunabbrev_tac `M_L` >> fs[findNode_def]
                        >> `node' = nId` by fs[] >> rw[]
                        >> `q = LABEL` by metis_tac[] >> rw[]
                        >> metis_tac[lookup_insert,SOME_11,MEM]
                       )
                    >- (Cases_on `x = node.frml` >> fs[]
                        >> `LABEL = label'` by (
                             qunabbrev_tac `LABEL`
                             >> fs[theorem "edgeLabelAA_component_equality"]
                         )
                        >> rw[] >> qexists_tac `suc` >> fs[]
                        >> qexists_tac `sucId` >> fs[]
                        >> Q.HO_MATCH_ABBREV_TAC `
                              MEM (LABEL,sucId) (OPTION_TO_LIST M_0)`
                        >> qabbrev_tac `
                            M_L =  do
                                     node <- findNode
                                              (λ(n,l). l.frml = (SND y).frml)
                                              nG;
                                     lookup node nG.followers
                                    od`
                        >> `IS_SOME M_L`
                              by metis_tac[MEM,OPTION_TO_LIST_def,
                                           NOT_IS_SOME_EQ_NONE]
                        >> `IS_SOME M_0` by (
                             qunabbrev_tac `M_L` >> POP_ASSUM mp_tac
                             >> qunabbrev_tac `M_0` >> simp[IS_SOME_EXISTS]
                             >> rpt strip_tac >> Cases_on `node' = nId`
                             >- (qexists_tac `followers_old`
                                 >> qexists_tac `nId` >> fs[findNode_def]
                                )
                             >- (qexists_tac `x` >> qexists_tac `node'`
                                 >> fs[findNode_def] >> metis_tac[lookup_insert]
                                )
                         )
                        >> fs[IS_SOME_EXISTS,OPTION_TO_LIST_def]
                        >> `MEM (LABEL,sucId) x` by metis_tac[OPTION_TO_LIST_def]
                        >> qunabbrev_tac `M_L` >> qunabbrev_tac `M_0` >> fs[]
                        >> `node' = node''` by (
                             Cases_on `nG` >> fs[findNode_def]
                             >> rw[] >> metis_tac[SOME_11]
                         )
                        >> rw[]
                        >> Cases_on `node' = nId` >> fs[]
                        >- (rw[]
                            >> `x = (q,r)::followers_old` by metis_tac[lookup_insert,SOME_11]
                            >> `~(sucId = r)` by (
                                `~(node = suc)` suffices_by metis_tac[SOME_11]
                                >> fs[theorem "nodeLabelAA_component_equality"]
                             )
                            >> `~((LABEL,sucId) = (q,r))` by fs[]
                            >> metis_tac[MEM]
                           )
                        >- (rw[] >> metis_tac[lookup_insert,SOME_11])
                       )
                   )
                    >- fs[]
                    >- (fs[] >> metis_tac[])
                   )
               )
       >> `!qs.



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
