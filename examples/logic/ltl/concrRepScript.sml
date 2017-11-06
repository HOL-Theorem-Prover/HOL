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

val concr2Abstr_edgeLabel_def = Define`
  concr2Abstr_edgeLabel (edgeLabelAA _ pos neg) aP =
     let  pos_part = FOLDL (\s a. s ∩ char (POW aP) a) {} pos
        in FOLDL (\s a. s ∩ char_neg (POW aP) a) pos_part neg`;

val concr2Abstr_trans_def = Define`
  concr2Abstr_trans graph aP s =
     let sucs = OPTION_TO_LIST
                     (OPTION_BIND (findNode (\label. (SND label).frml = s) graph)
                                  (\n. lookup n graph.followers))
     in { edge | ?i x label.
                 let iSucs = { (concr2Abstr_edgeLabel e aP,suc.frml)
                 | ?sucId. MEM (e,sucId) (FILTER ((\j. j = i) o FST) sucs)
                       ∧ SOME suc = lookup sucId graph.nodeInfo}
                 in (x ∈ iSucs) ∧ (label = FST x)
                  ∧ (edge = (label,IMAGE SND iSucs)) }`;

val concr2AbstrAA = Define`
  concr2AbstrAA (concrAA g init prop) =
    ALTER_A
        (concr2Abstr_states g)
        (concr2Abstr_init init g)
        (concr2Abstr_final g)
        (POW (LIST_TO_SET prop))
        (concr2Abstr_trans g (LIST_TO_SET prop))`;

val _ = Datatype`
  concrEdge = <| pos : (α list) ;
                 neg : (α list) ;
                 sucs : (α ltl_frml) list |>`;

val concr2AbstractEdge_def = Define`
  concr2AbstractEdge aP (concrEdge pos neg sucs) =
       (FOLDR (\a sofar. (char (POW aP) a) ∩ sofar)
          (FOLDR (\a sofar. (char_neg (POW aP) a) ∩ sofar) (POW aP) neg) pos
       , set sucs)`;

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

(* val ADDFRML_LEMM2 = store_thm *)
(*   ("ADDFRML_LEMM2", *)
(*    ``!g f. wfg g ==> *)
(*        (set (graphStates g) ⊆ set (graphStates (addFrmlToGraph g f)) *)
(*       ∧ wfg (addFrmlToGraph g f))``, *)
(*    simp[SUBSET_DEF] >> rpt strip_tac >> Cases_on `inAuto a f` *)
(*    >> Cases_on `a` *)
(*     >- (Cases_on `f` >> simp[addFrmlToGraph_def]) *)
(*     >- (Cases_on `f` >> simp[addFrmlToGraph_def,addNode_def] *)
(*         >> `~(g.next ∈ domain g.nodeInfo)` by ( *)
(*              fs[wfg_def] >> metis_tac[] *)
(*          ) *)
(*         >> fs[autoStates_def,insert_def] >> POP_ASSUM mp_tac *)
(*         >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac *)
(*         >> rw[MEM_MAP] >> qexists_tac `y` >> fs[] *)
(*         >> Cases_on `y` >> fs[] *)
(*         >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac *)
(*         >> rw[MEM_toAList] >> Cases_on `q = g.next` *)
(*         >> fs[lookup_insert] *)
(*         >> (`lookup q g.nodeInfo = NONE` by metis_tac[lookup_NONE_domain] *)
(*             >> rw[] >> fs[]) *)
(*        ) *)
(*     >- (Cases_on `f` >> simp[addFrmlToGraph_def] *)
(*         >> fs[wfg_def]) *)
(*     >- (Cases_on `f` >> simp[addFrmlToGraph_def] *)
(*         >> fs[]) *)
(*     >- (Cases_on `f` >> simp[addFrmlToGraph_def] *)
(*         >> fs[]) *)
(*     >- (Cases_on `f` >> simp[addFrmlToGraph_def] *)
(*         >> fs[]) *)
(*   ); *)

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

(* val ADDFRML_FOLDR_LEMM2 = store_thm *)
(*   ("ADDFRML_FOLDR_LEMM2", *)
(*    ``!a fs. wfg a.graph ==> *)
(*        set fs ⊆ set (autoStates (FOLDR (λp g. addFrmlToGraph g p) a fs))``, *)
(*    Induct_on `fs` >> rpt strip_tac >> fs[] >> rpt strip_tac *)
(*     >- metis_tac[ADDFRML_LEMM,inAuto_def] *)
(*     >- (first_x_assum (qspec_then `a` mp_tac) >> simp[] *)
(*         >> `!ls. wfg (FOLDR (λp g. addFrmlToGraph g p) a ls).graph` by ( *)
(*              Induct_on `ls` >> fs[] >> rpt strip_tac *)
(*              >> metis_tac[ADDFRML_LEMM2] *)
(*          ) *)
(*         >> metis_tac[ADDFRML_LEMM2,SUBSET_TRANS] *)
(*        ) *)
(*   ); *)

(* val ADDEDGE_LEMM = store_thm *)
(*   ("ADDEDGE_LEMM", *)
(*    ``!a f e. case addEdgeToGraph f e a of *)
(*                | SOME newAut => (set (autoStates newAut) = set (autoStates a)) *)
(*                | NONE => T ``, *)
(*    rpt strip_tac >> Cases_on `addEdgeToAut f e a` *)
(*    >> fs[] >> Cases_on `e` >> Cases_on `a` >> fs[addEdgeToAut_def] *)
(*    >> rename[`concrAA g init aP`] *)
(*    >> qabbrev_tac `M = (MAP *)
(*                            (λi. *)
(*                                 (<|edge_grp := *)
(*                                  (if oldSucPairs = [] then 0 *)
(*                                   else (HD (MAP FST oldSucPairs)).edge_grp) + 1; *)
(*                                  pos_lab := l; neg_lab := l0|>,i)) *)
(*                            (CAT_OPTIONS *)
(*                                 (MAP (λs. findNode (λ(n,l). l.frml = s) g) l1)))` *)
(*    >> qabbrev_tac `doAddEdge = *)
(*                          (λe a_opt. *)
(*                              do *)
(*                              a <- a_opt; *)
(*                           newGraph <- addEdge nodeId e a.graph; *)
(*                           SOME (concrAA newGraph init aP) *)
(*                                od)` *)
(*    >> `!xs. case FOLDR doAddEdge (SOME (concrAA g init aP)) xs of *)
(*             | NONE => T *)
(*             | SOME a => (set (autoStates a) *)
(*                          = set (autoStates (concrAA g init aP)))` *)
(*       by (Induct_on `xs` >> rpt strip_tac >> fs[] *)
(*           >> Cases_on *)
(*                `doAddEdge h (FOLDR doAddEdge (SOME (concrAA g init aP)) xs)` *)
(*           >> fs[] *)
(*           >> `~(FOLDR doAddEdge (SOME (concrAA g init aP)) xs = NONE)` by ( *)
(*                Cases_on `FOLDR doAddEdge (SOME (concrAA g init aP)) xs` >> fs[] *)
(*                >> qunabbrev_tac `doAddEdge` >> Cases_on `h` >> fs[] *)
(*            ) *)
(*           >> fs[] >> Cases_on `FOLDR doAddEdge (SOME (concrAA g init aP)) xs` *)
(*           >> fs[] >> qunabbrev_tac `doAddEdge` >> Cases_on `h` >> fs[] *)
(*           >> fs[addEdge_def] >> Cases_on `x'` >> simp[autoStates_def] *)
(*           >> fs[] >> Cases_on `x''` >> fs[autoStates_def] *)
(*           >> `g''.nodeInfo = g'.nodeInfo` suffices_by metis_tac[] *)
(*           >> rw[] *)
(*          ) *)
(*    >> first_x_assum (qspec_then `M` mp_tac) >> rpt strip_tac *)
(*    >> Cases_on `FOLDR doAddEdge (SOME (concrAA g init aP)) M` *)
(*    >> fs[] >> rw[] *)
(*   ); *)

val ADDEDGE_LEMM = store_thm
  ("ADDEDGE_LEMM",
   ``!g f e. wfg g ∧ MEM f (graphStates g)
        ==> (?g2. (addEdgeToGraph f e g = SOME g2) ∧ wfg g2
          ∧ (g.nodeInfo = g2.nodeInfo))``,
   rpt strip_tac >> Cases_on `e` >> fs[addEdgeToGraph_def]
   >> fs[graphStates_def,MEM_MAP] >> simp[findNode_def]
   >> Q.HO_MATCH_ABBREV_TAC
       `?x. (?nodeId. A nodeId ∧ ?oSP. P oSP x nodeId) ∧ Q x`
   >> `?nodeId. A nodeId ∧ ?oSP x. P oSP x nodeId ∧ Q x`
       suffices_by metis_tac[SWAP_EXISTS_THM]
   >> qunabbrev_tac `P` >> qunabbrev_tac `A` >> fs[]
   >> `?q. (FIND (λ(n,l). l.frml = (SND y).frml) (toAList g.nodeInfo) = SOME q)
         ∧ ((λ(n,l). l.frml = (SND y).frml) q)` by (
       qabbrev_tac `P = (λ(n:num,l). l.frml = (SND y).frml)`
       >> `P y` by (qunabbrev_tac `P` >> Cases_on `y` >> fs[])
       >> metis_tac[FIND_LEMM]
   )
   >> Cases_on `q` >> rename[`_ = SOME (nId,frml)`]
   >> qexists_tac `nId` >> rpt strip_tac
    >- (qexists_tac `(nId,frml)` >> fs[])
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
             `func = λs.
                         OPTION_MAP FST
                         (FIND (λ(n,l). l.frml = s) (toAList g.nodeInfo))`
         >> `?a. MEM a l1 ∧ SOME x = func a` by metis_tac[CAT_OPTIONS_MAP_LEMM]
         >> qunabbrev_tac `func` >> fs[]
         >> `MEM z (toAList g.nodeInfo)` by metis_tac[FIND_LEMM2]
         >> qexists_tac `SND z` >> fs[]
       )
       >> `!qs. (!lab x. MEM (lab,x) qs ==> ?h. MEM (x,h) (toAList g.nodeInfo))
             ==> ?m. (FOLDR addSingleEdge a_init qs = SOME m)
                   ∧ (g.nodeInfo = m.nodeInfo)
                   ∧ (wfg m)` by (
           Induct_on `qs` >> fs[]
            >- (qunabbrev_tac `a_init` >> simp[])
            >- (rpt strip_tac
                >> `∀lab x. MEM (lab,x) qs ⇒ ∃h. MEM (x,h) (toAList g.nodeInfo)`
                    by metis_tac[]
                >> `∃m. (FOLDR addSingleEdge a_init qs = SOME m)
                      ∧ (g.nodeInfo = m.nodeInfo)
                      ∧ (wfg m)` by metis_tac[]
                >> `?m2. (addSingleEdge h (SOME m) = SOME m2)
                       ∧ (g.nodeInfo = m2.nodeInfo)
                       ∧ (wfg m2)` suffices_by fs[]
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
                          >> fs[MEM_toAList,domain_lookup])
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
               )
       )
       >> qunabbrev_tac `Q` >> metis_tac[]
       )
  );

val _ = export_theory ();
