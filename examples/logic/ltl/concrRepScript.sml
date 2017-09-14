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

val autoStates_def = Define`
  autoStates (concrAA g i aP) =
    MAP ((\l. l.frml) o SND) (toAList g.nodeInfo)`;

val inAuto_def = Define`
  inAuto aut f = MEM f (autoStates aut)`;

val IN_AUTO_FINITE = store_thm
  ("IN_AUTO_FINITE",
   ``!aut. FINITE (LIST_TO_SET (autoStates aut))``,
   rpt strip_tac >> metis_tac[FINITE_LIST_TO_SET]
  );

val addFrmlToAut_def = Define`
   (addFrmlToAut (concrAA g i aP) (U f1 f2) =
       if inAuto (concrAA g i aP) (U f1 f2)
       then (concrAA g i aP)
       else concrAA (addNode <| frml := (U f1 f2); is_final := T |> g) i aP)
 ∧ (addFrmlToAut (concrAA g i aP) f =
       if inAuto (concrAA g i aP) f
       then (concrAA g i aP)
       else concrAA (addNode <| frml := f; is_final := F |> g) i aP)`;

val addEdgeToAut_def = Define`
  addEdgeToAut f (concrEdge pos neg sucs) (concrAA g i aP) =
    let sucIds = CAT_OPTIONS (MAP (\s. findNode (λ(n,l). l.frml = s) g) sucs)
    in do nodeId <- findNode (λ(n,l). l.frml = f) g;
           oldSucPairs <- lookup nodeId g.followers ;
           oldSucs <- SOME (MAP FST oldSucPairs);
           lstGrpId <- SOME (if oldSucs = [] then 0 else (HD oldSucs).edge_grp) ;
           unfolded_edges <- SOME
             (MAP (\i. (<| edge_grp := lstGrpId + 1;
                          pos_lab := pos ;
                          neg_lab := neg ; |>,i)) sucIds);
           FOLDR (\e a_opt. case a_opt of
                          | NONE => NONE
                          | SOME a =>
                                 do newGraph <- addEdge nodeId e a.graph;
                                    SOME (concrAA newGraph i aP)
                                 od)
                 (SOME (concrAA g i aP)) unfolded_edges
        od`;

val ADDFRML_LEMM = store_thm
  ("ADDFRML_LEMM",
   ``!a f. wfg a.graph ==>
       (set (autoStates a) ⊆ set (autoStates (addFrmlToAut a f))
      ∧ wfg (addFrmlToAut a f).graph)``,
   simp[SUBSET_DEF] >> rpt strip_tac >> Cases_on `inAuto a f`
   >> Cases_on `a`
    >- (Cases_on `f` >> simp[addFrmlToAut_def])
    >- (Cases_on `f` >> simp[addFrmlToAut_def,addNode_def]
        >> `~(g.next ∈ domain g.nodeInfo)` by (
             fs[wfg_def] >> metis_tac[]
         )
        >> fs[autoStates_def,insert_def] >> POP_ASSUM mp_tac
        >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
        >> rw[MEM_MAP] >> qexists_tac `y` >> fs[]
        >> Cases_on `y` >> fs[]
        >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
        >> rw[MEM_toAList] >> Cases_on `q = g.next`
        >> fs[lookup_insert]
        >> (`lookup q g.nodeInfo = NONE` by metis_tac[lookup_NONE_domain]
            >> rw[] >> fs[])
       )
    >- (Cases_on `f` >> simp[addFrmlToAut_def]
        >> fs[wfg_def])
    >- (Cases_on `f` >> simp[addFrmlToAut_def]
        >> fs[])
  );

val ADDFRML_FOLDR_LEMM = store_thm
  ("ADDFRML_FOLDR_LEMM",
   ``!a fs. wfg a.graph ==>
      (set (autoStates a) ⊆
         set (autoStates (FOLDR (\f a. addFrmlToAut a f) a fs))
         ∧ wfg (FOLDR (\f a. addFrmlToAut a f) a fs).graph)``,
   gen_tac >> HO_MATCH_MP_TAC list_induction >> rpt strip_tac
   >> fs[FOLDR]
     >- (`set (autoStates (FOLDR (λf a. addFrmlToAut a f) a fs))
           ⊆ set (autoStates (addFrmlToAut (FOLDR (λf a. addFrmlToAut a f) a fs) h))`
         by metis_tac[ADDFRML_LEMM]
         >> metis_tac[SUBSET_TRANS])
     >- (metis_tac[ADDFRML_LEMM])
  );

val ADDEDGE_LEMM = store_thm
  ("ADDEDGE_LEMM",
   ``!a f e. case addEdgeToAut f e a of
               | SOME newAut => (set (autoStates newAut) = set (autoStates a))
               | NONE => T ``,
   rpt strip_tac >> Cases_on `addEdgeToAut f e a`
   >> fs[] >> Cases_on `e` >> Cases_on `a` >> fs[addEdgeToAut_def]
   >> Induct_on `(MAP
                      (λi.
                           (<|edge_grp :=
                            (if oldSucPairs = [] then 0
                             else (HD (MAP FST oldSucPairs)).edge_grp) + 1;
                            pos_lab := l; neg_lab := l0|>,i))
                      (CAT_OPTIONS
                           (MAP (λs. findNode (λ(n,l). l.frml = s) g) l1)))`
    >> fs[] >> rpt strip_tac
    >> Cases_on `l1` >> fs[CAT_OPTIONS_def]
    >> first_x_assum (qspec_then `oldSucPairs` mp_tac) >> rpt strip_tac
    >> first_x_assum (qspec_then `l` mp_tac) >> rpt strip_tac
    >> first_x_assum (qspec_then `l0` mp_tac) >> rpt strip_tac
    >> first_x_assum (qspec_then `g` mp_tac) >> rpt strip_tac
    >> first_x_assum (qspec_then `t` mp_tac) >> simp[] >> rpt strip_tac
    >> `v = MAP
             (λi.
                  (<|edge_grp :=
                   (if oldSucPairs = [] then 0
                    else (HD (MAP FST oldSucPairs)).edge_grp) + 1;
                   pos_lab := l; neg_lab := l0|>,i))
             (CAT_OPTIONS (MAP (λs. findNode (λ(n,l). l.frml = s) g) t))`
       by (Cases_on `g` >> fs[MAP,CAT_OPTIONS_def]
           >> Cases_on `findNode (λ(n,l). l.frml = h') (gfg s s0 s1 n)`
           >> fs[CAT_OPTIONS_def]


 )

 )





val _ = export_theory ();
