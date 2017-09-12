open HolKernel Parse bossLib boolLib gfgTheory listTheory optionTheory

open alterATheory sptreeTheory ltlTheory generalHelpersTheory

val _ = new_theory "concrRep";

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

val inAuto_def = Define`
  inAuto (concrAA g i aP) f =
        IS_SOME (findNode (\label. (SND label).frml = f) g)`;

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
    in let nodeId = THE (findNode (λ(n,l). l.frml = f) g)
    in let oldSucs = MAP FST (THE (lookup nodeId g.followers))
    in let lstGrpId = (if oldSucs = [] then 0 else (HD oldSucs).edge_grp)
    in let unfolded_edges =
             MAP (\i. (<| edge_grp := lstGrpId + 1;
                          pos_lab := pos ;
                          neg_lab := neg ; |>,i)) sucIds
    in FOLDL (\a e. concrAA (addEdge nodeId e a.graph) i aP)
             (concrAA g i aP) unfolded_edges`;




val _ = export_theory ();
