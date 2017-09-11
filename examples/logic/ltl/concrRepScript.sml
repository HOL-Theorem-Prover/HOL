open HolKernel Parse bossLib boolLib gfgTheory listTheory

open alterATheory sptreeTheory ltlTheory

val _ = Datatype`
  concrAA = <| graph : (α ltl_frml, (num # (α set) set)) gfg ;
               init : (num # α ltl_frml) list ;
               final : (α ltl_frml) list ;
               atomicProp : α list
            |>`;

val concr2AbstrAA = Define`
  concr2AbstrAA (concrAA g init final prop) =
    ALTER_A
        { x | SOME x ∈ (IMAGE (\n. lookup n g.nodeInfo) (domain g.nodeInfo))}
        {initialSet |
           ?i. initialSet = LIST_TO_SET
                                (MAP SND (FILTER ((\j. j = i) o FST) init))}
        (LIST_TO_SET final)
        (POW (LIST_TO_SET prop))
        (\s. let nodeId_op = getNodeIdByLabel s g
                 and sucs_op = lookup nodeId g.followers
             in { edge |
                  ?i. edge = LIST_TO_SET
                                 (MAP
                                 (SND o FST)
                                 (FILTER ((\j. j = i) o FST o FST) sucs)) })`;

