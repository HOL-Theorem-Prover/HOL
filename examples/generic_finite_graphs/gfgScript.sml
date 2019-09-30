open HolKernel Parse boolLib bossLib listTheory pred_setTheory;

open sptreeTheory arithmeticTheory;

val _ = new_theory "gfg";

val _ = ParseExtras.tight_equality()
val _ = monadsyntax.temp_add_monadsyntax();
val _ = overload_on("monad_bind",``OPTION_BIND``);

val _ = Datatype‘
  gfg = <| nodeInfo : α spt ;
           followers : (ε # num) list spt ;
           preds : (ε # num) list spt ;
           next : num
        |>’;

val empty_def = Define‘
  empty = <| nodeInfo := LN ; followers := LN ; preds := LN; next := 0|>’;

val addNode_def = Define‘
  addNode i g = g with <| nodeInfo updated_by (insert g.next i) ;
                          next updated_by SUC ;
                          followers updated_by (insert g.next []) ;
                          preds updated_by (insert g.next []) ; |>’;

val addEdge_def = Define`
  addEdge src (e,tgt) g =
     if src ∈ domain g.nodeInfo ∧ tgt ∈ domain g.nodeInfo then
       do
         followers_old <- lookup src g.followers;
         preds_old <- lookup tgt g.preds;
         SOME (g with <|
                  followers updated_by (insert src ((e,tgt)::followers_old)) ;
                  preds updated_by (insert tgt ((e,src)::preds_old))
               |>)
       od
     else NONE`;

val findNode_def = Define`
  findNode P g =
    FIND P (toAList g.nodeInfo)`;

val updateNode_def = Define`
  updateNode nId node g =
    if nId ∈ domain g.nodeInfo
    then SOME (g with  <| nodeInfo updated_by (insert nId node) ;
                         next := g.next ;
                         followers := g.followers ;
                         preds := g.preds ; |>)
    else NONE`;

val wfAdjacency_def = Define‘
  wfAdjacency adjmap ⇔
     ∀k nl e n. lookup k adjmap = SOME nl ∧ MEM (e,n) nl ⇒
                n ∈ domain adjmap’;

val wfg_def = Define‘
  wfg g ⇔ (∀n. g.next ≤ n ⇒ n ∉ domain g.nodeInfo) ∧
           (domain g.followers = domain g.nodeInfo) ∧
           (domain g.preds = domain g.nodeInfo) ∧
           wfAdjacency g.followers ∧ wfAdjacency g.preds’;

val empty_is_wfg = Q.store_thm(
  "empty_is_wfg[simp]",
  `wfg empty`,
  simp[empty_def,wfg_def,wfAdjacency_def] >> rpt strip_tac
  >> fs[lookup_def]
    );

val cond_eq = Q.prove(
  ‘((if P then t else e) = v) ⇔ P ∧ t = v ∨ ¬P ∧ e = v’,
  rw[]);

val addNode_preserves_wfg = Q.store_thm(
  "addNode_preserves_wfg[simp]",
  ‘wfg g ⇒ wfg (addNode i g)’,
  simp[wfg_def, addNode_def] >>
  dsimp[wfAdjacency_def, lookup_insert, cond_eq] >> metis_tac[]);

Theorem addEdge_preserves_wfg:
  wfg g ∧ (addEdge i (e,s) g = SOME g2) ==> wfg g2
Proof
  simp[wfg_def,addEdge_def] >>
  dsimp[wfAdjacency_def, lookup_insert] >> rpt strip_tac >> rw[] >> fs[]
  >- metis_tac[]
  >- (fs[INSERT_DEF,SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> metis_tac[])
  >- (fs[INSERT_DEF,SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> metis_tac[])
  >- (rename[`lookup k (insert i _ _) = SOME nl`, `MEM (e',n) nl`,
             ‘i ∈ domain _’] >>
      fs[lookup_insert] >> Cases_on `k=i` >> fs[] >>
      Cases_on `MEM (e',n) followers_old` >> rw[] >> fs[MEM] >> metis_tac[])
  >- (rename[`lookup k1 (insert k2 _ _) = SOME nl`, `MEM (e',n) nl`,
             ‘k2 ∈ domain _’] >>
      fs[lookup_insert] >> Cases_on `k1=k2` >> fs[] >>
      Cases_on `MEM (e',n) preds_old` >> rw[] >> fs[MEM] >>
      metis_tac[])
QED

val addEdge_preserves_nodeInfo = Q.store_thm(
   "addEdge_preserves_nodeInfo",
   `(addEdge i (e,s) g) = SOME g2 ==> (g.nodeInfo = g2.nodeInfo)`,
   rpt strip_tac >> fs[addEdge_def,theorem "gfg_component_equality"]
    );

val updateNode_preserves_wfg = Q.store_thm(
   "updateNode_preserves_wfg[simp]",
   `wfg g ∧ (updateNode id n g = SOME g2) ==> wfg g2`,
   simp[wfg_def,updateNode_def]
   >> dsimp[wfAdjacency_def, lookup_insert]
   >> rw[] >> fs[INSERT_DEF,SET_EQ_SUBSET,SUBSET_DEF]
   >> rpt strip_tac >> metis_tac[]
    );

val updateNode_preserves_edges = Q.store_thm(
    "updateNode_preserves_edges",
    `updateNode id n g = SOME g2
       ==> (g.followers = g2.followers)
         ∧ (g.preds = g2.preds)`,
    simp[updateNode_def] >> rpt strip_tac
    >> fs[theorem "gfg_component_equality"]
    );

val updateNode_preserves_domain = Q.store_thm(
  "updateNode_preserves_domain",
  `updateNode id n g = SOME g2 ==> (domain g.nodeInfo = domain g2.nodeInfo)`,
   simp[updateNode_def] >> rpt strip_tac >> fs[theorem "gfg_component_equality"]
   >> `domain g2.nodeInfo = id INSERT (domain g.nodeInfo)`
      by metis_tac[domain_insert]
   >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> metis_tac[IN_INSERT]
    );

val graph_size_def = Define‘graph_size g = sptree$size g.nodeInfo’;

val graph_size_addNode = Q.store_thm(
  "graph_size_addNode[simp]",
  ‘wfg g ⇒ graph_size (addNode i g) = graph_size g + 1’,
  simp[graph_size_def, addNode_def, size_insert, wfg_def]);

val _ = export_theory();
