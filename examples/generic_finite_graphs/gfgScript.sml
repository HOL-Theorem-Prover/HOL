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

Definition wfg_def:
  wfg g ⇔ (∀n. g.next ≤ n ⇒ n ∉ domain g.nodeInfo) ∧
           (domain g.followers = domain g.nodeInfo) ∧
           (domain g.preds = domain g.nodeInfo) ∧
           wf g.nodeInfo ∧ wf g.followers ∧ wf g.preds ∧
           wfAdjacency g.followers ∧ wfAdjacency g.preds
End

Theorem empty_is_wfg[simp]:
  wfg empty
Proof
  simp[empty_def,wfg_def,wfAdjacency_def] >> rpt strip_tac >> fs[lookup_def]
QED

Theorem addNode_preserves_wfg[simp]:
  wfg g ⇒ wfg (addNode i g)
Proof
  simp[wfg_def, addNode_def, sptreeTheory.wf_insert] >>
  dsimp[wfAdjacency_def, lookup_insert, AllCaseEqs()] >> metis_tac[]
QED

Theorem addEdge_preserves_wfg:
  wfg g ∧ (addEdge i (e,s) g = SOME g2) ==> wfg g2
Proof
  simp[wfg_def,addEdge_def] >>
  dsimp[wfAdjacency_def, lookup_insert] >> rpt strip_tac >> rw[] >>
  fs[sptreeTheory.wf_insert] >>
  drule_then strip_assume_tac (SRULE [PULL_EXISTS] $ iffRL domain_lookup) >>
  simp[ABSORPTION_RWT]
  >- metis_tac[]
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

Theorem updateNode_preserves_wfg[simp]:
  wfg g ∧ (updateNode id n g = SOME g2) ==> wfg g2
Proof
   simp[wfg_def,updateNode_def] >> rw[] >> simp[] >>
   gs[ABSORPTION_RWT, wf_insert] >> metis_tac[]
QED

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

Definition removeEdges_on_def:
  removeEdges_on n g =
  if n ∈ domain g.nodeInfo then
  g with <|
      followers updated_by (insert n [] o map (FILTER (λei. SND ei ≠ n))) ;
      preds updated_by (insert n [] o map (FILTER (λei. SND ei ≠ n))) ;
    |>
  else g
End

Theorem removeEdges_on_preserves_wfg:
  wfg g ⇒ wfg (removeEdges_on n g)
Proof
  rw[wfg_def, removeEdges_on_def, sptreeTheory.domain_map,
     pred_setTheory.ABSORPTION_RWT, wf_insert] >>
  gs[wfAdjacency_def, sptreeTheory.domain_map] >>
  rw[sptreeTheory.lookup_insert] >>
  gs[sptreeTheory.lookup_map, listTheory.MEM_FILTER] >> metis_tac[]
QED

Theorem removeEdges_on_next[simp]:
  (removeEdges_on n g).next = g.next
Proof
  rw[removeEdges_on_def]
QED

Theorem domain_removeEdges_on:
  wfg g ⇒
  domain (removeEdges_on n g).nodeInfo = domain g.nodeInfo ∧
  domain (removeEdges_on n g).followers = domain g.followers ∧
  domain (removeEdges_on n g).preds = domain g.preds
Proof
  rw[removeEdges_on_def, sptreeTheory.domain_map, pred_setTheory.ABSORPTION_RWT,
     wfg_def]
QED

Definition deleteNode_def:
  deleteNode n g = removeEdges_on n g with <|
                                    nodeInfo updated_by (delete n) ;
                                    followers updated_by (delete n) ;
                                    preds updated_by (delete n)
                                  |>
End

Theorem deleteNode_preserves_wfg:
  wfg g ⇒ wfg (deleteNode n g)
Proof
  rw[deleteNode_def] >>
  rw[wfg_def, domain_removeEdges_on] >>
  gvs[wfg_def, wfAdjacency_def, sptreeTheory.lookup_delete,
      removeEdges_on_def, wf_delete] >>
  rw[] >>
  gs[lookup_insert, lookup_map, wf_delete, wf_insert, domain_map, MEM_FILTER] >>
  metis_tac[]
QED

Definition addNodeN_def:
  addNodeN n i g =
  if n ∈ domain g.nodeInfo then g with nodeInfo updated_by (insert n i)
  else g with <| nodeInfo updated_by (insert n i);
                 preds updated_by (insert n []) ;
                 followers updated_by (insert n []);
                 next := MAX g.next (n + 1) |>
End

Theorem addNodeN_preserves_wfg:
  wfg g ⇒ wfg (addNodeN n i g)
Proof
  rw[wfg_def, addNodeN_def, ABSORPTION_RWT, wf_insert] >>
  gs[wfAdjacency_def, sptreeTheory.lookup_insert, AllCaseEqs(),
     ABSORPTION_RWT, SF DNF_ss] >> metis_tac[]
QED

Theorem nodes_addNodeN[simp]:
  domain (addNodeN n i g).nodeInfo = n INSERT domain g.nodeInfo
Proof
  rw[addNodeN_def, pred_setTheory.ABSORPTION_RWT]
QED

val _ = export_theory();
