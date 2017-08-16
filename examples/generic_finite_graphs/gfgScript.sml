open HolKernel Parse boolLib bossLib;

open sptreeTheory arithmeticTheory

val _ = new_theory "gfg";

val _ = ParseExtras.tight_equality()

val _ = Datatype‘
  gfg = <| nodeInfo : 'a spt ;
           followers : ('e # num) list spt ;
           preds : ('e # num) list spt ;
           next : num
        |>’;

val empty_def = Define‘
  empty = <| nodeInfo := LN ; followers := LN ; preds := LN; next := 0|>’;

val addNode_def = Define‘
  addNode i g = g with <| nodeInfo updated_by (insert g.next i) ;
                          next updated_by SUC ;
                          followers updated_by (insert g.next []) ;
                          preds updated_by (insert g.next []) ; |>’;

val wfAdjacency_def = Define‘
  wfAdjacency adjmap ⇔
     ∀k nl e n. lookup k adjmap = SOME nl ∧ MEM (e,n) nl ⇒
                n ∈ domain adjmap’;


val wfg_def = Define‘
  wfg g ⇔ (∀n. g.next ≤ n ⇒ n ∉ domain g.nodeInfo) ∧
           (domain g.followers = domain g.nodeInfo) ∧
           (domain g.preds = domain g.nodeInfo) ∧
           wfAdjacency g.followers ∧ wfAdjacency g.preds’;

val cond_eq = Q.prove(
  ‘((if P then t else e) = v) ⇔ P ∧ t = v ∨ ¬P ∧ e = v’,
  rw[]);

val addNode_preserves_wfg = Q.store_thm(
  "addNode_preserves_wfg[simp]",
  ‘wfg g ⇒ wfg (addNode i g)’,
  simp[wfg_def, addNode_def] >>
  dsimp[wfAdjacency_def, lookup_insert, cond_eq] >> metis_tac[]);

val graph_size_def = Define‘graph_size g = sptree$size g.nodeInfo’;

val graph_size_addNode = Q.store_thm(
  "graph_size_addNode[simp]",
  ‘wfg g ⇒ graph_size (addNode i g) = graph_size g + 1’,
  simp[graph_size_def, addNode_def, size_insert, wfg_def]);

val _ = export_theory();
