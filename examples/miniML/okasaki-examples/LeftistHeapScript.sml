open bossLib Theory Parse boolTheory pairTheory Defn Tactic boolLib bagTheory
open relationTheory bagLib lcsymtacs;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;

val _ = new_theory "LeftistHeap"

val _ = Hol_datatype `
heaps = Empty | Node of num => 'a => heaps => heaps`;

val leftist_heap_to_bag_def = Define `
(leftist_heap_to_bag Empty = {||}) ∧
(leftist_heap_to_bag (Node _ x h1 h2) =
  BAG_INSERT x (BAG_UNION (leftist_heap_to_bag h1) (leftist_heap_to_bag h2)))`;

val leftist_heap_ok_def = Define `
(leftist_heap_ok leq Empty = T) ∧
(leftist_heap_ok leq (Node _ x h1 h2) = 
  leftist_heap_ok leq h1 ∧
  leftist_heap_ok leq h2 ∧
  (* OTHER STUFF *)
  T)`;

val rank_def = Define `
(rank Empty = 0) ∧
(rank (Node r _ _ _) = r)`;

val make_node_def = Define `
make_node x a b =
  if rank a >= rank b then 
    Node (rank b + 1) x a b
  else 
    Node (rank a + 1) x b a`;

val _ = Define `
empty = Empty`;

val is_empty = Define `
(is_empty Empty = T) ∧
(is_empty _ = F)`;

val merge_def = Define `
(merge leq h1 Empty = h1) ∧
(merge leq Empty h2 = h2) ∧
(merge leq (Node n1 x a1 b1) (Node n2 y a2 b2) =
  if leq x y then
    make_node x a1 (merge leq b1 (Node n2 y a2 b2))
  else 
    make_node y a2 (merge leq (Node n1 x a1 b1) b2))`;

val insert_def = Define `
insert leq x h = merge leq (Node 1 x Empty Empty) h`;

val find_min_def = Define `
find_min (Node _ x _ _) = x`;
  
val delete_min_def = Define `
delete_min leq _ x a b = merge leq a b`;

val _ = export_theory ();
