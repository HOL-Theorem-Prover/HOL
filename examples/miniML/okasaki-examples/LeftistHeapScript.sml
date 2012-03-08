open bossLib Theory Parse boolTheory pairTheory Defn Tactic boolLib bagTheory
open relationTheory bagLib miscTheory lcsymtacs;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;

val _ = new_theory "LeftistHeap"

val _ = Hol_datatype `
heap = Empty | Node of num => 'a => heap => heap`;

val leftist_heap_to_bag_def = Define `
(leftist_heap_to_bag Empty = {||}) ∧
(leftist_heap_to_bag (Node _ x h1 h2) =
  BAG_INSERT x (BAG_UNION (leftist_heap_to_bag h1) (leftist_heap_to_bag h2)))`;

val rank_def = Define `
(rank Empty = 0) ∧
(rank (Node r _ _ _) = r)`;

val leftist_heap_ok_def = Define `
(leftist_heap_ok leq Empty = T) ∧
(leftist_heap_ok leq (Node _ x h1 h2) =
  leftist_heap_ok leq h1 ∧
  leftist_heap_ok leq h2 ∧
  BAG_EVERY (\y. leq x y) (leftist_heap_to_bag h1) ∧
  BAG_EVERY (\y. leq x y) (leftist_heap_to_bag h2) ∧
  rank h1 ≥ rank h2)`;

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
(merge leq h Empty = h) ∧
(merge leq Empty h = h) ∧
(merge leq (Node n1 x a1 b1) (Node n2 y a2 b2) =
  if leq x y then
    make_node x a1 (merge leq b1 (Node n2 y a2 b2))
  else
    make_node y a2 (merge leq (Node n1 x a1 b1) b2))`;

val merge_ind = fetch "-" "merge_ind"

val insert_def = Define `
insert leq x h = merge leq (Node 1 x Empty Empty) h`;

val find_min_def = Define `
find_min (Node _ x _ _) = x`;

val delete_min_def = Define `
delete_min leq (Node _ x a b) = merge leq a b`;

val leftist_heap_merge_bag = Q.store_thm ("leftist_heap_merge_bag",
`!leq h1 h2.
  leftist_heap_to_bag (merge leq h1 h2) =
  BAG_UNION (leftist_heap_to_bag h1) (leftist_heap_to_bag h2)`,
HO_MATCH_MP_TAC merge_ind >>
srw_tac [BAG_ss]
        [merge_def, leftist_heap_to_bag_def, make_node_def, BAG_INSERT_UNION]);

val leftist_heap_merge_ok = Q.store_thm ("leftist_heap_merge_ok",
`!leq h1 h2.
  WeakLinearOrder leq ∧ leftist_heap_ok leq h1 ∧ leftist_heap_ok leq h2
  ⇒
  leftist_heap_ok leq (merge leq h1 h2)`,
HO_MATCH_MP_TAC merge_ind >>
rw [merge_def, leftist_heap_ok_def, make_node_def, leftist_heap_merge_bag] >>
rw [leftist_heap_to_bag_def] >|
[metis_tac [BAG_EVERY, WeakLinearOrder, WeakOrder, transitive_def],
 metis_tac [BAG_EVERY, WeakLinearOrder, WeakOrder, transitive_def],
 metis_tac [BAG_EVERY, WeakLinearOrder, WeakOrder, transitive_def],
 metis_tac [BAG_EVERY, WeakLinearOrder, WeakOrder, transitive_def],
 decide_tac,
 metis_tac [BAG_EVERY, WeakLinearOrder, WeakOrder, transitive_def,
            WeakLinearOrder_neg],
 metis_tac [BAG_EVERY, WeakLinearOrder, WeakOrder, transitive_def,
            WeakLinearOrder_neg],
 metis_tac [BAG_EVERY, WeakLinearOrder, WeakOrder, transitive_def,
            WeakLinearOrder_neg],
 metis_tac [BAG_EVERY, WeakLinearOrder, WeakOrder, transitive_def,
            WeakLinearOrder_neg],
 metis_tac [BAG_EVERY, WeakLinearOrder, WeakOrder, transitive_def,
            WeakLinearOrder_neg],
 metis_tac [BAG_EVERY, WeakLinearOrder, WeakOrder, transitive_def,
            WeakLinearOrder_neg],
 decide_tac]);

val leftist_heap_find_min_thm = Q.store_thm ("leftist_heap_find_min_thm",
`!h leq. WeakLinearOrder leq ∧ (h ≠ Empty) ∧ leftist_heap_ok leq h ⇒
  BAG_IN (find_min h) (leftist_heap_to_bag h) ∧
  (!y. BAG_IN y (leftist_heap_to_bag h) ⇒ leq (find_min h) y)`,
rw [] >>
cases_on `h` >>
fs [find_min_def, leftist_heap_to_bag_def, leftist_heap_ok_def] >>
fs [BAG_EVERY] >>
metis_tac [WeakLinearOrder, WeakOrder, reflexive_def]);

val leftist_heap_delete_min_thm = Q.store_thm ("leftist_heap_delete_min_thm",
`!h leq.
  WeakLinearOrder leq ∧
  (h ≠ Empty) ∧
  leftist_heap_ok leq h
  ⇒
  leftist_heap_ok leq (delete_min leq h) ∧
  (leftist_heap_to_bag (delete_min leq h) =
   BAG_DIFF (leftist_heap_to_bag h) (EL_BAG (find_min h)))`,
rw [] >>
cases_on `h` >>
fs [delete_min_def, leftist_heap_ok_def, leftist_heap_merge_bag] >-
metis_tac [leftist_heap_merge_ok] >>
rw [leftist_heap_to_bag_def, find_min_def, BAG_DIFF_INSERT2]);

val _ = export_theory ();
