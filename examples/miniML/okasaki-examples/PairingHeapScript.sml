open bossLib Theory Parse boolTheory pairTheory Defn Tactic boolLib bagTheory
open relationTheory bagLib miscTheory lcsymtacs;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;

val _ = new_theory "PairingHeap"

val _ = Hol_datatype `
heap = Empty | Node of 'a => heap list`;

val pairing_heap_to_bag_def = Define `
(pairing_heap_to_bag Empty = {||}) ∧
(pairing_heap_to_bag (Node x hs) =
  BAG_INSERT x (pairing_heaps_to_bag hs)) ∧

(pairing_heaps_to_bag [] = {||}) ∧
(pairing_heaps_to_bag (h::hs) = 
  BAG_UNION (pairing_heap_to_bag h) (pairing_heaps_to_bag hs))`;

val pairing_heap_ok_def = tDefine "pairing_heap_ok" `
(pairing_heap_ok leq Empty = T) ∧
(pairing_heap_ok leq (Node x hs) = 
  EVERY (pairing_heap_ok leq) hs ∧
  BAG_EVERY (\y. leq x y) (pairing_heaps_to_bag hs))`
(wf_rel_tac `measure (\(_,h). (heap_size (\x.1) h))` >>
rw [] >>
induct_on `hs` >>
rw [fetch "-" "heap_size_def"] >>
fs [] >>
decide_tac);

val _ = Define `
empty = Empty`;

val is_empty = Define `
(is_empty Empty = T) ∧
(is_empty _ = F)`;

val merge_def = Define `
(merge leq h Empty = h) ∧
(merge leq Empty h = h) ∧
(merge leq (Node x hs1) (Node y hs2) =
  if leq x y then
    Node x (Node y hs2 :: hs1)
  else 
    Node y (Node x hs1 :: hs2))`;

val merge_ind = fetch "-" "merge_ind"

val insert_def = Define `
insert leq x h = merge leq (Node x []) h`;

val merge_pairs_def = Define `
(merge_pairs leq [] = Empty) ∧
(merge_pairs leq [h] = h) ∧
(merge_pairs leq (h1::h2::hs) = 
  merge leq (merge leq h1 h2) (merge_pairs leq hs))`;

val merge_pairs_ind = fetch "-" "merge_pairs_ind"

val find_min_def = Define `
find_min (Node x _) = x`;

val delete_min_def = Define `
delete_min leq (Node x hs) = merge_pairs leq hs`;

val pairing_heap_merge_bag = Q.store_thm ("pairing_heap_merge_bag",
`!leq h1 h2.
  pairing_heap_to_bag (merge leq h1 h2) = 
  BAG_UNION (pairing_heap_to_bag h1) (pairing_heap_to_bag h2)`,
HO_MATCH_MP_TAC merge_ind >>
srw_tac [BAG_AC_ss] [merge_def, pairing_heap_to_bag_def, BAG_INSERT_UNION]);

val pairing_heap_merge_ok = Q.store_thm ("pairing_heap_merge_ok",
`!leq h1 h2. 
  WeakLinearOrder leq ∧ pairing_heap_ok leq h1 ∧ pairing_heap_ok leq h2 
  ⇒ 
  pairing_heap_ok leq (merge leq h1 h2)`,
HO_MATCH_MP_TAC merge_ind >>
rw [merge_def, pairing_heap_ok_def, pairing_heap_to_bag_def] >>
metis_tac [BAG_EVERY, WeakLinearOrder, WeakOrder, transitive_def,
           WeakLinearOrder_neg]);

val pairing_heap_insert_bag = Q.store_thm ("pairing_heap_insert_bag",
`!h leq x.
  pairing_heap_to_bag (insert leq x h) =
  BAG_INSERT x (pairing_heap_to_bag h)`,
rw [insert_def, pairing_heap_merge_bag, pairing_heap_to_bag_def,
    BAG_INSERT_UNION]);

val pairing_heap_insert_ok = Q.store_thm ("pairing_heap_insert_ok",
`!leq x h. 
  WeakLinearOrder leq ∧ pairing_heap_ok leq h 
  ⇒ 
  pairing_heap_ok leq (insert leq x h)`,
rw [insert_def] >>
`pairing_heap_ok leq (Node x [])` 
         by rw [pairing_heap_ok_def, pairing_heap_to_bag_def] >>
metis_tac [pairing_heap_merge_ok]);

val pairing_heap_find_min_thm = Q.store_thm ("pairing_heap_find_min_thm",
`!h leq. WeakLinearOrder leq ∧ (h ≠ Empty) ∧ pairing_heap_ok leq h ⇒
  BAG_IN (find_min h) (pairing_heap_to_bag h) ∧
  (!y. BAG_IN y (pairing_heap_to_bag h) ⇒ leq (find_min h) y)`,
rw [] >>
cases_on `h` >>
fs [find_min_def, pairing_heap_to_bag_def, pairing_heap_ok_def] >>
fs [BAG_EVERY] >>
metis_tac [WeakLinearOrder, WeakOrder, reflexive_def]);

val pairing_heap_merge_pairs_bag = Q.prove (
`!leq hs. pairing_heap_to_bag (merge_pairs leq hs) = pairing_heaps_to_bag hs`,
recInduct merge_pairs_ind >>
srw_tac [BAG_ss]
        [merge_pairs_def, pairing_heap_to_bag_def, pairing_heap_merge_bag]);

val pairing_heap_merge_pairs_ok = Q.prove (
`!leq hs.
  WeakLinearOrder leq ∧ EVERY (pairing_heap_ok leq) hs
  ⇒ 
  pairing_heap_ok leq (merge_pairs leq hs)`,
recInduct merge_pairs_ind >>
rw [merge_pairs_def, pairing_heap_ok_def, pairing_heap_merge_ok]);

val pairing_heap_delete_min_thm = Q.store_thm ("pairing_heap_delete_min_thm",
`!h leq. 
  WeakLinearOrder leq ∧
  (h ≠ Empty) ∧ 
  pairing_heap_ok leq h 
  ⇒ 
  pairing_heap_ok leq (delete_min leq h) ∧
  (pairing_heap_to_bag (delete_min leq h) = 
   BAG_DIFF (pairing_heap_to_bag h) (EL_BAG (find_min h)))`,
rw [] >>
cases_on `h` >>
fs [delete_min_def, pairing_heap_ok_def, pairing_heap_merge_pairs_bag] >-
metis_tac [pairing_heap_merge_pairs_ok] >>
rw [pairing_heap_to_bag_def, find_min_def, BAG_DIFF_INSERT2]);

val _ = export_theory ()
