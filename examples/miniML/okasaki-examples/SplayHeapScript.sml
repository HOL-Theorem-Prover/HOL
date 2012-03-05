open bossLib Theory Parse boolTheory pairTheory Defn Tactic boolLib bagTheory
open relationTheory lcsymtacs;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;


val _ = new_theory "SplayHeap"

val _ = Hol_datatype `
heaps = Empty | Node of heaps => 'a => heaps`;

val splay_heap_to_bag_def = Define `
(splay_heap_to_bag Empty = {||}) ∧
(splay_heap_to_bag (Node h1 x h2) =
  BAG_INSERT x (BAG_UNION (splay_heap_to_bag h1) (splay_heap_to_bag h2)))`;

val splay_heap_ok_def = Define `
(splay_heap_ok leq Empty = T) ∧
(splay_heap_ok leq (Node h1 x h2) = 
  splay_heap_ok leq h1 ∧
  splay_heap_ok leq h2 ∧
  BAG_EVERY (\y. leq y x) (splay_heap_to_bag h1) ∧
  BAG_EVERY (\y. ¬leq y x) (splay_heap_to_bag h2))`;

val _ = Define `
empty = Empty`;

val _ = Define `
(is_empty Empty = T) ∧
(is_empty _ = F)`;

val partition_def = Define `
(partition leq pivot Empty = (Empty, Empty)) ∧
(partition leq pivot (Node a x b) =
  if leq x pivot then
    (case b of
        Empty => (Node a x b, Empty)
      | Node b1 y b2 =>
          if leq y pivot then
            let (small, big) = partition leq pivot b2 in
              (Node (Node a x b1) y small, big)
          else
            let (small, big) = partition leq pivot b1 in
              (Node a x small, Node big y b2))
  else
    (case a of
        Empty => (Empty, Node a x b)
      | Node a1 y a2 =>
          if leq y pivot then
            let (small, big) = partition leq pivot a2 in
              (Node a1 y small, Node big x b)
          else
            let (small, big) = partition leq pivot a1 in
              (small, Node big y (Node a2 x b))))`;

val partition_ind = fetch "-" "partition_ind"
val heaps_size_def = fetch "-" "heaps_size_def"

val partition_size = Q.prove (
`!leq p h1 h2 h3.
  ((h2,h3) = partition leq p h1)
  ⇒
  (splay_heap_to_bag h1 =
   BAG_UNION (splay_heap_to_bag h2) (splay_heap_to_bag h3)) ∧
  heaps_size f h2 ≤ heaps_size f h1 ∧
  heaps_size f h3 ≤ heaps_size f h1`,
recInduct partition_ind >>
rw [heaps_size_def, partition_def] >>
every_case_tac >>
fs [] >>
rw [heaps_size_def] >>
cases_on `partition leq pivot h0` >>
cases_on `partition leq pivot h` >>
fs [LET_THM] >>
rw [heaps_size_def] >>
decide_tac);

val partition_bags = Q.prove (
`!leq p h1 h2 h3.
  ((h2,h3) = partition leq p h1)
  ⇒
  (splay_heap_to_bag h1 = 
   BAG_UNION (splay_heap_to_bag h2) (splay_heap_to_bag h3))`,
recInduct partition_ind >>
rw [partition_def, splay_heap_to_bag_def] >>
every_case_tac >>
fs [] >>
rw [splay_heap_to_bag_def] >>
cases_on `partition leq pivot h0` >>
cases_on `partition leq pivot h` >>
fs [LET_THM] >>
rw [splay_heap_to_bag_def, BAG_UNION_INSERT] >>
metis_tac [ASSOC_BAG_UNION, COMM_BAG_UNION, BAG_INSERT_commutes]);

val partition_split = Q.prove (
`!leq p h1 h2 h3.
  transitive leq ∧ 
  trichotomous leq ∧
  ((h2,h3) = partition leq p h1) ∧ 
  splay_heap_ok leq h1
  ⇒
  BAG_EVERY (\y. leq y p) (splay_heap_to_bag h2) ∧
  BAG_EVERY (\y. ¬leq y p) (splay_heap_to_bag h3)`,
recInduct partition_ind >>
rw [partition_def, splay_heap_to_bag_def, splay_heap_ok_def] >>
every_case_tac >>
fs [] >>
rw [] >>
fs [splay_heap_ok_def, splay_heap_to_bag_def] >>
cases_on `partition leq pivot h0` >>
cases_on `partition leq pivot h` >>
fs [LET_THM, splay_heap_to_bag_def] >>
rw [] >>
fs [BAG_EVERY, transitive_def, trichotomous] >>
metis_tac []);

(*
val partition_ok = Q.prove (
`!leq p h1 h2 h3.
  transitive leq ∧ 
  trichotomous leq ∧
  ((h2,h3) = partition leq p h1) ∧
  splay_heap_ok leq h1
  ⇒
  splay_heap_ok leq h2 ∧
  splay_heap_ok leq h3`,
recInduct partition_ind >>
rw [partition_def, splay_heap_ok_def] >>

every_case_tac >>
fs [] >>
rw [] >>
cases_on `partition leq pivot h0` >>
cases_on `partition leq pivot h` >>
fs [LET_THM, splay_heap_ok_def] >>
metis_tac [partition_split]
rw []

, splay_heap_ok_def, splay_heap_to_bag_def] >>
rw [splay_heap_ok_def]
metis_tac [ASSOC_BAG_UNION, COMM_BAG_UNION, BAG_INSERT_commutes]);
*)

val insert_def = Define `
insert leq x t =
  let (a, b) = partition leq x t in
    Node a x b`;

val merge_def = tDefine "merge" `
(merge leq Empty h2 = h2) ∧
(merge leq (Node a x b) h2 =
  let (ta, tb) = partition leq x h2 in
    Node (merge leq ta a) x (merge leq tb b))`
(WF_REL_TAC `measure (\(x,y,z).
                        heaps_size (\_.1) y +
                        heaps_size (\_.1) z)` >>
 rw [] >>
 imp_res_tac partition_thm >>
 pop_assum (MP_TAC o Q.SPEC `(λ_.1)`) >>
 pop_assum (MP_TAC o Q.SPEC `(λ_.1)`) >>
 full_simp_tac (srw_ss() ++ ARITH_ss) [partition_thm]);

val merge_ind = fetch "-" "merge_ind"

val find_min_def = Define `
(find_min (Node Empty x b) = x) ∧
(find_min (Node a x b) = find_min a)`;

val find_min_ind = fetch "-" "find_min_ind"

val delete_min_defn = Define `
(delete_min (Node Empty x b) = b) ∧
(delete_min (Node (Node Empty x b) y c) = Node b y c) ∧
(delete_min (Node (Node a x b) y c) = Node (delete_min a) x (Node b y c))`;

val insert_thm = Q.store_thm ("insert_thm",
`!h leq x.
  splay_heap_to_bag (insert leq x h) =
  BAG_INSERT x (splay_heap_to_bag h)`,
induct_on `h` >>
rw [splay_heap_to_bag_def, insert_def] >>
rw [splay_heap_to_bag_def] >>
fs [insert_def] >>
imp_res_tac (GSYM partition_thm) >>
fs [splay_heap_to_bag_def]);

val insert_ok = Q.store_thm ("insert_ok",
`!leq x h. splay_heap_ok leq h ⇒ splay_heap_ok leq (insert leq x h)`,
induct_on `h` >>
rw [splay_heap_ok_def, insert_def] >>
rw [splay_heap_ok_def] >>

val merge_thm = Q.store_thm ("merge_thm",
`!leq h1 h2.
  (splay_heap_to_bag (merge leq h1 h2) =
    BAG_UNION (splay_heap_to_bag h1) (splay_heap_to_bag h2))`,
recInduct merge_ind >>
rw [merge_def, splay_heap_to_bag_def] >>
cases_on `partition leq x h2` >>
fs [] >>
imp_res_tac (GSYM partition_thm) >>
rw [splay_heap_to_bag_def, BAG_UNION_INSERT] >>
metis_tac [ASSOC_BAG_UNION, COMM_BAG_UNION, BAG_INSERT_commutes]);

(*
val find_min_thm = Q.prove (
`!h x leq. (h ≠ Empty) ∧ splay_heap_ok leq h ⇒
  ((find_min h = x) =
   (BAG_IN x (splay_heap_to_bag h) ∧
    (!y. BAG_IN y (splay_heap_to_bag h) ⇒ leq x y)))`,
recInduct find_min_ind >>
rw [splay_heap_to_bag_def, splay_heap_ok_def, find_min_def] >-
*)

val _ = export_theory()

