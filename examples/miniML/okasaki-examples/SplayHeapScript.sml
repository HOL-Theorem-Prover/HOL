open bossLib Theory Parse boolTheory pairTheory Defn Tactic boolLib bagTheory
open relationTheory bagLib miscTheory lcsymtacs;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;

val _ = new_theory "SplayHeap"

val _ = Hol_datatype `
heap = Empty | Node of heap => 'a => heap`;

val splay_heap_to_bag_def = Define `
(splay_heap_to_bag Empty = {||}) ∧
(splay_heap_to_bag (Node h1 x h2) =
  BAG_INSERT x (BAG_UNION (splay_heap_to_bag h1) (splay_heap_to_bag h2)))`;

val splay_heap_ok_def = Define `
(splay_heap_ok get_key leq Empty = T) ∧
(splay_heap_ok get_key leq (Node h1 x h2) =
  splay_heap_ok get_key leq h1 ∧
  splay_heap_ok get_key leq h2 ∧
  BAG_EVERY (\y. leq (get_key y) (get_key x)) (splay_heap_to_bag h1) ∧
  BAG_EVERY (\y. leq (get_key x) (get_key y)) (splay_heap_to_bag h2))`;

val _ = Define `
empty = Empty`;

val _ = Define `
(is_empty Empty = T) ∧
(is_empty _ = F)`;

val partition_def = Define `
(partition get_key leq pivot Empty = (Empty, Empty)) ∧
(partition get_key leq pivot (Node a x b) =
  if leq (get_key x) (get_key pivot) then
    (case b of
        Empty => (Node a x b, Empty)
      | Node b1 y b2 =>
          if leq (get_key y) (get_key pivot) then
            let (small, big) = partition get_key leq pivot b2 in
              (Node (Node a x b1) y small, big)
          else
            let (small, big) = partition get_key leq pivot b1 in
              (Node a x small, Node big y b2))
  else
    (case a of
        Empty => (Empty, Node a x b)
      | Node a1 y a2 =>
          if leq (get_key y) (get_key pivot) then
            let (small, big) = partition get_key leq pivot a2 in
              (Node a1 y small, Node big x b)
          else
            let (small, big) = partition get_key leq pivot a1 in
              (small, Node big y (Node a2 x b))))`;

val partition_ind = fetch "-" "partition_ind"
val heap_size_def = fetch "-" "heap_size_def"

val partition_size = Q.prove (
`!get_key leq p h1 h2 h3.
  ((h2,h3) = partition get_key leq p h1)
  ⇒
  heap_size f h2 ≤ heap_size f h1 ∧
  heap_size f h3 ≤ heap_size f h1`,
recInduct partition_ind >>
rw [heap_size_def, partition_def] >>
every_case_tac >>
fs [] >>
rw [heap_size_def] >>
cases_on `partition get_key leq pivot h0` >>
cases_on `partition get_key leq pivot h` >>
fs [LET_THM] >>
rw [heap_size_def] >>
decide_tac);

val partition_bags = Q.prove (
`!get_key leq p h1 h2 h3.
  ((h2,h3) = partition get_key leq p h1)
  ⇒
  (splay_heap_to_bag h1 =
   BAG_UNION (splay_heap_to_bag h2) (splay_heap_to_bag h3))`,
recInduct partition_ind >>
rw [partition_def, splay_heap_to_bag_def] >>
every_case_tac >>
fs [] >>
rw [splay_heap_to_bag_def] >>
cases_on `partition get_key leq pivot h0` >>
cases_on `partition get_key leq pivot h` >>
fs [LET_THM] >>
rw [splay_heap_to_bag_def, BAG_UNION_INSERT] >>
metis_tac [ASSOC_BAG_UNION, COMM_BAG_UNION, BAG_INSERT_commutes]);

val partition_split = Q.prove (
`!get_key leq p h1 h2 h3.
  transitive leq ∧
  trichotomous leq ∧
  ((h2,h3) = partition get_key leq p h1) ∧
  splay_heap_ok get_key leq h1
  ⇒
  BAG_EVERY (\y. leq (get_key y) (get_key p)) (splay_heap_to_bag h2) ∧
  BAG_EVERY (\y. ¬leq (get_key y) (get_key p)) (splay_heap_to_bag h3)`,
recInduct partition_ind >>
rw [partition_def, splay_heap_to_bag_def, splay_heap_ok_def] >>
every_case_tac >>
fs [] >>
rw [] >>
fs [splay_heap_ok_def, splay_heap_to_bag_def] >>
cases_on `partition get_key leq pivot h0` >>
cases_on `partition get_key leq pivot h` >>
fs [LET_THM, splay_heap_to_bag_def] >>
rw [] >>
fs [BAG_EVERY, transitive_def, trichotomous] >>
metis_tac []);

val partition_ok_lem = Q.prove (
`!get_key leq p h1 h2 h3.
  (partition get_key leq p h1 = (h2, h3)) ⇒
  BAG_EVERY P (splay_heap_to_bag h1) ⇒
  BAG_EVERY P (splay_heap_to_bag h2) ∧
  BAG_EVERY P (splay_heap_to_bag h3)`,
rw [] >>
`splay_heap_to_bag h1 =
 BAG_UNION (splay_heap_to_bag h2) (splay_heap_to_bag h3)`
          by metis_tac [partition_bags] >>
rw [] >>
fs [] >>
rw []);

val partition_ok = Q.prove (
`!get_key leq p h1 h2 h3.
  WeakLinearOrder leq ∧
  ((h2,h3) = partition get_key leq p h1) ∧
  splay_heap_ok get_key leq h1
  ⇒
  splay_heap_ok get_key leq h2 ∧
  splay_heap_ok get_key leq h3`,
recInduct partition_ind >>
RW_TAC pure_ss [] >>
cases_on `leq (get_key x) (get_key pivot)` >>
fs [partition_def, splay_heap_ok_def] >>
every_case_tac >>
fs [] >>
rw [] >>
cases_on `partition get_key leq pivot h0` >>
cases_on `partition get_key leq pivot h` >>
fs [LET_THM, splay_heap_ok_def, splay_heap_to_bag_def] >>
rw [] >-
(fs [BAG_EVERY] >>
 metis_tac [transitive_def, WeakLinearOrder, WeakOrder]) >-
metis_tac [partition_ok_lem] >-
metis_tac [partition_ok_lem] >-
metis_tac [partition_ok_lem] >-
metis_tac [partition_ok_lem] >-
metis_tac [partition_ok_lem] >-
metis_tac [partition_ok_lem] >-
(fs [BAG_EVERY] >>
 metis_tac [transitive_def, WeakLinearOrder, WeakOrder]));

val insert_def = Define `
insert get_key leq x t =
  let (a, b) = partition get_key leq x t in
    Node a x b`;

val merge_def = tDefine "merge" `
(merge get_key leq Empty h2 = h2) ∧
(merge get_key leq (Node a x b) h2 =
  let (ta, tb) = partition get_key leq x h2 in
    Node (merge get_key leq ta a) x (merge get_key leq tb b))`
(WF_REL_TAC `measure (\(_,x,y,z).
                        heap_size (\_.1) y +
                        heap_size (\_.1) z)` >>
 rw [] >>
 imp_res_tac partition_size >>
 pop_assum (MP_TAC o Q.SPEC `(λ_.1)`) >>
 pop_assum (MP_TAC o Q.SPEC `(λ_.1)`) >>
 full_simp_tac (srw_ss() ++ ARITH_ss) [partition_size]);

val merge_ind = fetch "-" "merge_ind"

val find_min_def = Define `
(find_min (Node Empty x b) = x) ∧
(find_min (Node a x b) = find_min a)`;

val find_min_ind = fetch "-" "find_min_ind"

val delete_min_def = Define `
(delete_min (Node Empty x b) = b) ∧
(delete_min (Node (Node Empty x b) y c) = Node b y c) ∧
(delete_min (Node (Node a x b) y c) = Node (delete_min a) x (Node b y c))`;

val delete_min_ind = fetch "-" "delete_min_ind"

val splay_heap_insert_bag = Q.store_thm ("splay_heap_insert_bag",
`!h get_key leq x.
  splay_heap_to_bag (insert get_key leq x h) =
  BAG_INSERT x (splay_heap_to_bag h)`,
induct_on `h` >>
rw [splay_heap_to_bag_def, insert_def] >>
rw [splay_heap_to_bag_def] >>
fs [insert_def] >>
imp_res_tac (GSYM partition_bags) >>
fs [splay_heap_to_bag_def]);

val splay_heap_insert_ok = Q.store_thm ("splay_heap_insert_ok",
`!get_key leq x h.
  WeakLinearOrder leq ∧ splay_heap_ok get_key leq h
  ⇒
  splay_heap_ok get_key leq (insert get_key leq x h)`,
rw [insert_def, splay_heap_ok_def] >>
rw [splay_heap_ok_def] >-
metis_tac [partition_ok] >-
metis_tac [partition_ok] >-
metis_tac [WeakLinearOrder, WeakOrder, partition_split] >-
(`BAG_EVERY (\y. ¬leq (get_key y) (get_key x)) (splay_heap_to_bag b)`
           by metis_tac [partition_split, WeakLinearOrder, WeakOrder] >>
 fs [BAG_EVERY] >>
 metis_tac [WeakLinearOrder_neg]));

val splay_heap_merge_bag = Q.store_thm ("splay_heap_merge_bag",
`!get_key leq h1 h2.
  (splay_heap_to_bag (merge get_key leq h1 h2) =
    BAG_UNION (splay_heap_to_bag h1) (splay_heap_to_bag h2))`,
recInduct merge_ind >>
rw [merge_def, splay_heap_to_bag_def] >>
cases_on `partition get_key leq x h2` >>
fs [] >>
imp_res_tac (GSYM partition_bags) >>
rw [splay_heap_to_bag_def, BAG_UNION_INSERT] >>
metis_tac [ASSOC_BAG_UNION, COMM_BAG_UNION, BAG_INSERT_commutes]);

val splay_heap_merge_ok = Q.store_thm ("splay_heap_merge_ok",
`!get_key leq h1 h2.
  WeakLinearOrder leq ∧ splay_heap_ok get_key leq h1 ∧ splay_heap_ok get_key leq h2
  ⇒
  splay_heap_ok get_key leq (merge get_key leq h1 h2)`,
recInduct merge_ind >>
rw [merge_def, splay_heap_ok_def] >>
rw [splay_heap_ok_def, splay_heap_merge_bag] >-
metis_tac [partition_ok] >-
metis_tac [partition_ok] >-
metis_tac [partition_split, WeakLinearOrder, WeakOrder] >-
(`BAG_EVERY (\y. ¬leq (get_key y) (get_key x)) (splay_heap_to_bag tb)`
           by metis_tac [partition_split, WeakLinearOrder, WeakOrder] >>
 fs [BAG_EVERY] >>
 metis_tac [WeakLinearOrder_neg]));

val splay_heap_find_min_thm = Q.store_thm ("splay_heap_find_min_thm",
`!h get_key leq. 
  WeakLinearOrder leq ∧ (h ≠ Empty) ∧ splay_heap_ok get_key leq h 
  ⇒
  BAG_IN (find_min h) (splay_heap_to_bag h) ∧
  (!y. BAG_IN y (splay_heap_to_bag h) ⇒ 
       leq (get_key (find_min h)) (get_key y))`,
recInduct find_min_ind >>
rw [splay_heap_to_bag_def, find_min_def] >>
fs [splay_heap_ok_def, splay_heap_to_bag_def, BAG_EVERY] >> 
metis_tac [WeakLinearOrder, WeakOrder, transitive_def, reflexive_def]);

val splay_heap_delete_min_thm = Q.store_thm ("splay_heap_delete_min_thm",
`!h get_key leq.
  WeakLinearOrder leq ∧
  (h ≠ Empty) ∧
  splay_heap_ok get_key leq h
  ⇒
  splay_heap_ok get_key leq (delete_min h) ∧
  (splay_heap_to_bag (delete_min h) =
   BAG_DIFF (splay_heap_to_bag h) (EL_BAG (find_min h)))`,
HO_MATCH_MP_TAC delete_min_ind >>
srw_tac [bagLib.BAG_ss]
        [delete_min_def, splay_heap_ok_def, splay_heap_to_bag_def,
         find_min_def, BAG_INSERT_UNION] >|
[res_tac >>
     rw [] >>
     match_mp_tac BAG_EVERY_DIFF >>
     rw [],
 fs [BAG_EVERY_EL],
 fs [BAG_EVERY_EL] >>
     fs [BAG_EVERY] >>
     metis_tac [WeakLinearOrder, WeakOrder, transitive_def],
 res_tac >>
     srw_tac [BAG_AC_ss] [] >>
     `splay_heap_ok get_key leq (Node v6 v7 v8)` by rw [splay_heap_ok_def] >>
     `BAG_IN (find_min (Node v6 v7 v8)) (splay_heap_to_bag (Node v6 v7 v8))`
          by metis_tac [splay_heap_find_min_thm, fetch "-" "heap_distinct"] >>
     fs [splay_heap_to_bag_def] >>
     `SUB_BAG (EL_BAG (find_min (Node v6 v7 v8)))
              (EL_BAG v7 ⊎ (splay_heap_to_bag v6 ⊎ splay_heap_to_bag v8))`
                by rw [SUB_BAG_EL_BAG] >>
     rw [BAG_UNION_DIFF, SUB_BAG_UNION] >>
     srw_tac [BAG_AC_ss] []]);

val _ = export_theory()

