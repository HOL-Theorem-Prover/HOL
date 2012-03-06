open bossLib Theory Parse boolTheory pairTheory Defn Tactic boolLib bagTheory
open relationTheory bagLib lcsymtacs;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;


val _ = new_theory "SplayHeap"

val WeakLinearOrder_neg = Q.prove (
`!leq x y. WeakLinearOrder leq ⇒ (~leq x y = leq y x ∧ x ≠ y)`,
metis_tac [WeakLinearOrder, WeakOrder, trichotomous, reflexive_def,
           antisymmetric_def]);

val BAG_EVERY_DIFF = Q.prove (
`!P b1 b2. BAG_EVERY P b1 ⇒ BAG_EVERY P (BAG_DIFF b1 b2)`,
rw [BAG_EVERY] >>
metis_tac [BAG_IN_DIFF_E]);

val BAG_EVERY_EL = Q.prove (
`!P x. BAG_EVERY P (EL_BAG x) = P x`,
rw [BAG_EVERY, EL_BAG]);

val BAG_INN_BAG_DIFF = Q.prove (
`!x m b1 b2. 
  BAG_INN x m (BAG_DIFF b1 b2) = 
  ∃n1 n2. (m = n1 - n2) ∧ 
          BAG_INN x n1 b1 ∧ BAG_INN x n2 b2 ∧ ~BAG_INN x (n2 + 1) b2`,
rw [BAG_INN, BAG_DIFF] >>
EQ_TAC >>
rw [] >|
[qexists_tac `b2 x + m` >>
     qexists_tac `b2 x` >>
     decide_tac,
 qexists_tac `0` >>
     qexists_tac `b2 x` >>
     decide_tac,
 decide_tac]);

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
  BAG_EVERY (\y. leq x y) (splay_heap_to_bag h2))`;

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

val partition_ok_lem = Q.prove (
`!leq p h1 h2 h3.
  (partition leq p h1 = (h2, h3)) ⇒ 
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
`!leq p h1 h2 h3.
  WeakLinearOrder leq ∧
  ((h2,h3) = partition leq p h1) ∧
  splay_heap_ok leq h1
  ⇒
  splay_heap_ok leq h2 ∧
  splay_heap_ok leq h3`,
recInduct partition_ind >>
RW_TAC pure_ss [] >> 
cases_on `leq x pivot` >>
fs [partition_def, splay_heap_ok_def] >>
every_case_tac >>
fs [] >>
rw [] >>
cases_on `partition leq pivot h0` >>
cases_on `partition leq pivot h` >>
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
`!h leq x.
  splay_heap_to_bag (insert leq x h) =
  BAG_INSERT x (splay_heap_to_bag h)`,
induct_on `h` >>
rw [splay_heap_to_bag_def, insert_def] >>
rw [splay_heap_to_bag_def] >>
fs [insert_def] >>
imp_res_tac (GSYM partition_bags) >>
fs [splay_heap_to_bag_def]);

val splay_heap_insert_ok = Q.store_thm ("splay_heap_insert_ok",
`!leq x h. 
  WeakLinearOrder leq ∧ splay_heap_ok leq h 
  ⇒ 
  splay_heap_ok leq (insert leq x h)`,
rw [insert_def, splay_heap_ok_def] >>
rw [splay_heap_ok_def] >-
metis_tac [partition_ok] >-
metis_tac [partition_ok] >-
metis_tac [WeakLinearOrder, WeakOrder, partition_split] >-
(`BAG_EVERY (\y. ¬leq y x) (splay_heap_to_bag b)` 
           by metis_tac [partition_split, WeakLinearOrder, WeakOrder] >>
 fs [BAG_EVERY] >>
 metis_tac [WeakLinearOrder_neg]));

val splay_heap_merge_bag = Q.store_thm ("splay_heap_merge_bag",
`!leq h1 h2.
  (splay_heap_to_bag (merge leq h1 h2) =
    BAG_UNION (splay_heap_to_bag h1) (splay_heap_to_bag h2))`,
recInduct merge_ind >>
rw [merge_def, splay_heap_to_bag_def] >>
cases_on `partition leq x h2` >>
fs [] >>
imp_res_tac (GSYM partition_bags) >>
rw [splay_heap_to_bag_def, BAG_UNION_INSERT] >>
metis_tac [ASSOC_BAG_UNION, COMM_BAG_UNION, BAG_INSERT_commutes]);

val splay_heap_merge_ok = Q.store_thm ("splay_heap_merge_ok",
`!leq h1 h2.
  WeakLinearOrder leq ∧ splay_heap_ok leq h1 ∧ splay_heap_ok leq h2 
  ⇒ 
  splay_heap_ok leq (merge leq h1 h2)`,
recInduct merge_ind >>
rw [merge_def, splay_heap_ok_def] >>
rw [splay_heap_ok_def, splay_heap_merge_bag] >-
metis_tac [partition_ok] >-
metis_tac [partition_ok] >-
metis_tac [partition_split, WeakLinearOrder, WeakOrder] >-
(`BAG_EVERY (\y. ¬leq y x) (splay_heap_to_bag tb)` 
           by metis_tac [partition_split, WeakLinearOrder, WeakOrder] >>
 fs [BAG_EVERY] >>
 metis_tac [WeakLinearOrder_neg]));

val splay_heap_find_min = Q.prove (
`!h x leq. WeakLinearOrder leq ∧ (h ≠ Empty) ∧ splay_heap_ok leq h ⇒
  ((find_min h = x) =
   (BAG_IN x (splay_heap_to_bag h) ∧
    (!y. BAG_IN y (splay_heap_to_bag h) ⇒ leq x y)))`,
recInduct find_min_ind >>
rw [splay_heap_to_bag_def, splay_heap_ok_def, find_min_def] >-
metis_tac [BAG_EVERY, WeakLinearOrder_neg, WeakLinearOrder, WeakOrder, 
           reflexive_def] >>
EQ_TAC >>
rw [] >-
metis_tac [] >-
(fs [BAG_EVERY] >>
 metis_tac [WeakLinearOrder, WeakOrder, transitive_def]) >-
metis_tac [] >-
metis_tac [] >-
metis_tac [] >-
(fs [BAG_EVERY] >>
 metis_tac [WeakLinearOrder, WeakOrder, transitive_def]) >-
metis_tac [BAG_EVERY, WeakLinearOrder_neg, WeakLinearOrder, WeakOrder, 
           reflexive_def] >-
metis_tac [] >-
metis_tac [] >-
metis_tac [] >-
metis_tac [BAG_EVERY, WeakLinearOrder_neg, WeakLinearOrder, WeakOrder, 
           reflexive_def]);

val splay_heap_find_min_thm = Q.store_thm ("splay_heap_find_min_thm",
`!h leq. WeakLinearOrder leq ∧ (h ≠ Empty) ∧ splay_heap_ok leq h ⇒
  BAG_IN (find_min h) (splay_heap_to_bag h) ∧
  (!y. BAG_IN y (splay_heap_to_bag h) ⇒ leq (find_min h) y)`,
metis_tac [splay_heap_find_min]);

val splay_heap_delete_min_thm = Q.store_thm ("splay_heap_delete_min_thm",
`!h leq. 
  WeakLinearOrder leq ∧
  (h ≠ Empty) ∧ 
  splay_heap_ok leq h 
  ⇒ 
  splay_heap_ok leq (delete_min h) ∧
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
     (* EL_BAG (find_min (Node v6 v7 v8)) is a subbag of 
        EL_BAG v7 ⊎ (splay_heap_to_bag v6 ⊎ splay_heap_to_bag v8)
        by splay_heap_find_min_thm, and so by BAG_UNION_DIFF the difference
        can be lifted out to the top.  I don't feel like bashing this through
        HOL at the moment. *)
     all_tac]);

val _ = export_theory()

