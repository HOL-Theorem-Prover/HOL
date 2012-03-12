open bossLib Theory Parse boolTheory pairTheory Defn Tactic boolLib bagTheory
open relationTheory bagLib miscTheory lcsymtacs ml_translatorLib;

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
(pairing_heap_ok get_key leq Empty = T) ∧
(pairing_heap_ok get_key leq (Node x hs) =
  EVERY (pairing_heap_ok get_key leq) hs ∧
  BAG_EVERY (\y. leq (get_key x) (get_key y)) (pairing_heaps_to_bag hs))`
(wf_rel_tac `measure (\(_,_,h). (heap_size (\x.1) h))` >>
rw [] >>
induct_on `hs` >>
rw [fetch "-" "heap_size_def"] >>
fs [] >>
decide_tac);

val _ = Define `
empty = Empty`;

val is_empty_def = Define `
(is_empty Empty = T) ∧
(is_empty _ = F)`;

val merge_def = Define `
(merge get_key leq h Empty = h) ∧
(merge get_key leq Empty h = h) ∧
(merge get_key leq (Node x hs1) (Node y hs2) =
  if leq (get_key x) (get_key y) then
    Node x (Node y hs2 :: hs1)
  else
    Node y (Node x hs1 :: hs2))`;

val merge_ind = fetch "-" "merge_ind"

val insert_def = Define `
insert get_key leq x h = merge get_key leq (Node x []) h`;

val merge_pairs_def = Define `
(merge_pairs get_key leq [] = Empty) ∧
(merge_pairs get_key leq [h] = h) ∧
(merge_pairs get_key leq (h1::h2::hs) =
  merge get_key leq (merge get_key leq h1 h2) (merge_pairs get_key leq hs))`;

val merge_pairs_ind = fetch "-" "merge_pairs_ind"

val find_min_def = Define `
find_min (Node x _) = x`;

val delete_min_def = Define `
delete_min get_key leq (Node x hs) = merge_pairs get_key leq hs`;

val pairing_heap_merge_bag = Q.store_thm ("pairing_heap_merge_bag",
`!get_key leq h1 h2.
  pairing_heap_to_bag (merge get_key leq h1 h2) =
  BAG_UNION (pairing_heap_to_bag h1) (pairing_heap_to_bag h2)`,
HO_MATCH_MP_TAC merge_ind >>
srw_tac [BAG_AC_ss] [merge_def, pairing_heap_to_bag_def, BAG_INSERT_UNION]);

val pairing_heap_merge_ok = Q.store_thm ("pairing_heap_merge_ok",
`!get_key leq h1 h2.
  WeakLinearOrder leq ∧
  pairing_heap_ok get_key leq h1 ∧
  pairing_heap_ok get_key leq h2
  ⇒
  pairing_heap_ok get_key leq (merge get_key leq h1 h2)`,
HO_MATCH_MP_TAC merge_ind >>
rw [merge_def, pairing_heap_ok_def, pairing_heap_to_bag_def] >>
fs [BAG_EVERY] >>
metis_tac [WeakLinearOrder, WeakOrder, transitive_def, WeakLinearOrder_neg]);

val pairing_heap_insert_bag = Q.store_thm ("pairing_heap_insert_bag",
`!h get_key leq x.
  pairing_heap_to_bag (insert get_key leq x h) =
  BAG_INSERT x (pairing_heap_to_bag h)`,
rw [insert_def, pairing_heap_merge_bag, pairing_heap_to_bag_def,
    BAG_INSERT_UNION]);

val pairing_heap_insert_ok = Q.store_thm ("pairing_heap_insert_ok",
`!get_key leq x h.
  WeakLinearOrder leq ∧ pairing_heap_ok get_key leq h
  ⇒
  pairing_heap_ok get_key leq (insert get_key leq x h)`,
rw [insert_def] >>
`pairing_heap_ok get_key leq (Node x [])`
         by rw [pairing_heap_ok_def, pairing_heap_to_bag_def] >>
metis_tac [pairing_heap_merge_ok]);

val pairing_heap_find_min_thm = Q.store_thm ("pairing_heap_find_min_thm",
`!h get_key leq. WeakLinearOrder leq ∧ (h ≠ Empty) ∧ pairing_heap_ok get_key leq h ⇒
  BAG_IN (find_min h) (pairing_heap_to_bag h) ∧
  (!y. BAG_IN y (pairing_heap_to_bag h) ⇒
       leq (get_key (find_min h)) (get_key y))`,
rw [] >>
cases_on `h` >>
fs [find_min_def, pairing_heap_to_bag_def, pairing_heap_ok_def] >>
fs [BAG_EVERY] >>
metis_tac [WeakLinearOrder, WeakOrder, reflexive_def]);

val pairing_heap_merge_pairs_bag = Q.prove (
`!get_key leq hs. pairing_heap_to_bag (merge_pairs get_key leq hs) = pairing_heaps_to_bag hs`,
recInduct merge_pairs_ind >>
srw_tac [BAG_ss]
        [merge_pairs_def, pairing_heap_to_bag_def, pairing_heap_merge_bag]);

val pairing_heap_merge_pairs_ok = Q.prove (
`!get_key leq hs.
  WeakLinearOrder leq ∧ EVERY (pairing_heap_ok get_key leq) hs
  ⇒
  pairing_heap_ok get_key leq (merge_pairs get_key leq hs)`,
recInduct merge_pairs_ind >>
rw [merge_pairs_def, pairing_heap_ok_def, pairing_heap_merge_ok]);

val pairing_heap_delete_min_thm = Q.store_thm ("pairing_heap_delete_min_thm",
`!h get_key leq.
  WeakLinearOrder leq ∧
  (h ≠ Empty) ∧
  pairing_heap_ok get_key leq h
  ⇒
  pairing_heap_ok get_key leq (delete_min get_key leq h) ∧
  (pairing_heap_to_bag (delete_min get_key leq h) =
   BAG_DIFF (pairing_heap_to_bag h) (EL_BAG (find_min h)))`,
rw [] >>
cases_on `h` >>
fs [delete_min_def, pairing_heap_ok_def, pairing_heap_merge_pairs_bag] >-
metis_tac [pairing_heap_merge_pairs_ok] >>
rw [pairing_heap_to_bag_def, find_min_def, BAG_DIFF_INSERT2]);



val res = translate APPEND (* teaching the translator about lists... *)

(* register heap -- begin *)

(* val _ = register_type ``:'a heap`` *)

val ty = ``:'a heap``

val _ = delete_const "heap" handle _ => ()

val tm =
``(heap a Empty v ⇔ (v = Conv (SOME "EMPTY") []) ∧ T) ∧
  (heap a (Node x2_1 x2_2) v ⇔
   ∃v2_1 v2_2.
     (v = Conv (SOME "NODE") [v2_1; v2_2]) ∧ a x2_1 v2_1 ∧
     list (\x v. if MEM x x2_2 then heap a x v else ARB) x2_2 v2_2)``

val inv_def = tDefine "heap_def" [ANTIQUOTE tm]
 (WF_REL_TAC `measure (heap_size (\x.0) o FST o SND)`
  \\ Induct
  \\ EVAL_TAC \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)

val list_SIMP = prove(
  ``!xs b. list (\x v. if b x \/ MEM x xs then p x v else q) xs = list p xs``,
  Induct
  \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,fetch "-" "list_def",MEM,DISJ_ASSOC])
  |> Q.SPECL [`xs`,`\x.F`] |> SIMP_RULE std_ss [];

val inv_def = inv_def |> SIMP_RULE std_ss [list_SIMP]
                      |> CONV_RULE (DEPTH_CONV ETA_CONV)

val _ = set_inv_def (ty,inv_def)

val _ = register_type ``:'a heap``

(* register heap -- end *)

val res = translate is_empty_def;
val res = translate merge_def;
val res = translate insert_def;
val res = translate find_min_def;
val res = translate merge_pairs_def;
val res = translate delete_min_def;

val _ = export_theory ()
