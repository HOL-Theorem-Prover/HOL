open preamble
open bagTheory bagLib miscTheory ml_translatorLib

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []

val _ = new_theory "PairingHeap"

(* Okasaki page 54 *)

val _ = Hol_datatype `
heap = Empty | Tree of 'a => heap list`;

val heap_to_bag_def = Define `
(heap_to_bag Empty = {||}) ∧
(heap_to_bag (Tree x hs) =
  BAG_INSERT x (heaps_to_bag hs)) ∧

(heaps_to_bag [] = {||}) ∧
(heaps_to_bag (h::hs) =
  BAG_UNION (heap_to_bag h) (heaps_to_bag hs))`;

val is_heap_ordered_def = tDefine "is_heap_ordered" `
(is_heap_ordered get_key leq Empty = T) ∧
(is_heap_ordered get_key leq (Tree x hs) =
  EVERY (is_heap_ordered get_key leq) hs ∧
  BAG_EVERY (\y. leq (get_key x) (get_key y)) (heaps_to_bag hs))`
(wf_rel_tac `measure (\(_,_,h). (heap_size (\x.1) h))` >>
rw [] >>
induct_on `hs` >>
rw [fetch "-" "heap_size_def"] >>
fs [] >>
decide_tac);

val empty_def = Define `
empty = Empty`;

val is_empty_def = Define `
(is_empty Empty = T) ∧
(is_empty _ = F)`;

val merge_def = Define `
(merge get_key leq h Empty = h) ∧
(merge get_key leq Empty h = h) ∧
(merge get_key leq (Tree x hs1) (Tree y hs2) =
  if leq (get_key x) (get_key y) then
    Tree x (Tree y hs2 :: hs1)
  else
    Tree y (Tree x hs1 :: hs2))`;

val merge_ind = fetch "-" "merge_ind"

val insert_def = Define `
insert get_key leq x h = merge get_key leq (Tree x []) h`;

val merge_pairs_def = Define `
(merge_pairs get_key leq [] = Empty) ∧
(merge_pairs get_key leq [h] = h) ∧
(merge_pairs get_key leq (h1::h2::hs) =
  merge get_key leq (merge get_key leq h1 h2) (merge_pairs get_key leq hs))`;

val merge_pairs_ind = fetch "-" "merge_pairs_ind"

val find_min_def = Define `
find_min (Tree x _) = x`;

val delete_min_def = Define `
delete_min get_key leq (Tree x hs) = merge_pairs get_key leq hs`;


(* Functional correctness proof *)

val merge_bag = Q.store_thm ("merge_bag",
`!get_key leq h1 h2.
  heap_to_bag (merge get_key leq h1 h2) =
  BAG_UNION (heap_to_bag h1) (heap_to_bag h2)`,
HO_MATCH_MP_TAC merge_ind >>
srw_tac [BAG_AC_ss] [merge_def, heap_to_bag_def, BAG_INSERT_UNION]);

val merge_heap_ordered = Q.store_thm ("merge_heap_ordered",
`!get_key leq h1 h2.
  WeakLinearOrder leq ∧
  is_heap_ordered get_key leq h1 ∧
  is_heap_ordered get_key leq h2
  ⇒
  is_heap_ordered get_key leq (merge get_key leq h1 h2)`,
HO_MATCH_MP_TAC merge_ind >>
rw [merge_def, is_heap_ordered_def, heap_to_bag_def] >>
fs [BAG_EVERY] >>
metis_tac [WeakLinearOrder, WeakOrder, transitive_def, WeakLinearOrder_neg]);

val insert_bag = Q.store_thm ("insert_bag",
`!h get_key leq x.
  heap_to_bag (insert get_key leq x h) = BAG_INSERT x (heap_to_bag h)`,
rw [insert_def, merge_bag, heap_to_bag_def, BAG_INSERT_UNION]);

val insert_heap_ordered = Q.store_thm ("insert_heap_ordered",
`!get_key leq x h.
  WeakLinearOrder leq ∧ is_heap_ordered get_key leq h
  ⇒
  is_heap_ordered get_key leq (insert get_key leq x h)`,
rw [insert_def] >>
`is_heap_ordered get_key leq (Tree x [])`
         by rw [is_heap_ordered_def, heap_to_bag_def] >>
metis_tac [merge_heap_ordered]);

val find_min_correct = Q.store_thm ("find_min_correct",
`!h get_key leq.
  WeakLinearOrder leq ∧ (h ≠ Empty) ∧ is_heap_ordered get_key leq h
  ⇒
  BAG_IN (find_min h) (heap_to_bag h) ∧
  (!y. BAG_IN y (heap_to_bag h) ⇒ leq (get_key (find_min h)) (get_key y))`,
rw [] >>
cases_on `h` >>
fs [find_min_def, heap_to_bag_def, is_heap_ordered_def] >>
fs [BAG_EVERY] >>
metis_tac [WeakLinearOrder, WeakOrder, reflexive_def]);

val merge_pairs_bag = Q.prove (
`!get_key leq hs. heap_to_bag (merge_pairs get_key leq hs) = heaps_to_bag hs`,
recInduct merge_pairs_ind >>
srw_tac [BAG_ss] [merge_pairs_def, heap_to_bag_def, merge_bag]);

val merge_pairs_heap_ordered = Q.prove (
`!get_key leq hs.
  WeakLinearOrder leq ∧ EVERY (is_heap_ordered get_key leq) hs
  ⇒
  is_heap_ordered get_key leq (merge_pairs get_key leq hs)`,
recInduct merge_pairs_ind >>
rw [merge_pairs_def, is_heap_ordered_def, merge_heap_ordered]);

val delete_min_correct = Q.store_thm ("delete_min_correct",
`!h get_key leq.
  WeakLinearOrder leq ∧ (h ≠ Empty) ∧ is_heap_ordered get_key leq h
  ⇒
  is_heap_ordered get_key leq (delete_min get_key leq h) ∧
  (heap_to_bag (delete_min get_key leq h) =
   BAG_DIFF (heap_to_bag h) (EL_BAG (find_min h)))`,
rw [] >>
cases_on `h` >>
fs [delete_min_def, is_heap_ordered_def, merge_pairs_bag] >-
metis_tac [merge_pairs_heap_ordered] >>
rw [heap_to_bag_def, find_min_def, BAG_DIFF_INSERT2]);


(* Translate to MiniML *)

val res = translate APPEND (* teaching the translator about lists... *)

(* register heap -- begin *)

(* val _ = register_type ``:'a heap`` *)

val ty = ``:'a heap``

val _ = delete_const "heap" handle _ => ()

val tm =
``(heap a Empty v ⇔ (v = Conv "Empty" []) ∧ T) ∧
  (heap a (Tree x2_1 x2_2) v ⇔
   ∃v2_1 v2_2.
     (v = Conv "Tree" [v2_1; v2_2]) ∧ a x2_1 v2_1 ∧
     list (\x v. if MEM x x2_2 then heap a x v else ARB) x2_2 v2_2)``

val inv_def = tDefine "heap_def" [ANTIQUOTE tm]
 (WF_REL_TAC `measure (heap_size (\x.0) o FST o SND)`
  THEN Induct
  THEN EVAL_TAC THEN SIMP_TAC std_ss []
  THEN REPEAT STRIP_TAC THEN RES_TAC
  THEN FULL_SIMP_TAC std_ss [] THEN DECIDE_TAC)

val list_SIMP = prove(
  ``!xs b. list (\x v. if b x \/ MEM x xs then p x v else q) xs = list p xs``,
  Induct
  THEN FULL_SIMP_TAC std_ss [FUN_EQ_THM,fetch "-" "list_def",MEM,DISJ_ASSOC])
  |> Q.SPECL [`xs`,`\x.F`] |> SIMP_RULE std_ss [];

val inv_def = inv_def |> SIMP_RULE std_ss [list_SIMP]
                      |> CONV_RULE (DEPTH_CONV ETA_CONV)

val _ = set_inv_def (ty,inv_def)

val _ = register_type ``:'a heap``

(* register heap -- end *)

val res = translate empty_def;
val res = translate is_empty_def;
val res = translate merge_def;
val res = translate insert_def;
val res = translate find_min_def;
val res = translate merge_pairs_def;
val res = translate delete_min_def;

val _ = export_theory ()
