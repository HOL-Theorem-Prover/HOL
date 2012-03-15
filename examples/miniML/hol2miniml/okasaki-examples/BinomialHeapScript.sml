open preamble
open bagTheory bagLib miscTheory ml_translatorLib;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []

val _ = new_theory "BinomialHeap"

(* Okasaki page 24 *)

val _ = Hol_datatype `
tree = Node of num => 'a => tree list`;

val _ = type_abbrev ("heap", ``:'a tree list``);

val tree_size_def = fetch "-" "tree_size_def";

val heap_to_bag_def = tDefine "heap_to_bag" `
(heap_to_bag [] = {||}) ∧
(heap_to_bag (h::hs) =
  BAG_UNION (tree_to_bag h) (heap_to_bag hs)) ∧

(tree_to_bag (Node _ x hs) =
  BAG_INSERT x (heap_to_bag hs))`
(wf_rel_tac `measure (\x. case x of INL x => tree1_size (\x.0) x 
                                  | INR x => tree_size (\x.0) x)` >>
 rw [tree_size_def]);

val is_heap_ordered_def = tDefine "is_heap_ordered" `
(is_heap_ordered get_key leq [] = T) ∧
(is_heap_ordered get_key leq (t::ts) = 
  is_heap_ordered_tree get_key leq t ∧ is_heap_ordered get_key leq ts) ∧

(is_heap_ordered_tree get_key leq (Node _ x hs) =
  is_heap_ordered get_key leq hs ∧
  BAG_EVERY (\y. leq (get_key x) (get_key y)) (heap_to_bag hs))`
(wf_rel_tac `measure (\x. case x of INL (_,_,x) => tree1_size (\x.0) x 
                                  | INR (_,_,x) => tree_size (\x.0) x)` >>
 rw [tree_size_def]);

val empty_def = Define `
empty = []`;

val is_empty_def = Define `
(is_empty [] = T) ∧
(is_empty _ = F)`;

val rank_def = Define `
rank (Node r x c) = r`;

val root_def = Define `
root (Node r x c) = x`;

val link_def = Define `
link get_key leq (Node r x1 c1) (Node r' x2 c2) =
  if leq (get_key x1) (get_key x2) then
    Node (r+1) x1 ((Node r' x2 c2)::c1)
  else
    Node (r+1) x2 ((Node r x1 c1)::c2)`;

val ins_tree_def = Define `
(ins_tree get_key leq t [] = [t]) ∧
(ins_tree get_key leq t (t'::ts') =
  if rank t < rank t' then
    t::t'::ts'
  else
    ins_tree get_key leq (link get_key leq t t') ts')`;

val insert_def = Define `
insert get_key leq x ts = ins_tree get_key leq (Node 0 x []) ts`;

val merge_def = Define `
(merge get_key leq ts [] = ts) ∧
(merge get_key leq [] ts = ts) ∧
(merge get_key leq (t1::ts1) (t2::ts2) =
  if rank t1 < rank t2 then
    t1 :: merge get_key leq ts1 (t2::ts2)
  else if rank t2 < rank t1 then
    t2 :: merge get_key leq (t1::ts1) ts2
  else
    ins_tree get_key leq (link get_key leq t1 t2) (merge get_key leq ts1 ts2))`;

val merge_ind = fetch "-" "merge_ind";

val remove_min_tree_def = Define `
(remove_min_tree get_key leq [t] = (t,[])) ∧
(remove_min_tree get_key leq (t::ts) =
  let (t',ts') = remove_min_tree get_key leq ts in
    if leq (get_key (root t)) (get_key (root t')) then
      (t,ts)
    else
      (t',t::ts'))`;

val find_min_def = Define `
find_min get_key leq ts =
  let (t,ts') = remove_min_tree get_key leq ts in
    root t`;

val delete_min_def = Define `
delete_min get_key leq ts =
  case remove_min_tree get_key leq ts of
    | (Node _ x ts1, ts2) => merge get_key leq (REVERSE ts1) ts2`;


(* Functional correctness proof *)

val ins_bag = Q.prove (
`!get_key leq t h.
  heap_to_bag (ins_tree get_key leq t h) =
  BAG_UNION (tree_to_bag t) (heap_to_bag h)`,
induct_on `h` >>
rw [heap_to_bag_def, ins_tree_def, link_def] >>
cases_on `t` >>
cases_on `h'` >>
srw_tac [BAG_ss] [heap_to_bag_def, ins_tree_def, link_def, BAG_INSERT_UNION]);

val ins_heap_ordered = Q.prove (
`!get_key leq t h.
  WeakLinearOrder leq ∧ 
  is_heap_ordered_tree get_key leq t ∧
  is_heap_ordered get_key leq h
  ⇒
  is_heap_ordered get_key leq (ins_tree get_key leq t h)`,
induct_on `h` >>
rw [is_heap_ordered_def, ins_bag, ins_tree_def] >>
cases_on `t` >>
cases_on `h'` >>
rw [link_def] >>
fs [] >>
Q.PAT_ASSUM `!get_key leq t. P get_key leq t` match_mp_tac >>
rw [is_heap_ordered_def] >>
fs [is_heap_ordered_def, BAG_EVERY, heap_to_bag_def] >>
metis_tac [WeakLinearOrder, WeakOrder, transitive_def, WeakLinearOrder_neg]);

val insert_bag = Q.store_thm ("insert_bag",
`!get_key leq s h.
  heap_to_bag (insert get_key leq s h) = BAG_INSERT s (heap_to_bag h)`,
rw [insert_def, ins_bag, heap_to_bag_def, BAG_INSERT_UNION]);

val insert_heap_ordered = Q.store_thm ("insert_heap_ordered",
`!get_key leq x h.
  WeakLinearOrder leq ∧ 
  is_heap_ordered get_key leq h
  ⇒
  is_heap_ordered get_key leq (insert get_key leq x h)`,
rw [insert_def, is_heap_ordered_def] >>
match_mp_tac ins_heap_ordered >>
rw [is_heap_ordered_def, BAG_EVERY, heap_to_bag_def]);

val merge_bag = Q.store_thm ("merge_bag",
`!get_key leq h1 h2.
  heap_to_bag (merge get_key leq h1 h2) =
  BAG_UNION (heap_to_bag h1) (heap_to_bag h2)`,
HO_MATCH_MP_TAC merge_ind >>
srw_tac [BAG_ss] [merge_def, heap_to_bag_def, BAG_INSERT_UNION, ins_bag] >>
cases_on `t1` >>
cases_on `t2` >>
srw_tac [BAG_ss] [link_def, heap_to_bag_def, BAG_INSERT_UNION]);

val merge_heap_ordered = Q.store_thm ("merge_heap_ordered",
`!get_key leq h1 h2.
  WeakLinearOrder leq ∧
  is_heap_ordered get_key leq h1 ∧
  is_heap_ordered get_key leq h2
  ⇒
  is_heap_ordered get_key leq (merge get_key leq h1 h2)`,
HO_MATCH_MP_TAC merge_ind >>
rw [merge_def, is_heap_ordered_def, heap_to_bag_def] >>
fs [] >>
match_mp_tac ins_heap_ordered >>
rw [] >>
cases_on `t1` >>
cases_on `t2` >>
rw [link_def, is_heap_ordered_def, BAG_EVERY] >>
fs [is_heap_ordered_def, BAG_EVERY, heap_to_bag_def] >>
metis_tac [WeakLinearOrder, WeakOrder, transitive_def, WeakLinearOrder_neg]);

val remove_min_tree = Q.prove (
`∀get_key leq h t h'.
  WeakLinearOrder leq ∧
  (h ≠ []) ∧
  is_heap_ordered get_key leq h ∧
  ((t,h') = remove_min_tree get_key leq h) 
  ⇒
  is_heap_ordered get_key leq h' ∧
  is_heap_ordered_tree get_key leq t ∧
  (heap_to_bag h = BAG_UNION (heap_to_bag h') (tree_to_bag t)) ∧
  (!y. BAG_IN y (heap_to_bag h') ⇒ leq (get_key (root t)) (get_key y))`,
induct_on `h` >>
rw [heap_to_bag_def] >>
cases_on `h` >>
cases_on `t` >>
full_simp_tac (srw_ss()++BAG_ss) 
              [root_def, remove_min_tree_def, heap_to_bag_def] >>
rw [is_heap_ordered_def] >>
fs [LET_THM, is_heap_ordered_def] >>
cases_on `remove_min_tree get_key leq (h'''::t')` >>
fs [] >>
every_case_tac >>
fs [] >>
rw [] >>
full_simp_tac (srw_ss()++BAG_ss) 
              [root_def, is_heap_ordered_def, heap_to_bag_def, 
               BAG_INSERT_UNION] >|
[metis_tac [is_heap_ordered_def],
 metis_tac [is_heap_ordered_def],
 `tree_to_bag h''' ⊎ heap_to_bag t' = heap_to_bag r ⊎ tree_to_bag (Node n a l)`
              by metis_tac [] >>
     srw_tac [BAG_ss] [heap_to_bag_def, BAG_INSERT_UNION],
 `BAG_IN y (tree_to_bag q) ∨ BAG_IN y (heap_to_bag r)`
        by metis_tac [BAG_IN_BAG_UNION] >|
     [`is_heap_ordered_tree get_key leq q` by metis_tac [] >>
          `leq (get_key (root q)) (get_key y)`
                  by (cases_on `q` >>
                      fs [BAG_EVERY, is_heap_ordered_def, root_def,
                          heap_to_bag_def] >>
                      metis_tac [WeakLinearOrder, WeakOrder, reflexive_def]) >>
          metis_tac [WeakLinearOrder, WeakOrder, transitive_def],
      fs [BAG_EVERY] >>
          metis_tac [WeakLinearOrder, WeakOrder, transitive_def]],
 `BAG_IN y (tree_to_bag q) ∨ BAG_IN y (heap_to_bag r)`
        by metis_tac [BAG_IN_BAG_UNION] >|
     [`is_heap_ordered_tree get_key leq q` by metis_tac [] >>
          `leq (get_key (root q)) (get_key y)`
                  by (cases_on `q` >>
                      fs [BAG_EVERY, is_heap_ordered_def, root_def,
                          heap_to_bag_def] >>
                      metis_tac [WeakLinearOrder, WeakOrder, reflexive_def]) >>
          metis_tac [WeakLinearOrder, WeakOrder, transitive_def],
      fs [BAG_EVERY] >>
          metis_tac [WeakLinearOrder, WeakOrder, transitive_def]],
 cases_on `h'` >>
     fs [root_def, is_heap_ordered_def, heap_to_bag_def, BAG_EVERY] >>
     metis_tac [WeakLinearOrder, WeakOrder, WeakLinearOrder_neg,
                transitive_def],
 metis_tac [WeakLinearOrder, WeakOrder, WeakLinearOrder_neg, root_def,
            transitive_def]]);

val find_min_correct = Q.store_thm ("find_min_correct",
`!h get_key leq. 
  WeakLinearOrder leq ∧ (h ≠ []) ∧ is_heap_ordered get_key leq h 
  ⇒
  BAG_IN (find_min get_key leq h) (heap_to_bag h) ∧
  (!y. BAG_IN y (heap_to_bag h) 
       ⇒ 
       leq (get_key (find_min get_key leq h)) (get_key y))`,
rw [find_min_def] >>
`(heap_to_bag h = BAG_UNION (heap_to_bag ts') (tree_to_bag t)) ∧
 (∀y. y ⋲ heap_to_bag ts' ⇒ leq (get_key (root t)) (get_key y)) ∧
 (is_heap_ordered_tree get_key leq t)`
        by metis_tac [remove_min_tree] >>
cases_on `t` >>
fs [BAG_EVERY, heap_to_bag_def, root_def, is_heap_ordered_def] >>
metis_tac [WeakLinearOrder, WeakOrder, reflexive_def]);

val reverse_heap_ordered = Q.prove (
`!get_key leq l. 
  is_heap_ordered get_key leq l ⇒ is_heap_ordered get_key leq (REVERSE l)`,
induct_on `l` >>
rw [is_heap_ordered_def] >>
res_tac >>
POP_ASSUM MP_TAC >>
Q.SPEC_TAC (`REVERSE l`, `l'`) >>
rw [] >>
induct_on `l'` >>
rw [is_heap_ordered_def]);

val append_bag = Q.prove (
`!h1 h2. heap_to_bag (h1++h2) = BAG_UNION (heap_to_bag h1) (heap_to_bag h2)`,
induct_on `h1` >>
srw_tac [BAG_ss] [heap_to_bag_def]);

val reverse_bag = Q.prove (
`!l. heap_to_bag (REVERSE l) = heap_to_bag l`,
induct_on `l` >>
srw_tac [BAG_ss] [append_bag, heap_to_bag_def]);

val delete_min_correct = Q.store_thm ("delete_min_correct",
`!h get_key leq.
  WeakLinearOrder leq ∧ (h ≠ []) ∧ is_heap_ordered get_key leq h
  ⇒
  is_heap_ordered get_key leq (delete_min get_key leq h) ∧
  (heap_to_bag (delete_min get_key leq h) =
   BAG_DIFF (heap_to_bag h) (EL_BAG (find_min get_key leq h)))`,
rw [delete_min_def] >>
every_case_tac >>
rw [merge_bag, reverse_bag] >-
metis_tac [reverse_heap_ordered, merge_heap_ordered, remove_min_tree,
           is_heap_ordered_def] >>
rw [find_min_def, root_def] >>
rw [root_def] >>
`(heap_to_bag h = BAG_UNION (heap_to_bag r) (tree_to_bag (Node n a l)))`
           by metis_tac [remove_min_tree] >>
rw [heap_to_bag_def, BAG_DIFF, BAG_INSERT, EL_BAG, FUN_EQ_THM, EMPTY_BAG,
    BAG_UNION] >>
cases_on `x = a` >>
srw_tac [ARITH_ss] []);

(* translation *)

val _ = set_filename (current_theory())

val _ = register_type ``:'a list``

(* register tree -- begin *)

(* val _ = register_type ``:'a tree`` *)

val ty = ``:'a tree``

val _ = delete_const "tree" handle _ => ()

val tm =
``tree a (Node x1_1 x1_2 x1_3) v ⇔
  ∃v1_1 v1_2 v1_3.
    (v = Conv (SOME "NODE") [v1_1; v1_2; v1_3]) ∧ NUM x1_1 v1_1 ∧
    a x1_2 v1_2 ∧ list (\x v. if MEM x x1_3 then tree a x v else ARB) x1_3 v1_3``

val inv_def = tDefine "tree_def" [ANTIQUOTE tm]
 (WF_REL_TAC `measure (tree_size (\x.0) o FST o SND)`
  THEN STRIP_TAC THEN Induct
  THEN EVAL_TAC THEN SIMP_TAC std_ss []
  THEN REPEAT STRIP_TAC THEN RES_TAC
  THEN FULL_SIMP_TAC std_ss [] THEN DECIDE_TAC)

val list_SIMP = prove(
  ``!xs b. list (\x v. if b x \/ MEM x xs then p x v else q) xs = list p xs``,
  Induct
  THEN FULL_SIMP_TAC std_ss [FUN_EQ_THM,fetch "-" "list_def",MEM,DISJ_ASSOC])
  |> Q.SPECL [`xs`,`\x.F`] |> SIMP_RULE std_ss [];

val inv_def = CONV_RULE (DEPTH_CONV ETA_CONV) (SIMP_RULE std_ss [list_SIMP] inv_def)

val _ = set_inv_def (ty,inv_def)

val _ = register_type ty

(* register tree -- end *)

val res = translate APPEND;
val res = translate REV_DEF;
val res = translate REVERSE_REV;
val res = translate is_empty_def;
val res = translate rank_def;
val res = translate link_def;
val res = translate ins_tree_def;
val res = translate insert_def;
val res = translate root_def;
val res = translate remove_min_tree_def;
val res = translate find_min_def;
val res = translate merge_def;
val res = translate delete_min_def;

val _ = export_theory ();
