open bossLib Theory Parse boolTheory pairTheory Defn Tactic boolLib bagTheory
open relationTheory bagLib miscTheory lcsymtacs;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;

val _ = new_theory "BinomialHeap"

val _ = Hol_datatype `
tree = Node of num => 'a => tree list`;

val _ = type_abbrev ("heap", ``:'a tree list``);

val _ = Define `
empty = []`;

val is_empty = Define `
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

val _ = export_theory ();
