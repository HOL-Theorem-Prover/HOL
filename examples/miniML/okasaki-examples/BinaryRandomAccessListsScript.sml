open bossLib Theory Parse boolTheory pairTheory Defn Tactic boolLib 
open relationTheory miscTheory pred_setTheory lcsymtacs;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;

val _ = new_theory "BinaryRandomAccessLists"

val _ = Hol_datatype `
tree = Leaf of 'a | Node of num => tree => tree`;

val _ = Hol_datatype `
digit = Zero | One of 'a tree`;

val _ = type_abbrev ("rlist", ``:'a digit list``);

val empty_def = Define `
empty = []`;

val is_empty_def = Define `
(is_empty [] = T) ∧
(is_empty _ = F)`;

val size_def = Define `
(size (Leaf _) = 1) ∧
(size (Node w _ _) = w)`;

val link_def = Define `
(link t1 t2 = Node (size t1 + size t2) t1 t2)`;

val cons_tree_def = Define `
(cons_tree t [] = [One t]) ∧
(cons_tree t (Zero :: ts) = One t :: ts) ∧
(cons_tree t (One t' :: ts) = Zero :: cons_tree (link t t') ts)`;

val uncons_tree_def = Define `
(uncons_tree [One t] = (t, [])) ∧
(uncons_tree (One t::ts) = (t, Zero :: ts)) ∧
(uncons_tree (Zero :: ts) = 
  case uncons_tree ts of
    | (Node _ t1 t2, ts') => (t1, One t2 :: ts'))`;

val cons_def = Define `
cons x ts = cons_tree (Leaf x) ts`;

val head_def = Define `
head ts =
  case uncons_tree ts of
    | (Leaf x, _) => x`;

val tail_def = Define `
tail ts = let (x,ts') = uncons_tree ts in ts'`;

val lookup_tree_def = Define `
(lookup_tree i (Leaf x) = if i = 0 then x else ARB) ∧
(lookup_tree i (Node w t1 t2) =
  if i < w DIV 2  then 
    lookup_tree i t1
  else 
    lookup_tree (i - w DIV 2) t2)`;

val update_tree_def = Define `
(update_tree i y (Leaf x) = if i = 0 then Leaf y else ARB) ∧
(update_tree i y (Node w t1 t2) =
  if i < w DIV 2 then 
    Node w (update_tree i y t1) t2
  else 
    Node w t1 (update_tree (i - w DIV 2) y t2))`;

val lookup_def = Define `
(lookup i (Zero::ts) = lookup i ts) ∧
(lookup i (One t::ts) =
  if i < size t then 
    lookup_tree i t
  else 
    lookup (i - size t) ts)`;

val update_def = Define `
(update i y (Zero::ts) = Zero::update i y ts) ∧
(update i y (One t::ts) =
  if i < size t then
    One (update_tree i y t) :: ts
  else
    One t :: update (i - size t) y ts)`;

val _ = export_theory ();
