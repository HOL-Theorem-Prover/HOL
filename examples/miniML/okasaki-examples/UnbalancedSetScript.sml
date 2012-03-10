open bossLib Theory Parse boolTheory pairTheory Defn Tactic boolLib 
open relationTheory miscTheory pred_setTheory lcsymtacs;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;

val _ = new_theory "UnbalancedSet"

val _ = Hol_datatype `
tree = Empty | Node of tree => 'a => tree`;

val empty_def = Define `
empty = Empty`;

val member_def = Define `
(member lt x Empty = F) ∧
(member lt x (Node a y b) =
  if lt x y then
    member lt x a
  else if lt y x then
    member lt x b
  else
    T)`;

val insert_def = Define `
(insert lt x Empty = Node Empty x Empty) ∧
(insert lt x (Node a y b) =
  if lt x y then
    Node (insert lt x a) y b
  else if lt y x then
    Node a y (insert lt x b)
  else
    Node a y b)`;

val _ = export_theory ();
