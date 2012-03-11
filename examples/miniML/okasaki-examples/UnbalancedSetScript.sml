open bossLib Theory Parse boolTheory pairTheory Defn Tactic boolLib 
open relationTheory miscTheory pred_setTheory pred_setSimps lcsymtacs;

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

val unbalanced_set_to_set_def = Define `
(unbalanced_set_to_set Empty = {}) ∧
(unbalanced_set_to_set (Node t1 x t2)  =
  {x} ∪ unbalanced_set_to_set t1 ∪ unbalanced_set_to_set t2)`;

val unbalanced_set_ok_def = Define `
(unbalanced_set_ok lt Empty = T) ∧
(unbalanced_set_ok lt (Node t1 x t2) = 
  unbalanced_set_ok lt t1 ∧
  unbalanced_set_ok lt t2 ∧
  (!y. y ∈ unbalanced_set_to_set t1 ⇒ lt y x) ∧
  (!y. y ∈ unbalanced_set_to_set t2 ⇒ lt x y))`;

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

val member_thm = Q.store_thm ("member_thm",
`!lt t x. 
  StrongLinearOrder lt ∧
  unbalanced_set_ok lt t 
  ⇒ 
  (member lt x t = x ∈ unbalanced_set_to_set t)`,
induct_on `t` >>
rw [member_def, unbalanced_set_ok_def, unbalanced_set_to_set_def] >>
fs [StrongLinearOrder, StrongOrder, irreflexive_def, transitive_def,
    trichotomous] >>
metis_tac []);

val insert_def = Define `
(insert lt x Empty = Node Empty x Empty) ∧
(insert lt x (Node a y b) =
  if lt x y then
    Node (insert lt x a) y b
  else if lt y x then
    Node a y (insert lt x b)
  else
    Node a y b)`;

val insert_set = Q.store_thm ("insert_set",
`∀lt x t.
  StrongLinearOrder lt ⇒
  (unbalanced_set_to_set (insert lt x t) = {x} ∪ unbalanced_set_to_set t)`,
induct_on `t` >>
srw_tac [PRED_SET_AC_ss] [insert_def, unbalanced_set_to_set_def] >>
`x = a` by (fs [StrongLinearOrder, StrongOrder, irreflexive_def, 
                transitive_def, trichotomous] >>
            metis_tac []) >>
rw []);

val insert_ok = Q.store_thm ("insert_ok",
`!lt x t.
  StrongLinearOrder lt ∧
  unbalanced_set_ok lt t 
  ⇒ 
  unbalanced_set_ok lt (insert lt x t)`,
induct_on `t` >>
rw [unbalanced_set_ok_def, insert_def, unbalanced_set_to_set_def, insert_set] >>
metis_tac []);

val _ = export_theory ();
