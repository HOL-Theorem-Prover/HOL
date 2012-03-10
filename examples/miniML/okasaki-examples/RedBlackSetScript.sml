open bossLib Theory Parse boolTheory pairTheory Defn Tactic boolLib 
open relationTheory miscTheory pred_setTheory lcsymtacs;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;

val _ = new_theory "RedBlackSet"

val _ = Hol_datatype `
color = Red | Black`;

val _ = Hol_datatype `
tree = Empty | Node of color => tree => 'a => tree`;

val empty_def = Define `
empty = Empty`;

val member_def = Define `
(member lt x Empty = F) ∧
(member lt x (Node _ a y b) =
  if lt x y then
    member lt x a
  else if lt y x then
    member lt x b
  else
    T)`;

val balance_def = Define `
(balance Black (Node Red (Node Red a x b) y c) z d =
  Node Red (Node Black a x b) y (Node Black c z d)) ∧

(balance Black (Node Red a x (Node Red b y c)) z d =
  Node Red (Node Black a x b) y (Node Black c z d)) ∧

(balance Black a x (Node Red (Node Red b y c) z d) =
  Node Red (Node Black a x b) y (Node Black c z d)) ∧

(balance Black a x (Node Red b y (Node Red c z d)) =
  Node Red (Node Black a x b) y (Node Black c z d)) ∧

(balance col a x b = Node col a x b)`;

val ins_def = Define `
(ins lt x Empty = Node Red Empty x Empty) ∧
(ins lt x (Node col a y b) =
  if lt x y then
    balance col (ins lt x a) y b
  else if lt y x then
    balance col a y (ins lt x b)
  else
    Node col a y b)`;

val insert_def = Define `
insert lt x s =
  case ins lt x s of
     | Node _ a y b => Node Black a y b`;

val _ = export_theory ();
