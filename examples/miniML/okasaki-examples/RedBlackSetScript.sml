open bossLib Theory Parse boolTheory pairTheory Defn Tactic boolLib
open relationTheory miscTheory pred_setTheory pred_setSimps lcsymtacs;
open ml_translatorLib

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

val tree_distinct = fetch "-" "tree_distinct"
val tree_nchotomy = fetch "-" "tree_nchotomy"

val redblack_set_to_set_def = Define `
(redblack_set_to_set Empty = {}) ∧
(redblack_set_to_set (Node _ t1 x t2)  =
  {x} ∪ redblack_set_to_set t1 ∪ redblack_set_to_set t2)`;

val redblack_set_ok_def = Define `
(redblack_set_ok lt Empty = T) ∧
(redblack_set_ok lt (Node _ t1 x t2) =
  redblack_set_ok lt t1 ∧
  redblack_set_ok lt t2 ∧
  (!y. y ∈ redblack_set_to_set t1 ⇒ lt y x) ∧
  (!y. y ∈ redblack_set_to_set t2 ⇒ lt x y))`;

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

val member_thm = Q.store_thm ("member_thm",
`!lt t x.
  StrongLinearOrder lt ∧
  redblack_set_ok lt t
  ⇒
  (member lt x t = x ∈ redblack_set_to_set t)`,
induct_on `t` >>
rw [member_def, redblack_set_ok_def, redblack_set_to_set_def] >>
fs [StrongLinearOrder, StrongOrder, irreflexive_def, transitive_def,
    trichotomous] >>
metis_tac []);


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

val balance_ind = fetch "-" "balance_ind"

(*
val balance_left_def = Define `
(balance_left Black (Node Red (Node Red a x b) y c) z d =
  SOME (Node Red (Node Black a x b) y (Node Black c z d))) ∧

(balance_left Black (Node Red a x (Node Red b y c)) z d =
  SOME (Node Red (Node Black a x b) y (Node Black c z d))) ∧

(balance_left col a x b = NONE)`;

val balance_right_def = Define `
(balance_right Black a x (Node Red (Node Red b y c) z d) =
  SOME (Node Red (Node Black a x b) y (Node Black c z d))) ∧

(balance_right Black a x (Node Red b y (Node Red c z d)) =
  SOME (Node Red (Node Black a x b) y (Node Black c z d))) ∧

(balance_right col a x b = NONE)`;
*)

val balance_node = Q.prove (
`!c t1 x t2. ∃c' t1' x' t2'. (balance c t1 x t2 = Node c' t1' x' t2')`,
recInduct balance_ind >>
srw_tac [PRED_SET_AC_ss] [balance_def]);

val balance_set = Q.prove (
`!c t1 x t2.
  redblack_set_to_set (balance c t1 x t2) =
  redblack_set_to_set (Node c t1 x t2)`,
recInduct balance_ind >>
srw_tac [PRED_SET_AC_ss] [balance_def, redblack_set_to_set_def]);

val balance_ok = Q.prove (
`!c t1 x t2.
  transitive lt ∧
  redblack_set_ok lt (Node c t1 x t2) ⇒
  redblack_set_ok lt (balance c t1 x t2)`,
recInduct balance_ind >>
rw [transitive_def, balance_def, redblack_set_ok_def, redblack_set_to_set_def] >>
metis_tac []);

val ins_def = Define `
(ins lt x Empty = Node Red Empty x Empty) ∧
(ins lt x (Node col a y b) =
  if lt x y then
    balance col (ins lt x a) y b
  else if lt y x then
    balance col a y (ins lt x b)
  else
    Node col a y b)`;

val ins_node = Q.prove (
`!lt x t. ?c t1 y t2. (ins lt x t = Node c t1 y t2)`,
cases_on `t` >>
rw [ins_def] >>
metis_tac [balance_node]);

val ins_set = Q.prove (
`∀lt x t.
  StrongLinearOrder lt ⇒
  (redblack_set_to_set (ins lt x t) = {x} ∪ redblack_set_to_set t)`,
induct_on `t` >>
rw [redblack_set_to_set_def, ins_def, balance_set] >>
fs [] >>
srw_tac [PRED_SET_AC_ss] [] >>
`x = a` by (fs [StrongLinearOrder, StrongOrder, irreflexive_def,
                transitive_def, trichotomous] >>
            metis_tac []) >>
rw []);

val ins_ok = Q.prove (
`!lt x t.
  StrongLinearOrder lt ∧
  redblack_set_ok lt t
  ⇒
  redblack_set_ok lt (ins lt x t)`,
induct_on `t` >>
rw [redblack_set_ok_def, ins_def, redblack_set_to_set_def] >>
match_mp_tac balance_ok >>
rw [redblack_set_ok_def] >>
imp_res_tac ins_set >>
fs [StrongLinearOrder, StrongOrder]);

val insert_def = Define `
insert lt x s =
  case ins lt x s of
     | Node _ a y b => Node Black a y b`;

val insert_set = Q.store_thm ("insert_set",
`∀lt x t.
  StrongLinearOrder lt ⇒
  (redblack_set_to_set (insert lt x t) = {x} ∪ redblack_set_to_set t)`,
rw [insert_def] >>
`?c t1 y t2. ins lt x t = Node c t1 y t2` by metis_tac [ins_node] >>
rw [redblack_set_to_set_def] >>
`redblack_set_to_set (ins lt x t) = redblack_set_to_set (Node c t1 y t2)`
         by metis_tac [] >>
fs [] >>
imp_res_tac ins_set >>
fs [redblack_set_to_set_def]);

val insert_ok = Q.store_thm ("insert_ok",
`!lt x t.
  StrongLinearOrder lt ∧
  redblack_set_ok lt t
  ⇒
  redblack_set_ok lt (insert lt x t)`,
rw [insert_def] >>
`?c t1 y t2. ins lt x t = Node c t1 y t2` by metis_tac [ins_node] >>
rw [] >>
`redblack_set_ok lt (Node c t1 y t2)` by metis_tac [ins_ok] >>
fs [redblack_set_ok_def]);


(* translating balance *)

val balance_def = Define `
  balance col a x b =
    if col = Black then
      case (a,x,b) of
      | ((Node Red (Node Red a x b) y c),z,d) =>
        Node Red (Node Black a x b) y (Node Black c z d)
      | ((Node Red a x (Node Red b y c)),z,d) =>
        Node Red (Node Black a x b) y (Node Black c z d)
      | (a,x,(Node Red (Node Red b y c) z d)) =>
        Node Red (Node Black a x b) y (Node Black c z d)
      | (a,x,(Node Red b y (Node Red c z d))) =>
        Node Red (Node Black a x b) y (Node Black c z d)
      | _ =>
        Node col a x b
    else Node col a x b`

val _ = translate balance_def;

(*

val _ = translate member_def;
val _ = translate ins_def;
val _ = translate insert_def;

*)

val _ = export_theory ();
