open bossLib Theory Parse boolTheory pairTheory Defn Tactic boolLib bagTheory
open relationTheory bagLib miscTheory lcsymtacs;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;

val _ = new_theory "LazyPairingHeap"

(* Note, we're just cutting out the laziness since it shouldn't affect
 * functional correctness *)

val _ = Hol_datatype `
heap = Empty | Node of 'a => heap => heap`;

val _ = Define `
empty = Empty`;

val is_empty = Define `
(is_empty Empty = T) ∧
(is_empty _ = F)`;

(*
val merge_def = Define `
(merge get_key leq a Empty = a) ∧
(merge get_key leq Empty b = b) ∧
(merge get_key leq (Node x h1 h2) (Node y h1' h2') =
  if leq (get_key x) (get_key y) then
    link get_key leq (Node x h1 h2) (Node y h1' h2')
  else
    link get_key leq (Node y h1' h2') (Node x h1 h2)) ∧

(link get_key leq (Node x Empty m) a = Node x a m) ∧
(link get_key leq (Node x b m) a = 
  Node x Empty (merge get_key leq (merge get_key leq a b) m))`;
*)

(* Without mutual recursion *)

val merge_defn = Hol_defn "merge" `
(merge get_key leq a Empty = a) ∧
(merge get_key leq Empty b = b) ∧
(merge get_key leq (Node x h1 h2) (Node y h1' h2') =
  if leq (get_key x) (get_key y) then
    case h1 of
       | Empty => Node x (Node y h1' h2') h2
       | _ => Node x Empty (merge get_key leq (merge get_key leq (Node y h1' h2') h1) h2)
  else
    case h1' of
       | Empty => Node y (Node x h1 h2) h2'
       | _ => Node y Empty (merge get_key leq (merge get_key leq (Node x h1 h2) h1') h2'))`;

val _ = Defn.save_defn merge_defn;

val insert_def = Define `
insert get_key leq x a = merge get_key leq (Node x Empty Empty) a`;

val find_min_def = Define `
find_min (Node x _ _) = x`;

val delete_min_def = Define `
delete_min get_key leq (Node _ a b) = merge get_key leq a b`;

val _ = export_theory ();
