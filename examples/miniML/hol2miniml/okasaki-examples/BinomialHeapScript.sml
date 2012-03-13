open HolKernel Parse;
open bossLib Theory Parse boolTheory pairTheory Defn Tactic boolLib bagTheory
open relationTheory bagLib miscTheory lcsymtacs listTheory;
open ml_translatorLib;

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
