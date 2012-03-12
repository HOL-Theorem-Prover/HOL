open bossLib Theory Parse boolTheory pairTheory Defn Tactic boolLib bagTheory
open relationTheory bagLib miscTheory lcsymtacs ml_translatorLib;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;

val _ = new_theory "BottomUpMergeSort"

(* Note, we're just cutting out the laziness since it shouldn't affect
 * functional correctness *)

val _ = type_abbrev ("sortable", ``:num # 'a list list``);

val mrg_def = Define `
(mrg leq [] ys = ys) ∧
(mrg leq xs [] = xs) ∧
(mrg leq (x::xs) (y::ys) =
  if leq x y then
    x :: mrg leq xs (y::ys)
  else
    y :: mrg leq (x::xs) ys)`;

val empty_def = Define `
empty = (0, [])`;

val add_seg_def = tDefine "add_seg" `
add_seg leq seg segs size =
  if size MOD 2 = 0 then
    seg::segs
  else
    add_seg leq (mrg leq seg (HD segs)) (TL segs) (size DIV 2)`
(wf_rel_tac `measure (\(x,y,z,s). s)` >>
 rw [] >>
 Cases_on `size = 0` >>
 full_simp_tac (srw_ss()++ARITH_ss) []);

val add_def = Define `
add leq x (size,segs) = (size+1, add_seg leq [x] segs size)`;

val mrg_all_def = Define `
(mrg_all leq xs [] = xs) ∧
(mrg_all leq xs (seg::segs) = mrg_all leq (mrg leq xs seg) segs)`;

val sort_def = Define `
sort leq size segs = mrg_all leq [] segs`;

val res = translate listTheory.TL
val res = translate listTheory.HD
val res = translate mrg_def
val res = translate empty_def
val res = translate mrg_all_def
val res = translate sort_def

(* Fails with
hol2deep failed at 'lookup_cert'

target:

TL

but derived:

TL
* 
val res = translate add_seg_def
val res = translate add_def
*)
val _ = export_theory();

