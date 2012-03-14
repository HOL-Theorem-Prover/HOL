open preamble
open miscTheory ml_translatorLib;

val _ = new_theory "BottomUpMergeSort"

(* Okasaki page 77 *)

(* Note, we're following Chargueraud and just cutting out the laziness since it
 * shouldn't affect functional correctness *)

val _ = type_abbrev ("sortable", ``:num # 'a list list``);

val mrg_def = mlDefine `
(mrg leq [] ys = ys) ∧
(mrg leq xs [] = xs) ∧
(mrg leq (x::xs) (y::ys) =
  if leq x y then
    x :: mrg leq xs (y::ys)
  else
    y :: mrg leq (x::xs) ys)`;

val empty_def = mlDefine `
empty = (0, [])`;

val _ = translate listTheory.TL
val _ = translate listTheory.HD

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

val _ = translate add_seg_def;

val add_def = mlDefine `
add leq x (size,segs) = (size+1, add_seg leq [x] segs size)`;

val mrg_all_def = mlDefine `
(mrg_all leq xs [] = xs) ∧
(mrg_all leq xs (seg::segs) = mrg_all leq (mrg leq xs seg) segs)`;

val sort_def = mlDefine `
sort leq size segs = mrg_all leq [] segs`;


(* translation *)

(*val _ = set_filename (current_theory())*)

val _ = export_theory();

