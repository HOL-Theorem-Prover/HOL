open preamble
open miscTheory sortingTheory ml_translatorLib;

val _ = new_theory "BottomUpMergeSort"

(* Okasaki page 77 *)

(* Note, we're following Chargueraud and just cutting out the laziness since it
 * shouldn't affect functional correctness *)

val _ = type_abbrev ("sortable", ``:num # 'a list list``);

val sortable_inv_def = tDefine "sortable_inv" `
(sortable_inv leq (n,[]) m = (n = 0)) ∧
(sortable_inv leq (n,xs::xss) m =
  if (n = 0) then
    F
  else if n MOD 2 = 0 then 
    sortable_inv leq (n DIV 2,xs::xss) (m * 2)
  else 
    (LENGTH xs = m) ∧
    SORTED leq xs ∧
    sortable_inv leq (n DIV 2, xss) (m * 2))`
(wf_rel_tac `measure (\(x,(y,z),s). y)` >>
 rw [] >>
 Cases_on `n = 0` >>
 full_simp_tac (srw_ss()++ARITH_ss) []);

val sortable_inv_ind = fetch "-" "sortable_inv_ind"

val mrg_def = mlDefine `
(mrg leq [] ys = ys) ∧
(mrg leq xs [] = xs) ∧
(mrg leq (x::xs) (y::ys) =
  if leq x y then
    x :: mrg leq xs (y::ys)
  else
    y :: mrg leq (x::xs) ys)`;

val mrg_ind = fetch "-" "mrg_ind"

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

val add_seg_ind = fetch "-" "add_seg_ind"

val _ = translate add_seg_def;

val add_def = mlDefine `
add leq x (size,segs) = (size+1, add_seg leq [x] segs size)`;

val mrg_all_def = mlDefine `
(mrg_all leq xs [] = xs) ∧
(mrg_all leq xs (seg::segs) = mrg_all leq (mrg leq xs seg) segs)`;

val sort_def = mlDefine `
sort leq (size, segs) = mrg_all leq [] segs`;



(* Functional correctness *)

val mrg_sorted = Q.prove (
`!leq xs ys. 
  WeakLinearOrder leq ∧ SORTED leq xs ∧ SORTED leq ys 
  ⇒ 
  SORTED leq (mrg leq xs ys)`,
recInduct mrg_ind >>
rw [SORTED_DEF,mrg_def] >|
[cases_on `xs`, cases_on `ys`] >>
fs [SORTED_DEF, mrg_def] >>
every_case_tac >>
fs [SORTED_DEF] >>
metis_tac [WeakLinearOrder_neg]);

val mrg_perm = Q.prove (
`!leq xs ys. PERM (mrg leq xs ys) (xs++ys)`,
recInduct mrg_ind >>
rw [mrg_def] >>
metis_tac [PERM_FUN_APPEND, PERM_CONS_IFF, CONS_PERM, PERM_SWAP_AT_FRONT,
           PERM_TRANS, PERM_REFL]);

val mrg_length = Q.prove (
`!leq xs ys. LENGTH (mrg leq xs ys) = LENGTH xs + LENGTH ys`,
recInduct mrg_ind >>
srw_tac [ARITH_ss] [mrg_def]);

val odd_div_add1 = mk_thm ([],
``!n:num. ~EVEN n ⇒ (n DIV 2 + 1 = (n + 1) DIV 2)``);

val add_seg_sub_inv = Q.prove (
`!leq size segs n seg. 
  WeakLinearOrder leq ∧
  (n ≠ 0) ∧
  sortable_inv leq (size,segs) n ∧ 
  SORTED leq seg ∧
  (LENGTH seg = n)
  ⇒
  sortable_inv leq (size+1, add_seg leq seg segs size) n`,
recInduct sortable_inv_ind >>
rw [] >|
[fs [Once sortable_inv_def] >>
     rw [Once add_seg_def] >>
     rw [Once sortable_inv_def] >>
     rw [Once sortable_inv_def],
 `n ≠ 0` by fs [Once sortable_inv_def] >>
     cases_on `n MOD 2 = 0` >>
     fs [] >>
     fs [Once sortable_inv_def] >>
     rw [Once add_seg_def] >>
     rw [Once sortable_inv_def] >|
     [fs [arithmeticTheory.MOD_2] >>
          every_case_tac >>
          fs [arithmeticTheory.EVEN_ADD],
      `0 < 2:num` by rw [] >>
          `(n+1) DIV 2 = n DIV 2 + 1 DIV 2`  
                     by metis_tac [arithmeticTheory.ADD_DIV_RWT] >>
          fs [],
      `LENGTH seg + LENGTH xs = LENGTH seg * 2`
                    by decide_tac >>
          `sortable_inv leq (n DIV 2 +  1, 
                             add_seg leq (mrg leq seg xs) xss (n DIV 2)) 
                        (LENGTH seg * 2)`
                    by metis_tac [mrg_sorted, mrg_length] >>
          cases_on `add_seg leq (mrg leq seg xs) xss (n DIV 2)` >>
          fs [] >-
          fs [Once sortable_inv_def] >>
          rw [Once sortable_inv_def] >>
          fs [arithmeticTheory.MOD_2] >>
          every_case_tac >>
          fs [arithmeticTheory.EVEN_ADD] >>
          metis_tac [odd_div_add1]]]);

val add_correct = Q.store_thm ("add_correct",
`!leq x size segs. 
  WeakLinearOrder leq ∧ sortable_inv leq (size,segs) 1
  ⇒ 
  sortable_inv leq (add leq x (size,segs)) 1`,
rw [add_def] >>
match_mp_tac add_seg_sub_inv >>
rw [SORTED_DEF]);


(* translation *)

(*val _ = set_filename (current_theory())*)

val _ = export_theory();

