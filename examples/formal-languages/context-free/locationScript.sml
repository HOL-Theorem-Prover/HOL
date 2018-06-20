open HolKernel Parse boolLib bossLib

val _ = new_theory "location";

val _ = Datatype `
 locn = <| row : num;  col : num; offset : num |>`;

val _ = Datatype `
  locs = Locs locn locn
`

val default_loc_def = Define`
  default_loc = <| row := 1; col := 1; offset := 0 |>`;

val start_loc_def = Define`
  start_loc = (default_loc,default_loc)`;

val unknown_loc_def = Define`
  unknown_loc = Locs <| row := 0; col := 0; offset := 0 |>
                     <| row := 0; col := 0; offset := 0 |>`;
val merge_locs_def = Define`
  merge_locs (Locs l1 l2) (Locs l3 l4) = Locs l1 l4
`;

val merge_list_locs_def = Define`
  (merge_list_locs [] = unknown_loc) /\
  (merge_list_locs (h :: []) = h) /\
  (merge_list_locs (h1 :: h2 :: []) = merge_locs h1 h2) /\
  (merge_list_locs (h1 :: h2 :: t) = merge_list_locs (h1 :: t))`;

(* for debugging *)

val map_loc_def = Define`
  (map_loc [] _ = []) /\
  (map_loc (h :: t) n =
    (h, Locs <| row := n; col := 0; offset := 0 |>
             <| row := n; col := 1; offset := 0 |>) :: map_loc t (n+1))
`;


val merge_locs_assoc = Q.store_thm(
  "merge_locs_assoc[simp]",
  ‘(merge_locs (merge_locs l1 l2) l3 = merge_locs l1 l3) ∧
   (merge_locs l1 (merge_locs l2 l3) = merge_locs l1 l3)’,
  map_every Cases_on [`l1`, `l2`, `l3`] >>
  simp[merge_locs_def]);

val merge_list_locs_2 = Q.store_thm(
  "merge_list_locs_2[simp]",
  ‘∀h1 h2 t.
     merge_list_locs (h1 :: h2 :: t) = merge_list_locs (merge_locs h1 h2 :: t)’,
  Induct_on ‘t’ >> simp[merge_list_locs_def]);

val merge_list_locs_nested = Q.store_thm(
  "merge_list_locs_nested[simp]",
  ‘∀h t1 t2. merge_list_locs (merge_list_locs (h::t1) :: t2) =
             merge_list_locs (h :: t1 ++ t2)’,
  Induct_on ‘t1’ >> simp[merge_list_locs_def]);

val merge_list_locs_sing = Q.store_thm(
  "merge_list_locs_sing[simp]",
  ‘merge_list_locs [h] = h’,
  simp[merge_list_locs_def]);

val merge_locs_idem = Q.store_thm(
  "merge_locs_idem[simp]",
  ‘merge_locs l l = l’,
  Cases_on ‘l’ >> simp[merge_locs_def]);

val _ = export_theory();
