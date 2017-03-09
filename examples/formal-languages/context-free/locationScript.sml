open HolKernel Parse boolLib bossLib

val _ = new_theory "location";

val _ = Hol_datatype `
 locn = <| row : num;  col : num; offset : num |>`;

val _ = type_abbrev ("locs", ``:locn # locn``);

val default_loc_def = Define`
  default_loc = <| row := 1; col := 1; offset := 0 |>`;

val start_loc_def = Define`
  start_loc = (default_loc,default_loc)`;

val unknown_loc_def = Define`
  unknown_loc = (<| row := 0; col := 0; offset := 0 |>,
                 <| row := 0; col := 0; offset := 0 |>)`;
val merge_locs_def = Define`
  merge_locs (l1 :locn, l2 : locn) (l3 : locn, l4 : locn) = (l1, l4)`;

val merge_list_locs_def = Define`
  (merge_list_locs [] = unknown_loc) /\
  (merge_list_locs (h :: []) = h) /\
  (merge_list_locs (h1 :: h2 :: []) = merge_locs h1 h2) /\
  (merge_list_locs (h1 :: h2 :: t) = merge_list_locs (h1 :: t))`;

(* for debugging *)

val map_loc_def = Define`
  (map_loc [] _ = []) /\
  (map_loc (h :: t) n = (h, (<| row := n; col := 0; offset := 0 |>,
                             <| row := n; col := 1; offset := 0 |>)) ::
                        map_loc t (n+1))     `;

val _ = export_theory();



