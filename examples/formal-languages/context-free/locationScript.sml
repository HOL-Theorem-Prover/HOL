open HolKernel Parse boolLib bossLib

val _ = new_theory "location";

Datatype: locn = <| row : num;  col : num; offset : num |>
End

Datatype: locs = Locs locn locn
End

Definition default_loc_def:
  default_loc = <| row := 1; col := 1; offset := 0 |>
End

Definition start_locs_def: start_locs = Locs default_loc default_loc
End

Definition end_locn_def:
  end_locn = <| row := 0; col := 0; offset := 1 |>
End

Definition unknown_locn_def:
  unknown_locn = <| row := 0; col := 0; offset := 0 |>
End

Definition unknown_loc_def:
  unknown_loc = Locs unknown_locn unknown_locn
End

Definition locnle_def:
  locnle l1 l2 <=>
    l1 = l2 ∨ (* reflexivity, for free *)
    l1 = default_loc ∨ (* minimal element *)
    l2 = end_locn ∨ (* maximal element *)
    (* otherwise compare row and col lexicographically*)
    l1.row ≠ 0 ∧ l2.row ≠ 0 ∧ l1.col ≠ 0 ∧ l2.col ≠ 0 ∧
    (l1.row < l2.row ∨ l1.row = l2.row ∧ l1.col < l2.col)
End

Theorem locn_rwts[simp]:
  default_loc ≠ end_locn ∧ default_loc ≠ unknown_locn ∧
  end_locn ≠ unknown_locn ∧ end_locn.row = 0 ∧
  unknown_locn.row = 0 ∧ default_loc.row = 1 ∧ default_loc.col = 1
Proof
  simp[default_loc_def, end_locn_def, unknown_locn_def]
QED

Theorem locnle_REFL[simp]:
  locnle loc loc
Proof simp[locnle_def]
QED

Theorem locnle_TRANS:
  locnle l1 l2 ∧ locnle l2 l3 ⇒ locnle l1 l3
Proof
  rw[locnle_def] >> fs[]
QED

Theorem locnle_end[simp]:
  locnle end_locn l ⇔ l = end_locn
Proof
  simp[locnle_def]
QED

Theorem locnle_start[simp]:
  locnle l default_loc ⇔ l = default_loc
Proof
  simp[locnle_def]
QED

Definition locsle_def:
  locsle (Locs l1 _) (Locs l2 _) ⇔ locnle l1 l2
End

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
