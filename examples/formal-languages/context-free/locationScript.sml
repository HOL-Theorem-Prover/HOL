Theory location

Datatype: locn = UNKNOWNpt | EOFpt | POSN num num
End

Definition locnrow_def:
  locnrow (POSN r c) = r
End
val _ = add_record_field ("row", “locnrow”)

Definition locn_rowupdate_def:
  locn_rowupdate f (POSN r c) = POSN (f r) c
End
val _ = add_record_fupdate ("row", “locn_rowupdate”)

Definition locncol_def:
  locncol (POSN r c) = c
End
val _ = add_record_field ("col", “locncol”)
Definition locn_colupdate_def:
  locn_colupdate f (POSN r c) = POSN r (f c)
End
val _ = add_record_fupdate ("col", “locn_colupdate”)

Datatype: locs = Locs locn locn
End

Definition default_loc_def:
  default_loc = POSN 0 0
End

Definition start_locs_def: start_locs = Locs default_loc default_loc
End

Overload end_locn[local] = “EOFpt”
Overload unknown_locn[local] = “UNKNOWNpt”

Definition unknown_loc_def:
  unknown_loc = Locs unknown_locn unknown_locn
End

Definition locnle_def:
  locnle l1 l2 <=>
    l1 = l2 ∨ (* reflexivity, for free *)
    l1 = unknown_locn ∨ (* minimal element *)
    l2 = end_locn ∨ (* maximal element *)
    (* otherwise compare row and col lexicographically*)
    l2 ≠ unknown_locn ∧ l1 ≠ end_locn ∧
    (l1.row < l2.row ∨ l1.row = l2.row ∧ l1.col < l2.col)
End

Theorem locnle_REFL[simp]:
  locnle l l
Proof
  simp[locnle_def]
QED

Theorem locnle_total:
  locnle l1 l2 ∨ locnle l2 l1
Proof
  simp[locnle_def] >> Cases_on ‘l1 = l2’ >> simp[] >>
  map_every Cases_on [‘l1 = unknown_locn’, ‘l2 = unknown_locn’,
                      ‘l1 = end_locn’, ‘l2 = end_locn’] >> simp[] >>
  reverse (Cases_on ‘l1.row = l2.row’) >> simp[] >>
  ‘l1.col ≠ l2.col’ suffices_by simp[] >>
  map_every Cases_on [‘l1’, ‘l2’] >> gvs[locnrow_def, locncol_def]
QED

Theorem locnle_ANTISYM:
  locnle l1 l2 ∧ locnle l2 l1 ⇒ l1 = l2
Proof
  map_every Cases_on [‘l1’, ‘l2’] >> gvs[locnle_def,locnrow_def, locncol_def]
QED

Theorem locnle_TRANS:
  locnle l1 l2 ∧ locnle l2 l3 ⇒ locnle l1 l3
Proof
  map_every Cases_on [‘l1’, ‘l2’, ‘l3’] >>
  gvs[locnle_def,locnrow_def, locncol_def]
QED

Theorem locnle_end[simp]:
  locnle end_locn l ⇔ l = end_locn
Proof
  simp[locnle_def]
QED

Theorem locnle_unknown[simp]:
  locnle l unknown_locn ⇔ l = unknown_locn
Proof
  simp[locnle_def]
QED

Definition locsle_def[simp]:
  locsle (Locs l1 _) (Locs l2 _) ⇔ locnle l1 l2
End

Theorem locsle_REFL[simp]:
  locsle l l
Proof
  Cases_on ‘l’ >> simp[]
QED

Theorem locsle_total:
  locsle l1 l2 ∨ locsle l2 l1
Proof
  map_every Cases_on [‘l1’, ‘l2’] >> simp[locnle_total]
QED

Theorem locsle_TRANS:
  locsle l1 l2 ∧ locsle l2 l3 ⇒ locsle l1 l3
Proof
  map_every Cases_on [‘l1’, ‘l2’, ‘l3’] >> simp[] >> metis_tac[locnle_TRANS]
QED

Definition merge_locs_def:
  merge_locs (Locs l1 l2) (Locs l3 l4) = Locs l1 l4
End

Definition merge_list_locs_def:
  (merge_list_locs [] = unknown_loc) /\
  (merge_list_locs (h :: []) = h) /\
  (merge_list_locs (h1 :: h2 :: []) = merge_locs h1 h2) /\
  (merge_list_locs (h1 :: h2 :: t) = merge_list_locs (h1 :: t))
End

(* for debugging *)

Definition map_loc_def[simp]:
  (map_loc [] _ = []) /\
  (map_loc (h :: t) n =
    (h, Locs (POSN 0 n) (POSN 0 n)) :: map_loc t (n+1))
End


Theorem merge_locs_assoc[simp]:
  (merge_locs (merge_locs l1 l2) l3 = merge_locs l1 l3) ∧
  (merge_locs l1 (merge_locs l2 l3) = merge_locs l1 l3)
Proof
  map_every Cases_on [`l1`, `l2`, `l3`] >> simp[merge_locs_def]
QED

Theorem merge_list_locs_2[simp]:
  ∀h1 h2 t.
    merge_list_locs (h1 :: h2 :: t) = merge_list_locs (merge_locs h1 h2 :: t)
Proof
  Induct_on ‘t’ >> simp[merge_list_locs_def]
QED

Theorem merge_list_locs_nested[simp]:
  ∀h t1 t2. merge_list_locs (merge_list_locs (h::t1) :: t2) =
            merge_list_locs (h :: t1 ++ t2)
Proof
  Induct_on ‘t1’ >> simp[merge_list_locs_def]
QED

Theorem merge_list_locs_sing[simp]:
   merge_list_locs [h] = h
Proof
  simp[merge_list_locs_def]
QED

Theorem merge_locs_idem[simp]:
   merge_locs l l = l
Proof
  Cases_on ‘l’ >> simp[merge_locs_def]
QED

