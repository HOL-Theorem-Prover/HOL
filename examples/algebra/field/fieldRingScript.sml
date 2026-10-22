Theory fieldRing
Ancestors
  field ringLib

(* Keep the field dependency on this side of the ring automation interface. *)
Theorem field_toRing_div:
    Ring r ==> ring_div (toRing r) x y = field_div r x y
Proof
    simp [ring_div_def, toRing_operations, field_div_def]
QED

Theorem FIELD_INV:
    Field r ==> !x.
      x IN ring_carrier (toRing r) /\ x <> ring_0 (toRing r) ==>
      ring_inv (toRing r) x IN ring_carrier (toRing r)
Proof
    rw [toRing_operations] >>
    metis_tac [field_inv_element, field_nonzero_eq]
QED

Theorem FIELD_MUL_LINV:
    Field r ==> !x.
      x IN ring_carrier (toRing r) /\ x <> ring_0 (toRing r) ==>
      ring_mul (toRing r) (ring_inv (toRing r) x) x = ring_1 (toRing r)
Proof
    rw [toRing_operations] >>
    metis_tac [field_mult_linv, field_nonzero_eq]
QED

Theorem FIELD_MUL_RINV:
    Field r ==> !x.
      x IN ring_carrier (toRing r) /\ x <> ring_0 (toRing r) ==>
      ring_mul (toRing r) x (ring_inv (toRing r) x) = ring_1 (toRing r)
Proof
    rw [toRing_operations] >>
    metis_tac [field_mult_rinv, field_nonzero_eq]
QED
