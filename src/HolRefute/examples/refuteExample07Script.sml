(* HolRefute by example, 7: datatype invariants. *)

Theory refuteExample07
Ancestors
  string
Libs
  Refute

Datatype:
  interval = <| lo : num; hi : num |>
End

Definition valid_interval_def:
  valid_interval i <=> i.lo <= i.hi
End

(* A datatype generator knows the representation, not an application-level
   invariant.  State the invariant as an assumption in the conjecture. *)

Theorem every_raw_interval_is_valid:
  valid_interval i
Proof
  QUICKCHECK_TAC >> cheat
QED

Theorem a_valid_interval_need_not_be_a_singleton:
  valid_interval i ==> i.lo = i.hi
Proof
  QUICKCHECK_TAC >> cheat
QED

Theorem an_interval_contains_its_lower_endpoint:
  valid_interval i ==> i.lo <= i.lo /\ i.lo <= i.hi
Proof
  REFUTE_TAC >>
  simp [valid_interval_def]
QED

Datatype:
  labelled = <| label : string; payload : num list |>
End

Definition well_formed_def:
  well_formed x <=> x.label <> "" /\ x.payload <> []
End

Theorem well_formed_values_need_not_have_one_payload_item:
  well_formed x ==> LENGTH x.payload = 1
Proof
  QUICKCHECK_TAC >> cheat
QED
