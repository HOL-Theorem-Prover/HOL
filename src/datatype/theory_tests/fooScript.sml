open HolKernel Parse boolLib Datatype

val _ = new_theory "foo"

val _ = Hol_datatype`foo = Success | Failure`

val _ = export_theory()
