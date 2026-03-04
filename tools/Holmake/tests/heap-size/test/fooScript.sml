open HolKernel boolLib

val _ = new_theory "foo"

val foo_def = Definition.new_definition("foo_def", ``foo = T``)

val _ = export_theory()
