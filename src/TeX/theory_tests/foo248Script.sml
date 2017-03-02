open HolKernel boolLib bossLib Parse
val _ = new_theory"foo248"
val _ = Define`foo a b = a < b`
val _ = overload_on("<:",``\a b. foo b a``)
val _ = export_theory()
