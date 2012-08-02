open HolKernel boolLib Parse

open fooTheory

val _ = new_theory "bar"

val f_def = new_definition(
  "f_def",
  ``f x = x + 1``);

val _ = export_theory()
