open HolKernel Parse boolLib

open github130Lib
val _ = new_theory "github130a";

val foo_def = new_definition("foo_def", ``foo f x = f x``)
val _ = export_gh130 "foo_def"
val _ = Feedback.WARNINGs_as_ERRs := false
val _ = delete_const "foo"


val _ = export_theory();
