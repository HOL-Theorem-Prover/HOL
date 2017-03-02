open HolKernel Parse boolLib

val _ = new_theory "github234a";

val _ = Globals.max_print_depth := 5
val _ = overload_on("foo",``\t1 t2. !t. (t1 ==> t2 ==> t) ==> t``)

val _ = export_theory();
