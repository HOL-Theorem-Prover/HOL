Theory github234a[bare]
Libs
  HolKernel Parse boolLib

val _ = Globals.max_print_depth := 5;
val _ = overload_on("foo",``\t1 t2. !t. (t1 ==> t2 ==> t) ==> t``);

