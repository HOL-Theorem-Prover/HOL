open HolKernel Parse boolLib bossLib;

val _ = new_theory "delsimps1";

val foo_def = Define‘foo x = x * 2 + 1’;
val _ = export_rewrites ["foo_def"]

val _ = delsimps ["arithmetic.NOT_LT_ZERO_EQ_ZERO"]

val _ = export_theory();
