open HolKernel Parse boolLib bossLib;

val _ = new_theory "tyabbrev";

val _ = type_abbrev_pp("reln", ``:'a -> 'a -> bool``)

val thm1 = save_thm("thm1", TRUTH)

val _ = export_theory();
