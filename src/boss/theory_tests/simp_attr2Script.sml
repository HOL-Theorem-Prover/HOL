open HolKernel Parse boolLib bossLib;

open simp_attr1Theory

val _ = new_theory "simp_attr2";

val fact_SUC = store_thm(
  "fact_SUC",
  ``fact (SUC n) = SUC n * fact n``,
  SRW_TAC [][])

val _ = export_theory();
