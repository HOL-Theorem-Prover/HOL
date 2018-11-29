open HolKernel Parse boolLib

open proj2ATheory
val _ = new_theory "proj2B";

val thm2B = store_thm(
  "thm2B",
  “~bar m n <=> (m <=> F) \/ (n <=> F)”,
  REWRITE_TAC[bar_def, DE_MORGAN_THM]);

val _ = export_theory();
