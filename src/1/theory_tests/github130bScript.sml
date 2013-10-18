open HolKernel Parse boolLib

open github130Lib github130aTheory
val _ = new_theory "github130b";

val _ = save_thm("gh130b", boolTheory.AND_CLAUSES);


val _ = export_theory();
