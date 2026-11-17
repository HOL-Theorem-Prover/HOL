open HolKernel Parse boolLib bossLib

val _ = new_theory "staged_source"
val _ = QUse.use "tests/stagedSourceScript.sml"
