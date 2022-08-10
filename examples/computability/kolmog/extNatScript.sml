open HolKernel Parse boolLib bossLib;

val _ = new_theory "extNat";

val _ = type_abbrev("extnat",``:num option``)

val extnat_le_def = Define`
(extnat_le NONE NONE <=> T) ∧
(extnat_le NONE (SOME _) <=> F) ∧
(extnat_le (SOME _) NONE <=> T)∧
(extnat_le (SOME (x:num)) (SOME y) <=> x<=y)`

val extnat_plus_def = Define`
(extnat_plus NONE NONE = NONE ) ∧
(extnat_plus (SOME _) NONE = NONE ) ∧
(extnat_plus NONE (SOME _) = NONE) ∧
(extnat_plus (SOME (x:num)) (SOME y) = SOME (x+y) )`

val _ = overload_on ("<=",``extnat_le``);
val _ = overload_on ("+",``extnat_plus``);
val _ = export_rewrites["extNat.extnat_le_def","extNat.extnat_plus_def"]

val extnat_plus_inf = Q.store_thm("extnat_plus_inf[simp]",
`(NONE + c = NONE) ∧ (c + NONE = NONE)`,Cases_on`c` >> simp[])

val _ = export_theory();

