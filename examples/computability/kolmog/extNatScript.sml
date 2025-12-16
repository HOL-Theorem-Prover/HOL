Theory extNat

val _ = type_abbrev("extnat",``:num option``)

Definition extnat_le_def:
(extnat_le NONE NONE <=> T) ∧
(extnat_le NONE (SOME _) <=> F) ∧
(extnat_le (SOME _) NONE <=> T)∧
(extnat_le (SOME (x:num)) (SOME y) <=> x<=y)
End

Definition extnat_plus_def:
(extnat_plus NONE NONE = NONE ) ∧
(extnat_plus (SOME _) NONE = NONE ) ∧
(extnat_plus NONE (SOME _) = NONE) ∧
(extnat_plus (SOME (x:num)) (SOME y) = SOME (x+y) )
End

val _ = overload_on ("<=",``extnat_le``);
val _ = overload_on ("+",``extnat_plus``);
val _ = export_rewrites["extNat.extnat_le_def","extNat.extnat_plus_def"]

Theorem extnat_plus_inf[simp]:
 (NONE + c = NONE) ∧ (c + NONE = NONE)
ProofCases_on`c` >> simp[]
QED

