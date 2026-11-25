Theory splitParent[bare]
Ancestors bool
Libs HolKernel Parse boolLib splitLib splitPersistLib

val _ = Theory.add_ML_dependency "splitPersistLib"

Theorem bool_split[split] = splitLib.type_split_of bool
