Theory SGAUnicodeMergeA1[bare]
Libs
  HolKernel Parse boolLib

val UNION_def = new_definition(
  "UNION_def",
  ``UNION P Q x <=> P x \/ Q x``);

