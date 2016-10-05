open HolKernel Parse boolLib

val _ = new_theory "SGAUnicodeMergeA1";

val UNION_def = new_definition(
  "UNION_def",
  ``UNION P Q x = P x \/ Q x``);

val _ = export_theory();
