open HolKernel Parse boolLib

val _ = new_theory "label";

val _ = set_fixity ":-" (Infix(NONASSOC, 80));

val _ = new_type ("label", 0);

val label_def = new_definition(
  "label_def",
  ``((lab:label) :- (argument:bool)) = argument``);

val _ = export_theory();
