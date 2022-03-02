open HolKernel Parse boolLib bossLib;

val _ = new_theory "register_indnA";

Definition foo_def:
  foo [] = [] /\
  foo (h::t) = (h + 1) :: foo t
End

Definition foo_def:
  foo x 0 = x /\
  foo x (SUC n) = SUC (foo x n)
End

val _ = add_ML_dependency "Werror"

val _ = export_theory();
