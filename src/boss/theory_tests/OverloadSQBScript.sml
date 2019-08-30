open HolKernel Parse boolLib bossLib;

val _ = new_theory "OverloadSQB";

Overload "[.]" = “(+)”

Theorem foo:
  [.] 4 5 = 9
Proof
  EVAL_TAC
QED


val _ = export_theory();
