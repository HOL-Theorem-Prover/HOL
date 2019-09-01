open HolKernel Parse boolLib bossLib;

val _ = new_theory "OverloadSQB";

Overload "[.]" = “(+)”

Overload "↝₁" = “$*”  (* UOK *)

Theorem foo:
  [.] 4 (↝₁ 5 2) = 14   (* UOK *)
Proof
  EVAL_TAC
QED


val _ = export_theory();
