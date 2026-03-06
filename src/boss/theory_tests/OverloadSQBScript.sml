Theory OverloadSQB

Overload "[.]" = “(+)”

Overload "↝₁" = “$*”

Theorem foo:
  [.] 4 (↝₁ 5 2) = 14
Proof
  EVAL_TAC
QED


