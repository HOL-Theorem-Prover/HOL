(*  A theory that loads markerLib but suspends nothing: exporting it
    must not write any suspension.* data (checked by suspCompact). *)

Theory suspNone[bare]

Libs HolKernel Parse boolLib markerLib

Theorem none_thm:
  p ==> p
Proof
  DISCH_TAC >> POP_ASSUM ACCEPT_TAC
QED
