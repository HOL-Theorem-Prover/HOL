Theory suspNested[bare]

Libs HolKernel Parse boolLib markerLib

Theorem nested:
  p ∧ (p ⇒ r) ⇒ p ∧ r
Proof
  strip_tac >> suspend "goal"
QED

Resume nested[goal]:
  conj_tac
  >- suspend "p"
  >> res_tac
QED

Resume nested[p]:
  ASM_REWRITE_TAC[]
QED

Finalise nested
