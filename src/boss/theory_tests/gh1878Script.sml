Theory gh1878

Theorem test:
  T /\ T
Proof
  conj_tac >- suspend "fine"
  >- suspend "::"
QED

Resume test[fine]:
  ACCEPT_TAC TRUTH
QED

Resume test[::]:
  ACCEPT_TAC TRUTH
QED

Finalise test
