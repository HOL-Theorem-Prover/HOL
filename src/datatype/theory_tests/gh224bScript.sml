Theory gh224b[bare]
Ancestors
  gh224a
Libs
  HolKernel Parse boolLib

Theorem size_works:
  <| size := 3|>.size = 3
Proof
  simpLib.SIMP_TAC (BasicProvers.srw_ss()) []
QED


