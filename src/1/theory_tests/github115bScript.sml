Theory github115b[bare]
Ancestors
  github115a
Libs
  HolKernel Parse boolLib

(* this theory is in the test-case solely to force Holmake to check that the
   github115aTheory.sml file is loadable (it isn't when the bug is evident
   because the exception in the execution of export_theory results in a
   corrupt Theory.sml file)
*)

Theorem sample2 = AND_CLAUSES

