open HolKernel Parse boolLib

open github115aTheory

(* this theory is in the test-case solely to force Holmake to check that the
   github115aTheory.sml file is loadable (it isn't when the bug is evident
   because the exception in the execution of export_theory results in a
   corrupt Theory.sml file)
*)

val _ = new_theory "github115b"

val sample2 = save_thm("sample2", AND_CLAUSES)

val _ = export_theory()
