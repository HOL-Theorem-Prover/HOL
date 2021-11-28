open HolKernel boolTheory tautLib

val _ = new_theory "foo"

val _ = print ("tautLib.x = " ^ Int.toString tautLib.x ^ "\n")

val foo = Theory.save_thm("foo", TRUTH)

val _ = export_theory()
