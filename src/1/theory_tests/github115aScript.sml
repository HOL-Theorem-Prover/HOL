open HolKernel Parse boolLib

val _ = new_theory "github115a"

val _ = overload_on ("foo", ``\x. x /\ y``)

val sample = store_thm(
  "sample",
  ``!y:bool->bool. foo x /\ foo z ==> x /\ z``,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);

val _ = export_theory()
