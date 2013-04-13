open HolKernel Parse boolLib bossLib

val _ = new_theory "github115a"

open arithmeticTheory

val _ = overload_on ("foo", ``\x. x + y``)

val sample = store_thm(
  "sample",
  ``!y:bool. foo x < foo z ==> x < z``,
  SRW_TAC [ARITH_ss][])

val _ = export_theory()
