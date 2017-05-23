open HolKernel Parse boolLib bossLib;

open proj1ATheory

val _ = new_theory "pp";

val _ = overload_on ("quux", ``foo``)


val _ = export_theory();
