open HolKernel Parse boolLib Datatype

open gh260aTheory

val _ = new_theory "gh260b";

val _ = Datatype`foo = <| fld : num |>`


val _ = export_theory();
