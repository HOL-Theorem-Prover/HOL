open HolKernel Parse boolLib Datatype

val _ = new_theory "gh260a";

val _ = Datatype`foo = <| fld : num |>`;


val _ = export_theory();
