open HolKernel Parse boolLib bossLib;

val _ = new_theory "dupop20171208a";

val _ = Datatype `testtype = <| fld1 : 'a ; fld2 : num -> bool |>`;


val _ = export_theory();
