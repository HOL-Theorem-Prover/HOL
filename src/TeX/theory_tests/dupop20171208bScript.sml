open HolKernel Parse boolLib bossLib;

open dupop20171208aTheory

val _ = new_theory "dupop20171208b";

val _ = Datatype `testtype = <| fld1 : 'a ; fld3 : 'b -> bool |>`;

val _ = export_theory();
