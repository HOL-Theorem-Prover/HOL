open HolKernel Parse boolLib bossLib;

open dupop20171208aTheory

val _ = new_theory "dupop20171208b";

val _ = Datatype `testtype = <| fld0 : num ; fld1 : 'c ; fld3 : 'dd -> bool |>`;

val _ = export_theory();
