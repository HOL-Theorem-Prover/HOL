open HolKernel Parse boolLib

open bossLib

open HolDoc

val _ = new_theory "Type";

val _ = Hol_datatype`
  loc = loc of num
`;

val _ = export_theory();