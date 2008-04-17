open HolKernel Parse boolLib

open bossLib

open HolDoc

local open TypeTheory in end;

val _ = new_theory "Value";

val _ = Hol_datatype`
  value =
    VUnit of one
  | VNum  of num
  | VLoc  of loc
`;

val _ = export_theory();