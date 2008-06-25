open HolKernel Parse boolLib

open bossLib

open HolDoc

local open ValueTheory in end;

val _ = new_theory "Label";

val _ = Hol_datatype`
  translabel =
    new    of num
  | get    of loc
  | set    of (loc # num)
  | return of value
`;

val _ = export_theory();