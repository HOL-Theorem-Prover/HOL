open HolKernel Parse boolLib

open bossLib

open HolDoc

val _ = new_theory "Type";

val _ = Hol_datatype`
  loc = loc of num
`;

(* a handy utility: *)
val _ = add_infix ("NOTIN", 450, RIGHT);
val notin_def = Define `(x NOTIN s) = ~(x IN s)`;

val _ = export_theory();