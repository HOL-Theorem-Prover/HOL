open HolKernel Parse boolLib

val _ = new_theory "stored_grammars_unicode";

val (typarse, tmparse) = parse_from_grammars boolTheory.bool_grammars
val t = tmparse `x ⇔ x`   (* UOK *)

val th = store_thm(
  "th",
  t,
  REWRITE_TAC[]);

val _ = export_theory();
