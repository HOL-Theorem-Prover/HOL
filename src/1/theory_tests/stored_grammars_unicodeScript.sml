Theory stored_grammars_unicode[bare]
Libs
  HolKernel Parse boolLib

val (typarse, tmparse) =
  parse_from_grammars $ valOf $ Parse.grammarDB{thyname="bool"}
val t = tmparse `x ⇔ x`

val th = store_thm(
  "th",
  t,
  REWRITE_TAC[]);

