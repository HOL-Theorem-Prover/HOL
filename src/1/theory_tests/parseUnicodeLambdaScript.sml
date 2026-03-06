Theory parseUnicodeLambda[bare]
Ancestors[qualified]
  bool
Libs
  HolKernel Parse boolLib

val _ = set_grammar_ancestry ["bool"]

val t = ``λi. P i``;

Theorem made_it = TRUTH
