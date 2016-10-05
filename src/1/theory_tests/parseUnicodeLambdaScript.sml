open HolKernel Parse boolLib

val _ = new_theory "parseUnicodeLambda";

val _ = set_grammar_ancestry ["bool"]

val t = ``λi. P i``;      (* UOK *)

val th = save_thm("made_it", TRUTH);


val _ = export_theory();
