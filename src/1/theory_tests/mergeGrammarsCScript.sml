open HolKernel Parse boolLib


open mergeGrammarsBTheory

val _ = new_theory "mergeGrammarsC";

val _ = temp_set_grammars mergeGrammarsB_grammars
val _ = set_trace "ambiguous grammar warning" 2

val _ = store_thm("true_dat", ``T``, REWRITE_TAC [])


val _ = export_theory();
