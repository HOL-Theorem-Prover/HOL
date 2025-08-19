Theory mergeGrammarsC[bare]
Ancestors
  mergeGrammarsB
Libs
  HolKernel Parse boolLib

val _ = temp_set_grammars $ valOf $ grammarDB{thyname="mergeGrammarsB"}
val _ = set_trace "ambiguous grammar warning" 2

val _ = store_thm("true_dat", ``T``, REWRITE_TAC [])


