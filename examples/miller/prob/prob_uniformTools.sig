signature prob_uniformTools =
sig

  val PROB_UNIF_CONV : Term.term -> Thm.thm;
  val PROB_UNIFORM_CUT_CONV : Term.term -> Thm.thm;

end