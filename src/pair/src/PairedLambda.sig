signature PairedLambda =
sig
  include Abbrev

  val PAIRED_BETA_CONV : conv 
  val PAIRED_ETA_CONV  : conv 
  val GEN_BETA_CONV    : conv 
  val let_CONV         : conv 

  val GEN_BETA_RULE    : thm -> thm
  val GEN_BETA_TAC     : tactic
end
