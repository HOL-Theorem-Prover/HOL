signature word32Lib =
sig
  include Abbrev

  val word_compset : computeLib.compset
  val WORD_CONV : conv
  val WORD_RULE : thm -> thm
  val WORD_TAC  : tactic

end
