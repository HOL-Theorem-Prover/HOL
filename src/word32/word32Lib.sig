signature word32Lib =
sig
  include Abbrev

  val word_compset : computeLib.compset

  val WORD_CONV    : conv
  val WORD_RULE    : thm -> thm
  val WORD_TAC     : tactic

  val WORD32_CONV  : conv
  val WORD32_RULE  : thm -> thm
  val WORD32_TAC   : tactic

end
