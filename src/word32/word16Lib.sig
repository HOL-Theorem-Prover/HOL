signature word16Lib =
sig
  include Abbrev

  val word_compset : computeLib.compset

  val WORD_CONV    : conv
  val WORD_RULE    : thm -> thm
  val WORD_TAC     : tactic

  val WORD16_CONV  : conv
  val WORD16_RULE  : thm -> thm
  val WORD16_TAC   : tactic

end
