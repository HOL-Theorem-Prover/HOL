signature word64Lib =
sig
  include Abbrev

  val word_compset : computeLib.compset

  val WORD_CONV    : conv
  val WORD_RULE    : thm -> thm
  val WORD_TAC     : tactic

  val WORD64_CONV  : conv
  val WORD64_RULE  : thm -> thm
  val WORD64_TAC   : tactic

end
