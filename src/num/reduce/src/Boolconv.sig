signature Boolconv =
sig
  include Abbrev

  val NOT_CONV  : conv
  val AND_CONV  : conv
  val OR_CONV   : conv
  val IMP_CONV  : conv
  val BEQ_CONV  : conv
  val COND_CONV : conv
end
