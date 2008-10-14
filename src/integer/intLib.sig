signature intLib =
sig
  include Abbrev

  val int_ss         : simpLib.simpset
  val INT_ARITH_ss   : simpLib.ssfrag

  val prefer_int     : unit -> unit
  val deprecate_int  : unit -> unit

  val REDUCE_CONV    : conv
  val ARITH_CONV     : conv
  val ARITH_PROVE    : conv
  val ARITH_TAC      : tactic

  val COOPER_CONV    : conv
  val COOPER_PROVE   : conv
  val COOPER_TAC     : tactic


end
