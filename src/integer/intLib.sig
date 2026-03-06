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

  val INT_POLY_CONV       : conv
  val INT_RING            : term -> thm
  val INT_RING_TAC        : tactic
  val int_ideal_cofactors : term list -> term -> term list

  val INTEGER_TAC    : tactic
  val INTEGER_RULE   : term -> thm

end
