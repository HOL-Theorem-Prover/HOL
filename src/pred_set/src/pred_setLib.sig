signature pred_setLib =
sig
  include Abbrev

  val SET_SPEC_CONV  : conv
  val SET_INDUCT_TAC : tactic
  val FINITE_CONV    : conv
  val IN_CONV        : conv -> conv
  val DELETE_CONV    : conv -> conv
  val UNION_CONV     : conv -> conv
  val INSERT_CONV    : conv -> conv
  val IMAGE_CONV     : conv -> conv -> conv

  val MAX_SET_elim_tac : tactic

  val PRED_SET_ss    : simpLib.ssfrag

end;
