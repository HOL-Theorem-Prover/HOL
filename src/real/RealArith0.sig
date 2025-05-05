signature RealArith0 =
sig
  include Abbrev

  type positivstellensatz
  type rat = Arbrat.rat
  type aint = Arbint.int

  val is_intconst          : term -> bool
  val mk_intconst          : aint -> term
  val dest_intconst        : term -> aint
  val is_realintconst      : term -> bool
  val dest_realintconst    : term -> aint
  val mk_realintconst      : aint -> term
  val is_ratconst          : term -> bool
  val rat_of_term          : term -> rat
  val term_of_rat          : rat -> term

  val REAL_INT_LE_CONV     : conv
  val REAL_INT_LT_CONV     : conv
  val REAL_INT_GE_CONV     : conv
  val REAL_INT_GT_CONV     : conv
  val REAL_INT_EQ_CONV     : conv
  val REAL_INT_ADD_CONV    : conv
  val REAL_INT_SUB_CONV    : conv
  val REAL_INT_NEG_CONV    : conv
  val REAL_INT_MUL_CONV    : conv
  val REAL_INT_POW_CONV    : conv

 (* fn translator (eq,le,lt) -> 'a *)
  val REAL_LINEAR_PROVER   : (thm list * thm list * thm list ->
                              positivstellensatz -> 'a) ->
                             thm list * thm list * thm list -> 'a

 (* for REAL_LINEAR_PROVER, 0: nothing, 1: minimal, 2+: details *)
  val verbose_level        : int ref (* default: 1 *)

  val GEN_REAL_ARITH0:
    (rat -> term) * conv * conv * conv * conv * conv * conv * conv * conv * conv *
    ((thm list * thm list * thm list -> positivstellensatz -> thm) ->
      thm list * thm list * thm list -> thm) -> conv

end
