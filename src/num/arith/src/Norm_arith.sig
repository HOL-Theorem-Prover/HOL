signature Norm_arith =
sig
  type int = Arbint.int
  type thm = Thm.thm
  type conv = Abbrev.conv

  val COLLECT_NUM_CONSTS_CONV : conv
  val NUM_RELN_NORM_CONV : conv -> conv -> conv
  val FAST_MULT_CONV : conv
  val reset_multiplication_theorems : unit -> unit
  val multiplication_theorems : unit -> ((int * int) * thm) list
  val SUM_OF_PRODUCTS_SUC_CONV : conv
  val SUM_OF_PRODUCTS_MULT_CONV : conv
  val SUM_OF_PRODUCTS_CONV : conv
  val LINEAR_SUM_CONV : conv
  val GATHER_CONV : conv
  val IN_LINE_SUM_CONV : conv -> conv
  val ONE_PASS_SORT_CONV : conv
  val SORT_AND_GATHER_CONV : conv
  val SYM_ONE_MULT_VAR_CONV : conv
  val NORM_ZERO_AND_ONE_CONV : conv
end
