signature Arithconv =
sig
  include Abbrev

    val NEQ_CONV : conv
    val LT_CONV  : conv
    val GT_CONV  : conv
    val LE_CONV  : conv
    val GE_CONV  : conv
    val EVEN_CONV: conv
    val ODD_CONV : conv
    val SUC_CONV : conv
    val PRE_CONV : conv
    val SBC_CONV : conv
    val ADD_CONV : conv
    val MUL_CONV : conv
    val EXP_CONV : conv
    val DIV_CONV : conv
    val MOD_CONV : conv
end
