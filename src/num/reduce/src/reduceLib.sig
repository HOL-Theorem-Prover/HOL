signature reduceLib =
sig
    include Abbrev

    val NOT_CONV    : conv
    val AND_CONV    : conv
    val OR_CONV     : conv
    val IMP_CONV    : conv
    val BEQ_CONV    : conv
    val COND_CONV   : conv

    val NEQ_CONV    : conv
    val LT_CONV     : conv
    val GT_CONV     : conv
    val LE_CONV     : conv
    val GE_CONV     : conv
    val ODD_CONV    : conv
    val EVEN_CONV   : conv
    val SUC_CONV    : conv
    val PRE_CONV    : conv
    val SBC_CONV    : conv
    val ADD_CONV    : conv
    val MUL_CONV    : conv
    val EXP_CONV    : conv
    val DIV_CONV    : conv
    val MOD_CONV    : conv

    val RED_CONV    : conv
    val REDUCE_CONV : conv
    val REDUCE_RULE : thm -> thm
    val REDUCE_TAC  : tactic

    val num_compset : unit -> computeLib.compset
end
