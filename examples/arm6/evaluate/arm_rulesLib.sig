signature arm_rulesLib =
sig
    include Abbrev

    val SORT_REG_WRITEL_CONV : conv
    val REG_READ_WRITEL_CONV : conv
    val REG_WRITEL_CONV      : conv

    val GET_ARM_RULE : term -> thm list
    val GET_ARM      : string -> thm list
end
