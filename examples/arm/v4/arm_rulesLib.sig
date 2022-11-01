signature arm_rulesLib =
sig
    include Abbrev

    val SORT_REG_WRITEL_CONV : conv
    val REG_READ_WRITEL_CONV : conv
    val REG_WRITEL_CONV      : conv
    val PSR_CONV             : conv

    val arm_rules     : (string * thm) list

    val RULE_GET      : term -> thm list -> thm list
    val RULE_GET_ARM  : term -> thm

    val GET_ARM       : string -> thm
end
