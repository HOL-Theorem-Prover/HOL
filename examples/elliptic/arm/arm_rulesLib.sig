signature arm_rulesLib =
sig
    include Abbrev

    val SORT_REG_WRITEL_CONV : conv
    val REG_READ_WRITEL_CONV : conv
    val REG_WRITEL_CONV      : conv
    val PSR_CONV             : conv

    val all_arm_rules : (string * thm) list
    val arm_rules     : (string * thm) list
    val nop_rules     : (string * thm) list

    val RULE_GET      : term -> thm list -> thm list
    val RULE_GET_ARM  : term -> thm
    val RULE_GET_NOP  : term -> thm

    val GET_ARM       : string -> thm
    val GET_NOP       : string -> thm
end
