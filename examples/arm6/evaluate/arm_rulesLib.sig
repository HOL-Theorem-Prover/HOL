signature arm_rulesLib =
sig
    include Abbrev

    val SORT_REG_WRITEL_CONV : conv
    val REG_READ_WRITEL_CONV : conv
    val REG_WRITEL_CONV      : conv
end
