signature arm_rulesLib =
sig
    include Abbrev

    val ARM_PSR_ss  : simpLib.ssfrag
    val ARM_REG_ss  : simpLib.ssfrag
    val PSR_CONV    : conv

end
