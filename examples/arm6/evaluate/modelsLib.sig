signature modelsLib =
sig
    include Abbrev

    val arm_compset  : unit -> computeLib.compset
    val arm6_compset : unit -> computeLib.compset

    val ARM_CONV     : conv
    val ARM_RULE     : rule
    val ARM6_CONV    : conv
    val ARM6_RULE    : rule
end
