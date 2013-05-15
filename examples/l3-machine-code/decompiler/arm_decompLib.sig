signature arm_decompLib =
sig

    include helperLib

    val l3_arm_triples       : string -> thm list
    val l3_arm_tools         : decompiler_tools
    val l3_arm_decompile     : string -> term quotation -> thm * thm

end
