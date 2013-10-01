signature arm_decompLib =
sig

    val config_for_fast   : unit -> unit
    val l3_arm_triples    : string -> Thm.thm list
    val l3_arm_tools      : helperLib.decompiler_tools
    val l3_arm_decompile  : string -> Term.term quotation -> Thm.thm * Thm.thm

end
