signature arm_decompLib =
sig

    val config_for_fast: unit -> unit
    val config_for_original: unit -> unit
    val l3_arm_decompile: string -> Term.term quotation -> Thm.thm * Thm.thm
    val l3_arm_decompile_no_status:
       string -> Term.term quotation -> Thm.thm * Thm.thm
    val l3_arm_tools: helperLib.decompiler_tools
    val l3_arm_tools_no_status: helperLib.decompiler_tools
    val l3_arm_triples: string -> Thm.thm list

end
