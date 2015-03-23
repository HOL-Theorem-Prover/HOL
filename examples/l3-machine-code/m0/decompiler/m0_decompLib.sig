signature m0_decompLib =
sig
    val l3_m0_tools: helperLib.decompiler_tools
    val l3_m0_tools_array: helperLib.decompiler_tools
    val l3_m0_tools_array_no_status: helperLib.decompiler_tools
    val l3_m0_tools_flat: helperLib.decompiler_tools
    val l3_m0_tools_flat_no_status: helperLib.decompiler_tools
    val l3_m0_tools_mapped: helperLib.decompiler_tools
    val l3_m0_tools_mapped_no_status: helperLib.decompiler_tools
    val l3_m0_tools_no_status: helperLib.decompiler_tools
    val m0_decompile : string -> string quotation -> Thm.thm * Thm.thm
    val m0_decompile_code : string -> string quotation -> Thm.thm * Thm.thm
end
