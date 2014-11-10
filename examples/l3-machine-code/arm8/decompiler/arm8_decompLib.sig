signature arm8_decompLib =
sig
    val arm8_decompile: string -> string quotation -> Thm.thm * Thm.thm
    val arm8_decompile_no_status:
       string -> string quotation -> Thm.thm * Thm.thm

    val arm8_decompile32: string -> string quotation -> Thm.thm * Thm.thm
    val arm8_decompile32_no_status:
       string -> string quotation -> Thm.thm * Thm.thm

    val arm8_decompile_code: string -> string quotation -> Thm.thm * Thm.thm
    val arm8_decompile_code_no_status:
       string -> string quotation -> Thm.thm * Thm.thm

    val arm8_decompile32_code: string -> string quotation -> Thm.thm * Thm.thm
    val arm8_decompile32_code_no_status:
       string -> string quotation -> Thm.thm * Thm.thm

    val arm8_tools: helperLib.decompiler_tools
    val arm8_tools_array: helperLib.decompiler_tools
    val arm8_tools_array_no_status: helperLib.decompiler_tools
    val arm8_tools_map8: helperLib.decompiler_tools
    val arm8_tools_map8_no_status: helperLib.decompiler_tools
    val arm8_tools_map32: helperLib.decompiler_tools
    val arm8_tools_map32_no_status: helperLib.decompiler_tools
    val arm8_triples: string -> Thm.thm list
end
