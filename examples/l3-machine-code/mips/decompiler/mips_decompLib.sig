signature mips_decompLib =
sig
    val mips_decompile: string -> string quotation -> Thm.thm * Thm.thm
    val mips_tools: helperLib.decompiler_tools
end
