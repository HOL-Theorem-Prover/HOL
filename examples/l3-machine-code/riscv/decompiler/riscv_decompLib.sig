signature riscv_decompLib =
sig
    val riscv_decompile: string -> string quotation -> Thm.thm * Thm.thm
    val riscv_decompile_noC: string -> string quotation -> Thm.thm * Thm.thm
    val riscv_tools: helperLib.decompiler_tools
    val riscv_tools_noC: helperLib.decompiler_tools
end
