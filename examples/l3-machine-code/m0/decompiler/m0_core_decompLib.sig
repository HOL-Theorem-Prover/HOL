signature m0_core_decompLib =
sig
    val config_for_m0: unit -> unit
    val m0_triple: string -> helperLib.instruction
    val m0_core_decompile: string -> string quotation -> Thm.thm * Thm.thm
    val m0_core_decompile_code: string -> string quotation -> Thm.thm * Thm.thm
end
