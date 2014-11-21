signature arm_core_decompLib =
sig
    val config_for_arm: unit -> unit
    val l3_triple: string -> helperLib.instruction
    val arm_core_decompile: string -> string quotation -> Thm.thm * Thm.thm
    val arm_core_decompile_code: string -> string quotation -> Thm.thm * Thm.thm
end
