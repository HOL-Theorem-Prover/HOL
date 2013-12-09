signature arm_core_decompLib =
sig
    val config_for_arm: unit -> unit
    val l3_triple: string -> helperLib.instruction
end
