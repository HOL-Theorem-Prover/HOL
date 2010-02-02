signature prog_armLib =
sig

    include helperLib

    val arm_spec             : string -> (thm * int * int option) *
                                         (thm * int * int option) option
    val arm_spec_no_cache    : string -> (thm * int * int option) *
                                         (thm * int * int option) option

    val arm_tools            : decompiler_tools
    val arm_tools_no_status  : decompiler_tools

    val arm_enc              : string -> string
    val set_arm_memory_pred  : string -> unit

end
