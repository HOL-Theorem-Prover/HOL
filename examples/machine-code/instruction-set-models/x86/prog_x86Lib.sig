signature prog_x86Lib =
sig

    include helperLib

    val x86_spec             : string -> (thm * int * int option) *
                                         (thm * int * int option) option

    val x86_tools            : decompiler_tools
    val x86_tools_no_status  : decompiler_tools

    val set_x86_exec_flag             : bool -> unit
    val set_x86_code_write_perm_flag  : bool -> unit
    val set_x86_use_stack             : bool -> unit

end
