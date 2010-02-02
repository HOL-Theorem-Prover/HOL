signature prog_ppcLib =
sig

    include helperLib

    val ppc_spec             : string -> (thm * int * int option) *
                                         (thm * int * int option) option

    val ppc_tools            : decompiler_tools
    val ppc_tools_no_status  : decompiler_tools

end
