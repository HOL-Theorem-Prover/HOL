signature prog_x64Lib =
sig

    include helperLib

    val x64_spec                      : string -> (thm * int * int option) *
                                        (thm * int * int option) option

    val x64_spec_byte_memory          : string -> (thm * int * int option) *
                                        (thm * int * int option) option

    val x64_spec_memory64             : string -> (thm * int * int option) *
                                        (thm * int * int option) option

    val x64_spec_memory64_no_status   : string -> (thm * int * int option) *
                                        (thm * int * int option) option

    val x64_tools               : decompiler_tools
    val x64_tools_no_status     : decompiler_tools
    val x64_tools_64            : decompiler_tools
    val x64_tools_64_no_status  : decompiler_tools

    val set_x64_exec_flag             : bool -> unit
    val set_x64_code_write_perm_flag  : bool -> unit
    val set_x64_use_stack             : bool -> unit

    val calc_code : thm -> term
    val pre_process_thm : thm -> thm
    val w2n_MOD : thm
    val x64_prove_one_spec_1 : thm -> term -> thm
    val introduce_zMEMORY64 : thm -> thm
    val introduce_zMEMORY64_1 : thm -> thm

end
