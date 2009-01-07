signature prog_x86Lib =
sig

    include helperLib

    val x86_spec         : string -> (thm * int * int option) * 
                                     (thm * int * int option) option      

    val x86_tools        : decompiler_tools

end
