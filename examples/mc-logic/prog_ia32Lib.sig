signature prog_ia32Lib =
sig

    include helperLib

    val ia32_spec         : string -> (thm * int * int option) * 
                                      (thm * int * int option) option      

    val ia32_tools        : decompiler_tools

end
