signature prog_armLib =
sig

    include helperLib

    val arm_spec          : string -> (thm * int * int option) *
                                      (thm * int * int option) option

    val arm_tools         : decompiler_tools

end
