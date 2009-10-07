signature prog_toyLib =
sig

    include helperLib

    val toy_spec          : string -> (thm * int * int option) *
                                      (thm * int * int option) option

    val toy_tools         : decompiler_tools

    val toy_spec_tac      : tactic

end
