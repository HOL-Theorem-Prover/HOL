signature decompilerLib =
sig

    include helperLib

    val decompile : decompiler_tools -> string -> term quotation -> thm * thm list

    val decompile_arm  : string -> term quotation -> thm * thm list
    val decompile_ppc  : string -> term quotation -> thm * thm list
    val decompile_ia32 : string -> term quotation -> thm * thm list

end
