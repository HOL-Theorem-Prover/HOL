signature decompilerLib =
sig

    include helperLib

    val decompile : decompiler_tools -> string -> term quotation -> thm * thm

    val decompile_arm  : string -> term quotation -> thm * thm
    val decompile_ppc  : string -> term quotation -> thm * thm
    val decompile_ia32 : string -> term quotation -> thm * thm

end
