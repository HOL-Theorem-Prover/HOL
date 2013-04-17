signature decompilerLib =
sig

    include helperLib

    val decompile : decompiler_tools -> string -> term quotation -> thm * thm

    val UNABBREV_CODE_RULE  : thm -> thm

end
