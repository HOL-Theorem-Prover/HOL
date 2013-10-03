signature m0_decompLib =
sig

    val m0_triples   : string -> helperLib.instruction
    val m0_tools     : helperLib.decompiler_tools
    val m0_decompile : string -> Term.term quotation -> Thm.thm * Thm.thm

end
