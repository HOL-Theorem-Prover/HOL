signature opsem_translatorLib =
sig

    include Abbrev

    val DERIVE_SEP_SPEC        : string -> term -> thm * thm
    val DERIVE_SEP_TOTAL_SPEC  : string -> term -> thm * thm

    val SEP_SPEC_SEMANTICS     : thm -> thm

end
