signature lisp_synthesisLib =
sig

    include Abbrev

    val lisp_Define    : term quotation -> thm
    val lisp_tDefine   : string -> term quotation -> tactic -> thm

    val synthesise_deep_embeddings : unit -> thm

end
