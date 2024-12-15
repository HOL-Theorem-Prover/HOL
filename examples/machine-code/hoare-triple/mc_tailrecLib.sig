signature mc_tailrecLib =
sig

    include Abbrev

    val tailrec_define              : term -> thm
    val tailrec_define_with_pre     : term -> term -> thm * thm

    val tailrec_define_from_step    : string -> term -> (term * term option) option ->
                                      thm * thm * thm * thm

    val TAILREC_TAC                 : tactic

end
