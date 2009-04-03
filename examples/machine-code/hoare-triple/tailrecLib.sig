signature tailrecLib =
sig

    include Abbrev

    val tailrec_define       : term -> term option -> thm * thm

    val tailrec_ss           : unit -> simpLib.ssfrag
    val tailrec_top_ss       : unit -> simpLib.ssfrag
    val tailrec_part_ss      : unit -> simpLib.ssfrag
    val tailrec_reverse_ss   : unit -> simpLib.ssfrag

    val TAILREC_EQ_TAC       : unit -> tactic

    val tailrec_add_to_simpsets : thm * thm * thm * thm * thm * thm -> unit

end
