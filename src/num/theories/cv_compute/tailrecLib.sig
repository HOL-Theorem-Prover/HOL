signature tailrecLib =
sig

    include Abbrev

    val tailrec_define         : string -> term -> thm
    val prove_tailrec_exists   : term -> thm

end
