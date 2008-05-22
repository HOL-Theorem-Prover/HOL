signature ppcLib =
sig

    include Abbrev

    val ppc_decode          : string -> thm      
    val ppc_step            : string -> thm      

end
