signature ppc_Lib =
sig
    include Abbrev

    val ppc_decode          : string -> thm      
    val ppc_step            : string -> thm      

    val ppc_test            : string -> (string * string) list -> (string * string) list -> thm

end
