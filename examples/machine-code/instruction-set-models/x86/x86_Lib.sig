signature x86_Lib =
sig
    include Abbrev

    val x86_decode          : string -> thm      
    val x86_step            : string -> thm      

    val x86_test            : string -> (string * string) list -> (string * string) list -> thm

end
