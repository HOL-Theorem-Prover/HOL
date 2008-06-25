signature ia32Lib =
sig
    include Abbrev

    val ia32_decode          : string -> thm      
    val ia32_step            : string -> thm      

end
