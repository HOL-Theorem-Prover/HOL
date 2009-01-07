signature decompilerLib =
sig

    include helperLib

    val decompile : decompiler_tools -> string -> term quotation -> thm * thm

    val decompile_arm  : string -> term quotation -> thm * thm
    val decompile_ppc  : string -> term quotation -> thm * thm
    val decompile_x86  : string -> term quotation -> thm * thm

    val basic_decompile : decompiler_tools -> string -> (term * term) option -> term quotation -> thm * thm
 
    val basic_decompile_arm  : string -> (term * term) option -> term quotation -> thm * thm
    val basic_decompile_ppc  : string -> (term * term) option -> term quotation -> thm * thm
    val basic_decompile_x86  : string -> (term * term) option -> term quotation -> thm * thm

    val add_decompiled : string * thm * int * int option -> unit

end
