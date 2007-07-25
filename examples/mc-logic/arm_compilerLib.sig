signature arm_compilerLib =
sig
    include Abbrev

    val arm_compile         : thm -> thm -> bool -> thm * string list
    val reset_compiled      : unit -> unit

    val optimise_code       : bool ref
    val abbrev_code         : bool ref

    val show_enc            : bool ref
    val show_code           : bool ref 
    val pp_enc              : unit -> unit

end
