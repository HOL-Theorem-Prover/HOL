signature arm_compilerLib =
sig
    include Abbrev

    datatype arm_code_format = 
      InLineCode | SimpleProcedure | PushProcedure of string list * int

    val arm_compile         : thm -> thm -> arm_code_format -> thm * string list
    val arm_flatten_code    : unit -> thm
    val reset_compiled      : unit -> unit

    val optimise_code       : bool ref
    val abbrev_code         : bool ref

    val show_enc            : bool ref
    val show_code           : bool ref 
    val pp_enc              : unit -> unit

end
