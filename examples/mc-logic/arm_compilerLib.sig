signature arm_compilerLib =
sig
    include Abbrev

    datatype arm_code_format = 
      InLineCode | SimpleProcedure | PushProcedure of string list * int

    val arm_compile         : thm -> thm -> arm_code_format -> thm * string list
    val arm_flatten_code    : unit -> thm
    val reset_compiled      : unit -> unit
    val arm_decompiler      : string -> term frag list -> tactic option -> 
                              string list -> string list -> thm * thm

    val map_compiled        : (thm -> thm) -> unit 
    val fetch_compiled      : string -> thm

    val compile             : term frag list -> thm * thm * thm
    val compile_proc        : arm_code_format -> term frag list -> thm * thm * thm

    val optimise_code       : bool ref
    val abbrev_code         : bool ref

    val show_enc            : bool ref
    val show_code           : bool ref 
    val pp_enc              : unit -> unit

end
