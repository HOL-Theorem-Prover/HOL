signature decompilerLib =
sig

    include helperLib

    val decompile : decompiler_tools -> string -> term quotation -> thm * thm
    val decompile_strings : decompiler_tools -> string -> string list -> thm * thm

    val decompile_io : decompiler_tools -> string -> (term * term) option -> term quotation -> thm * thm
    val decompile_io_strings : decompiler_tools -> string -> (term * term) option -> string list -> thm * thm

    val decompile_arm  : string -> term quotation -> thm * thm
    val decompile_ppc  : string -> term quotation -> thm * thm
    val decompile_x86  : string -> term quotation -> thm * thm

    val basic_decompile : decompiler_tools -> string -> (term * term) option -> term quotation -> thm * thm
    val basic_decompile_strings : decompiler_tools -> string -> (term * term) option -> string list -> thm * thm

    val basic_decompile_arm : string -> (term * term) option -> term quotation -> thm * thm
    val basic_decompile_ppc : string -> (term * term) option -> term quotation -> thm * thm
    val basic_decompile_x86 : string -> (term * term) option -> term quotation -> thm * thm

    (* some internals exposed *)

    val get_output_list     : thm -> term
    val decompiler_finalise : (thm * thm -> thm * thm) ref

    val add_decompiled      : string * thm * int * int option -> unit

    val add_code_abbrev     : thm list -> unit
    val set_abbreviate_code : bool -> unit
    val get_abbreviate_code : unit -> bool
    val UNABBREV_CODE_RULE  : thm -> thm
    val UNABBREV_ALL        : thm -> thm

    val add_executable_data_name     : string -> unit
    val remove_executable_data_name  : string -> unit

    val add_modifier          : string -> (thm -> thm) -> unit
    val remove_all_modifiers  : unit -> unit

    val decompile_as_single_function : bool ref
    val decompiler_set_pc            : (int -> thm -> thm) ref

    val AUTO_DECONSTRUCT_TAC  : (term -> term) -> tactic 

end
