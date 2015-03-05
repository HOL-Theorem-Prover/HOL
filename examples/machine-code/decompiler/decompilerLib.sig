signature decompilerLib =
sig

    include helperLib

    val decompile_with :
       ('a -> string list) -> decompiler_tools -> string -> 'a -> thm * thm
    val decompile : decompiler_tools -> string -> string quotation -> thm * thm
    val decompile_strings :
       decompiler_tools -> string -> string list -> thm * thm

    val decompile_io_with :
       ('a -> string list) -> decompiler_tools -> string ->
       (term * term) option -> 'a -> thm * thm
    val decompile_io :
       decompiler_tools -> string -> (term * term) option -> term quotation ->
       thm * thm
    val decompile_io_strings :
       decompiler_tools -> string -> (term * term) option -> string list ->
       thm * thm

    val basic_decompile_with :
       ('a -> string list) -> decompiler_tools -> string ->
       (term * term) option -> 'a -> thm * thm
    val basic_decompile :
       decompiler_tools -> string -> (term * term) option -> term quotation ->
       thm * thm
    val basic_decompile_strings :
       decompiler_tools -> string -> (term * term) option -> string list ->
       thm * thm

    (* some internals exposed *)

    val get_output_list     : thm -> term
    val decompiler_finalise : (thm * thm -> thm * thm) ref

    val add_decompiled      : string * thm * int * int option -> unit
    val get_decompiled      : string -> thm * int * int option

    val add_code_abbrev     : thm list -> unit
    val set_abbreviate_code : bool -> unit
    val get_abbreviate_code : unit -> bool
    val UNABBREV_CODE_RULE  : thm -> thm
    val UNABBREV_ALL        : thm -> thm

    val add_modifier          : string -> (thm -> thm) -> unit
    val remove_all_modifiers  : unit -> unit

    val decompile_as_single_function : bool ref
    val decompiler_set_pc            : (int -> thm -> thm) ref

    val AUTO_DECONSTRUCT_TAC  : (term -> term) -> tactic

end
