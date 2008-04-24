signature EmitTeX =
sig
    include Abbrev

    val texOptions                : string ref
    val texPrefix                 : string ref
    val emitTeXDir                : string ref

    val non_type_definitions      : string -> (string * thm) list
    val non_type_theorems         : string -> (string * thm) list
    val datatype_theorems         : string -> (string * thm) list

    val pp_datatype_theorem       : ppstream -> thm -> unit
    val datatype_thm_to_string    : thm -> string
    val theory_datatypes          : string -> unit

    val theorem_to_tex            : (string -> string) ref
    val datatype_to_tex           : (string -> string) ref

    val pp_theorem_as_tex         : ppstream -> thm -> unit

    val pp_theory_as_tex_commands : ppstream -> string -> unit
    val pp_theory_as_tex          : ppstream -> string -> unit
    val pp_theories_as_tex        : ppstream -> string list -> unit

    val print_theory_as_tex       : string -> string -> unit
    val print_theories_as_tex     : string list -> string -> unit

    val tex_commands_theory       : string -> unit
    val tex_theory                : string -> unit
end
