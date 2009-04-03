signature EmitTeX =
sig
    include Abbrev

    val texPrefix                 : string ref
    val emitTeXDir                : string ref

    val non_type_definitions      : string -> (string * thm) list
    val non_type_theorems         : string -> (string * thm) list
    val datatype_theorems         : string -> (string * thm) list
    val print_datatypes           : string -> unit
    val datatype_thm_to_string    : thm -> string

    val hol_to_tex                : (string -> string) ref

    val pp_term_as_tex            : ppstream -> term -> unit
    val pp_type_as_tex            : ppstream -> hol_type -> unit
    val pp_theorem_as_tex         : ppstream -> thm -> unit

    val print_term_as_tex         : term -> unit
    val print_type_as_tex         : hol_type -> unit
    val print_theorem_as_tex      : thm -> unit
    val print_theory_as_tex       : string -> unit

    val print_theories_as_tex_doc : string list -> string -> unit

    val tex_theory                : string -> unit
end
