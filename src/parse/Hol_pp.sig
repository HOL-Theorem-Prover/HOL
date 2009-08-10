signature Hol_pp =
sig
  type ppstream = Portable.ppstream
  type hol_type = Type.hol_type
  type term     = Term.term
  type thm      = Thm.thm

  datatype theory
    = THEORY of string *
                {types       : (string * int) list,
                 consts      : (string * hol_type) list,
                 parents     : string list,
                 axioms      : (string * thm) list,
                 definitions : (string * thm) list,
                 theorems    : (string * thm) list}

  val pp_type        : ppstream -> hol_type -> unit
  val pp_term        : ppstream -> term -> unit
  val pp_thm         : ppstream -> thm -> unit
  val pp_theory      : ppstream -> theory -> unit

  val type_to_string : hol_type -> string
  val term_to_string : term -> string
  val thm_to_string  : thm -> string

  val print_type     : hol_type -> unit
  val print_term     : term -> unit
  val print_thm      : thm -> unit

  (* val print_theory : theory -> unit  ... found in DB *)

end
