signature term_pp =
sig

  val pp_term :
    term_grammar.grammar -> type_grammar.grammar -> Portable.ppstream ->
    Term.term -> unit

  val ty_antiq      : Type.hol_type -> Term.term
  val dest_ty_antiq : Term.term -> Type.hol_type
  val is_ty_antiq   : Term.term -> bool

end

