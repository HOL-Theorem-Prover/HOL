signature term_pp =
sig

  type term = Term.term
  val pp_term :
    term_grammar.grammar -> type_grammar.grammar -> Portable.ppstream ->
    term -> unit

  val ty_antiq      : Type.hol_type -> term
  val dest_ty_antiq : term -> Type.hol_type
  val is_ty_antiq   : term -> bool

  (* this initialises a reference storing a function for pulling apart
     case splits.  It's expected that the initialisation will be called
     from inside the TypeBase *)
  val init_casesplit_munger : (term -> term * (term * term) list) -> unit

end

