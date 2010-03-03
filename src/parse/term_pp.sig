signature term_pp =
sig

  type term = Term.term
  val pp_term :
    term_grammar.grammar -> type_grammar.grammar -> PPBackEnd.t ->
    Portable.ppstream -> term -> unit


  (* this initialises a reference storing a function for pulling apart
     case splits.  It's expected that the initialisation will be called
     from inside the TypeBase *)
  val init_casesplit_munger : (term -> term * (term * term) list) -> unit

end

