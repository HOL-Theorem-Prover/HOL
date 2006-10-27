signature term_pp =
sig

  type term = Term.term
  val pp_term :
    term_grammar.grammar -> type_grammar.grammar -> Portable.ppstream ->
    term -> unit

(* The term pretty-printer "pp_term_sep" is exactly like "pp_term",      *)
(* except that it prevents the adjacent printing of two symbolic names,  *)
(* such as two symbolic identifiers, like "|>" and "::".  This enables   *)
(* easier parsing of the result as a term without confusing the lexer.   *)

  val wrap_consumer_sep : (string -> unit) -> (string -> unit)

  val pp_term_sep :
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

