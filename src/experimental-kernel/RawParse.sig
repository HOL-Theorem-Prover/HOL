signature RawParse =
sig

  val readTerm : Type.hol_type vector -> Term.term vector -> string -> Term.term
  val pp_raw_term : (Type.hol_type -> int) -> (Term.term -> int) -> Term.term -> string

end;
