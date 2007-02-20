signature RawParse =
sig

  val readTerm : Term.term vector -> string -> Term.term
  val pp_raw_term : (Term.term -> int) -> Term.term -> string

end;
