structure thmpos_dtype =
struct


  datatype match_position
    = Any
    | Pat of Term.term Abbrev.quotation
    | Pos of (Term.term list -> Term.term)
    | Concl



end (* struct *)
