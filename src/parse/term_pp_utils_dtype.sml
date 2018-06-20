structure term_pp_utils_dtype =
struct
  datatype bvar
    = Simple of Term.term
    | Restricted of {Bvar : Term.term, Restrictor : Term.term}

end
