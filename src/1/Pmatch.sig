signature Pmatch =
sig

  type term = Term.term
  type thm = Thm.thm
  type thry = {Thy : string, Tyop : string} ->
              {case_const : term, constructors : term list} option

   datatype pattern
        = GIVEN   of term * int
        | OMITTED of term * int

   val allow_new_clauses : bool ref
   val pat_of : pattern -> term
   val givens : pattern list -> term list

   val mk_functional : thry -> term -> {functional:term, pats: pattern list}
   val mk_pattern_fn : thry -> (term * term) list -> term

end
