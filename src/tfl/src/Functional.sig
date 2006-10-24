signature Functional =
sig

  type term = Term.term
  type thry = TypeBasePure.typeBase

  val allow_new_clauses : bool ref

  datatype pattern
        = GIVEN   of term * int
        | OMITTED of term * int

   val pat_of : pattern -> term
   val givens : pattern list -> term list

   val mk_functional : thry -> term -> {functional:term, pats: pattern list}
   
   val mk_pattern_fn : thry -> (term * term) list -> term
   (* Each element of the list argument is a (pattern, expression) pair.
      A function is constructed which contains a case based on the list of patterns,
      where matching a pattern yields the value of its corresponding expression. *)

end
