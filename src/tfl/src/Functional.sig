signature Functional =
sig

  type term = Term.term
  type thry = TypeBasePure.typeBase

   datatype pattern
        = GIVEN   of term * int
        | OMITTED of term * int

   val pat_of : pattern -> term
   val givens : pattern list -> term list

   val mk_functional : thry -> term -> {functional:term, pats: pattern list}

end;
