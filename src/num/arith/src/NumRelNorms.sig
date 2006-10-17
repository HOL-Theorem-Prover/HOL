signature NumRelNorms =
sig

  include Abbrev
  val ADDL_CANON_CONV : conv
  val ADDR_CANON_CONV : conv
  val MUL_CANON_CONV : conv

  (* these three normalise relational expressions of the form
       e1 <relop> e2
     taking, for example with sum_eq_norm,
       x + (y + 7) = x + 10
     to
       y = 3
     They all assume that both expressions have already been canonicalised
     with ADDR_CANON_CONV
  *)
  val sum_leq_norm : conv
  val sum_lt_norm : conv
  val sum_eq_norm : conv

end
