signature OmegaSymbolic =
sig

  include Abbrev

  val eliminate_an_existential : conv
  val sym_normalise : conv
  val findelim_deep_existential : conv

end;

(*
    [eliminate_an_existential t] with t of the form
       ?x1..xn. body
    and body a conjunction of normalised <= and int_divides terms.
    The latter may be negated.  Eliminates one of the existential
    variables, picking the "best" one to eliminate.

    [sym_normalise t] with t of the form
       ?x1..xn. body
    and with body of just about any quantifier-free form
    as long as the leaves are relations over integer expressions.

    [findelim_deep_existential t] with t of any form (other than that
    leaves are relations over integer expressions), finds a quantifier
    with scope over no others and eliminates it.

*)
