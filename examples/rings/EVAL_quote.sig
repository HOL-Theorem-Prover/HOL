signature EVAL_quote =
sig

include Abbrev
val meta_expr : hol_type -> (term -> bool) ->
                {Op1 : (term * term) list, Op2 : (term * term) list,
                 Vars : term, Csts : term} ->
                term list -> {Metamap : term, Poly : term list}

end
