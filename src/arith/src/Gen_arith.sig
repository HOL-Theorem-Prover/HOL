signature Gen_arith =
sig
  local type int = arbint.int in


   val non_presburger_subterms : Term.term -> Term.term list
   val is_presburger : Term.term -> bool
   val ARITH_CONV : Abbrev.conv
  end
end
