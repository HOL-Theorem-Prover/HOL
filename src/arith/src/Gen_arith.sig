signature Gen_arith =
sig

   val non_presburger_subterms : Term.term -> Term.term list
   val is_presburger : Term.term -> bool
   val ARITH_CONV : Abbrev.conv
end
