signature Instance =
sig
  local type int = arbint.int in


   val INSTANCE_T_CONV 
       : (Term.term -> Term.term list) -> Abbrev.conv -> Abbrev.conv
  end
end
