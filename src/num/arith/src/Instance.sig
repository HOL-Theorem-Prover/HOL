signature Instance =
sig
   val INSTANCE_T_CONV 
       : (Term.term -> Term.term list) -> Abbrev.conv -> Abbrev.conv
end
