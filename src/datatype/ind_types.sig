signature ind_types =
sig
 include Abbrev 
 type constructor  = string * hol_type list
 type tyspec       = hol_type * constructor list

 val define_type  : tyspec list -> {induction:thm, recursion:thm}

end
