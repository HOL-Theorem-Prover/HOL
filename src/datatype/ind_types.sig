signature ind_types =
sig
 type hol_type     = Type.hol_type
 type thm          = Thm.thm
 type constructor  = string * hol_type list
 type tyspec       = hol_type * constructor list

 val define_type  : tyspec list -> {induction:thm, recursion:thm}

end