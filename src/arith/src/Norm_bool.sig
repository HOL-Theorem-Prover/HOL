signature Norm_bool =
sig
   type term = Term.term
   type conv = Abbrev.conv

   val EQ_IMP_ELIM_CONV : (term -> bool) -> conv
   val MOVE_NOT_DOWN_CONV : (term -> bool) -> conv -> conv
   val DISJ_LINEAR_CONV : conv
   val DISJ_NORM_FORM_CONV : conv

end
