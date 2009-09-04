signature Solve =
sig
   type term = Term.term
   type conv = Abbrev.conv

   val INEQS_FALSE_CONV : conv
   val DISJ_INEQS_FALSE_CONV : conv
   val NOT_NOT_INTRO_CONV : conv
   val is_T : term -> bool
   val is_F : term -> bool
   val NEGATE_CONV : conv -> conv
   val DEPTH_FORALL_CONV : conv -> conv
   val FORALL_ARITH_CONV : conv

end
