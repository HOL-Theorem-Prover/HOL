signature arithLib =
sig
 include Abbrev

   val ARITH_CONV              : conv
   val ARITH_FORM_NORM_CONV    : conv
   val ARITH_PROVE             : term -> thm
   val COND_ELIM_CONV          : conv
   val DISJ_INEQS_FALSE_CONV   : conv
   val EXISTS_ARITH_CONV       : conv
   val FORALL_ARITH_CONV       : conv
   val INSTANCE_T_CONV         : (term -> term list) -> conv -> conv
   val is_prenex               : term -> bool
   val is_presburger           : term -> bool
   val non_presburger_subterms : term -> term list
   val NEGATE_CONV             : conv -> conv
   val PRENEX_CONV             : conv
   val SUB_AND_COND_ELIM_CONV  : conv

end;
