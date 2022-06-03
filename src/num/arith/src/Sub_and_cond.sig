signature Sub_and_cond =
sig
   include Abbrev

   val SUB_AND_COND_ELIM_CONV : conv
   val COND_ELIM_CONV         : conv

   (* from HOL-Light's canon.ml *)
   val CONDS_ELIM_CONV        : conv
   val CONDS_CELIM_CONV       : conv
end
