signature RJBConv =
sig
   include Abbrev

   val RULE_OF_CONV : conv -> term -> thm
   val ALL_CONV     : conv
   val THENC        : conv * conv -> conv
   val ORELSEC      : conv * conv -> conv
   val REPEATC      : conv -> conv
   val CHANGED_CONV : conv -> conv
   val TRY_CONV     : conv -> conv
   val CONV_RULE    : conv -> thm -> thm
   val RAND_CONV    : conv -> conv
   val RATOR_CONV   : conv -> conv
   val ABS_CONV     : conv -> conv
   val ARGS_CONV    : conv -> conv
end
