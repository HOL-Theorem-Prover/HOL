signature Qconv =
sig
  local type int = arbint.int in

   type conv = Abbrev.conv

   val RULE_OF_CONV : conv -> (Term.term -> Thm.thm)
   val ALL_CONV : conv
   val THENC : (conv * conv) -> conv
   val ORELSEC : (conv * conv) -> conv
   val REPEATC : conv -> conv
   val CHANGED_CONV : conv -> conv
   val TRY_CONV : conv -> conv
   val CONV_RULE : conv -> Thm.thm -> Thm.thm
   val RAND_CONV : conv -> conv
   val RATOR_CONV : conv -> conv
   val ABS_CONV : conv -> conv
   val ARGS_CONV : conv -> conv
  end
end
