signature DecisionArithConvs =
sig

   type conv = Abbrev.conv

   val ADD_ASSOC_CONV : conv
   val ADD_SYM_CONV : conv
   val GATHER_BOTH_CONV : conv
   val GATHER_LEFT_CONV : conv
   val GATHER_NEITHER_CONV : conv
   val GATHER_RIGHT_CONV : conv
   val GEQ_NORM_CONV : conv
   val GREAT_NORM_CONV : conv
   val LEFT_ADD_DISTRIB_CONV : conv
   val LESS_NORM_CONV : conv
   val MULT_ASSOC_CONV : conv
   val MULT_COMM_CONV : conv
   val NOT_GEQ_NORM_CONV : conv
   val NOT_GREAT_NORM_CONV : conv
   val NOT_LEQ_NORM_CONV : conv
   val NOT_LESS_NORM_CONV : conv
   val NOT_NUM_EQ_NORM_CONV : conv
   val ONE_MULT_CONV : conv
   val PLUS_ZERO_CONV : conv
   val SYM_ADD_ASSOC_CONV : conv
   val ZERO_MULT_CONV : conv
   val ZERO_MULT_PLUS_CONV : conv
   val ZERO_PLUS_CONV : conv
   val EQ_PLUS_CONV : conv
   val LEQ_PLUS_CONV : conv
   val LESS_PLUS_CONV : conv
   val NUM_COND_RATOR_CONV : conv
   val NUM_COND_RAND_CONV : conv
   val SUB_NORM_CONV : conv
end;
