signature DecisionTheorems =
sig
   type thm = Thm.thm

   val ONE_PLUS : thm
   val ZERO_PLUS : thm
   val PLUS_ZERO : thm
   val SUC_ADD1 : thm
   val SUC_ADD2 : thm
   val ZERO_MULT : thm
   val MULT_ZERO : thm
   val ONE_MULT : thm
   val MULT_ONE : thm
   val MULT_SUC : thm
   val MULT_COMM : thm
   val MULT_EQ_SUC : thm
   val MULT_LEQ_SUC : thm
   val MULT_LESS_SUC : thm
   val SUC_ADD_EQ_F : thm
   val EQ_SUC_ADD_F : thm
   val ZERO_LESS_EQ : thm
   val ZERO_LESS_EQ_T : thm
   val SUC_LESS_EQ_ZERO_F : thm
   val LESS_EQ_PLUS : thm
   val SUC_ADD_LESS_EQ_F : thm
   val ZERO_LESS_SUC_T : thm
   val LESS_ZERO_F : thm
   val LESS_PLUS : thm
   val ADD_LESS_F : thm
   val EQ_EQ_TRANSIT : thm
   val EQ_LEQ_TRANSIT : thm
   val EQ_LESS_TRANSIT : thm
   val LEQ_EQ_TRANSIT : thm
   val LEQ_LEQ_TRANSIT : thm
   val LEQ_LESS_TRANSIT : thm
   val LESS_EQ_TRANSIT : thm
   val LESS_LEQ_TRANSIT : thm
   val LESS_LESS_TRANSIT : thm
end;
