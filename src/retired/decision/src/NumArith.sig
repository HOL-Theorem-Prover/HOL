signature NumArith =
sig
   type num = NumType.num
   type coeffs = num * (string * num) list
   type term = Term.term
   type thm = Thm.thm

   val ADD_CONV : DecisionConv.conv
   val COLLECT_NUM_CONSTS_CONV : DecisionConv.conv
   val NUM_RELN_NORM_CONV :
          DecisionConv.conv -> DecisionConv.conv -> DecisionConv.conv
   val FAST_MULT_CONV : DecisionConv.conv
   val reset_multiplication_theorems : unit -> unit
   val multiplication_theorems : unit -> ((num * num) * thm) list
   val SUM_OF_PRODUCTS_SUC_CONV : DecisionConv.conv
   val SUM_OF_PRODUCTS_MULT_CONV : DecisionConv.conv
   val SUM_OF_PRODUCTS_CONV : DecisionConv.conv
   val LINEAR_SUM_CONV : DecisionConv.conv
   val GATHER_CONV : DecisionConv.conv
   val IN_LINE_SUM_CONV : DecisionConv.conv -> DecisionConv.conv
   val ONE_PASS_SORT_CONV : DecisionConv.conv
   val SORT_AND_GATHER_CONV : DecisionConv.conv
   val NORM_ZERO_AND_ONE_CONV : DecisionConv.conv
   val ADD_TERM_TO_INEQ_CONV : term -> DecisionConv.conv
   val ADD_COEFFS_TO_INEQ_CONV : coeffs -> DecisionConv.conv
   val INEQ_GATHER_CONV : DecisionConv.conv
   val ARITH_LITERAL_NORM_CONV : DecisionConv.conv
   val CONST_TIMES_ARITH_CONV : DecisionConv.conv
   val MULT_INEQ_BY_CONST_CONV : term -> DecisionConv.conv
   val EQ_CONV : DecisionConv.conv
   val LEQ_CONV : DecisionConv.conv
   val LESS_CONV : DecisionConv.conv
   val WEIGHTED_SUM : string ->
        ((NumInequalityCoeffs.inequality_relation * coeffs) LazyThm.lazy_thm *
         (NumInequalityCoeffs.inequality_relation * coeffs) LazyThm.lazy_thm)
         ->
          (NumInequalityCoeffs.inequality_relation * coeffs) LazyThm.lazy_thm
   val var_to_elim :
          (NumInequalityCoeffs.inequality_relation * coeffs) list -> string
   val VAR_ELIM
     :(NumInequalityCoeffs.inequality_relation * coeffs) LazyThm.lazy_thm list
       ->
      (NumInequalityCoeffs.inequality_relation * coeffs) LazyThm.lazy_thm
   val INEQS_FALSE_CONV : term -> LazyThm.pre_thm
end;
