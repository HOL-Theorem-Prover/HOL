(*===========================================================================
== LIBRARY:     reduce (part II)                                           ==
==                                                                         ==
== DESCRIPTION: Conversions to reduce arithmetic constant expressions      ==
==                                                                         ==
== AUTHOR:      Magnus Myreen                                              ==
==              Chalmers University of Technology                          ==
==                                                                         ==
== DATE:        July 2023                                                  ==
==                                                                         ==
== NOTE:        This replaces the previous version by Michael Norrish.     ==
============================================================================*)

structure Arithconv :> Arithconv =
struct

open HolKernel boolTheory boolLib Parse Rsyntax cvTheory cv_computeLib
     Num_conv numSyntax arithmeticTheory numeralTheory;

val ambient_grammars = Parse.current_grammars();
val _ = Parse.temp_set_grammars arithmeticTheory.arithmetic_grammars

val cv_eval = cv_compute []
val cv_eval_exp = cv_compute [cv_exp_eq]
val c2n_Num = c2n_def |> CONJUNCT1

(*
ADD_CONV “4+5:num”
*)
val ADD_CONV =
  REWR_CONV cvTheory.add_to_cv
  THENC RAND_CONV cv_eval
  THENC REWR_CONV c2n_Num

(*
SBC_CONV “4-5:num”
*)
val SBC_CONV =
  REWR_CONV cvTheory.sub_to_cv
  THENC RAND_CONV cv_eval
  THENC REWR_CONV c2n_Num

(*
SUC_CONV “SUC 5:num”
*)
val SUC_CONV =
  REWR_CONV cvTheory.suc_to_cv
  THENC RAND_CONV cv_eval
  THENC REWR_CONV c2n_Num

(*
PRE_CONV “PRE 5:num”
*)
val PRE_CONV =
  REWR_CONV cvTheory.pre_to_cv
  THENC RAND_CONV cv_eval
  THENC REWR_CONV c2n_Num

(*
MUL_CONV “4*5:num”
*)
val MUL_CONV =
  REWR_CONV cvTheory.mul_to_cv
  THENC RAND_CONV cv_eval
  THENC REWR_CONV c2n_Num

(*
MOD_CONV “4 MOD 5:num”
*)
val MOD_CONV =
  REWR_CONV cvTheory.mod_to_cv
  THENC RAND_CONV cv_eval
  THENC REWR_CONV c2n_Num

(*
DIV_CONV “20 DIV 5:num”
DIV_CONV “20 DIV 21:num”
DIV_CONV “20 DIV 0:num”
*)
val DIV_CONV =
  REWR_CONV cvTheory.div_to_cv
  THENC RAND_CONV cv_eval
  THENC REWR_CONV c2n_Num

(*
EXP_CONV “2 ** 128:num”
*)
val EXP_CONV =
  REWR_CONV cvTheory.exp_to_cv
  THENC RAND_CONV cv_eval_exp
  THENC REWR_CONV c2n_Num

(*
NEQ_CONV “4 = 5:num”
NEQ_CONV “4 = 4:num”
*)
val NEQ_CONV =
  REWR_CONV cvTheory.neq_to_cv
  THENC (RAND_CONV cv_eval)
  THENC REWRITE_CONV [c2b_thm]

(*
LT_CONV “4 < 5:num”
LT_CONV “5 < 4:num”
*)
val LT_CONV =
  REWR_CONV cvTheory.lt_to_cv
  THENC RAND_CONV cv_eval
  THENC REWRITE_CONV [c2b_thm]

(*
GT_CONV “4 > 5:num”
GT_CONV “5 > 4:num”
*)
val GT_CONV =
  REWR_CONV cvTheory.gt_to_cv
  THENC RAND_CONV cv_eval
  THENC REWRITE_CONV [c2b_thm]

(*
LE_CONV “4 <= 5:num”
LE_CONV “5 <= 4:num”
*)
val LE_CONV =
  REWR_CONV cvTheory.le_to_cv
  THENC RAND_CONV (RAND_CONV cv_eval)
  THENC REWRITE_CONV [c2b_thm]

(*
GE_CONV “4 >= 5:num”
GE_CONV “5 >= 4:num”
*)
val GE_CONV =
  REWR_CONV cvTheory.ge_to_cv
  THENC RAND_CONV (RAND_CONV cv_eval)
  THENC REWRITE_CONV [c2b_thm]

(*
EVEN_CONV “EVEN 700”
EVEN_CONV “EVEN 7000000001”
*)
val EVEN_CONV =
  REWR_CONV cvTheory.EVEN_to_cv
  THENC RAND_CONV (RAND_CONV cv_eval)
  THENC REWRITE_CONV [c2b_thm]

(*
ODD_CONV “ODD 700”
ODD_CONV “ODD 7000000001”
*)
val ODD_CONV =
  REWR_CONV cvTheory.ODD_to_cv
  THENC RAND_CONV cv_eval
  THENC REWRITE_CONV [c2b_thm]

val _ = Parse.temp_set_grammars ambient_grammars

end
