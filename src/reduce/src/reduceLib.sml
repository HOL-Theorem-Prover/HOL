structure reduceLib :> reduceLib =
struct

  open Boolconv Arithconv

type conv   = Abbrev.conv
type tactic = Abbrev.tactic
type thm    = Thm.thm

fun failwith function = raise
 Exception.HOL_ERR{origin_structure = "reduceLib",
                   origin_function = function,
                           message = ""};


(*-----------------------------------------------------------------------*)
(* RED_CONV - Try all the conversions in the library                     *)
(*-----------------------------------------------------------------------*)

val RED_CONV =
  let fun FAIL_CONV (s:string) tm = failwith s
  in
      Lib.itlist (Lib.curry (Conv.ORELSEC))
         [ADD_CONV,  AND_CONV,  BEQ_CONV,  COND_CONV, EVEN_CONV,
          DIV_CONV,  EXP_CONV,   GE_CONV,    GT_CONV, ODD_CONV,
          IMP_CONV,   LE_CONV,   LT_CONV,   MOD_CONV,
          MUL_CONV,  NEQ_CONV,  NOT_CONV,    OR_CONV,
          PRE_CONV,  SBC_CONV,  SUC_CONV] (FAIL_CONV "RED_CONV")
  end;

(*-----------------------------------------------------------------------*)
(* REDUCE_CONV - Perform above reductions at any depth.                  *)
(*-----------------------------------------------------------------------*)

val REDUCE_CONV = Conv.DEPTH_CONV RED_CONV;

(*-----------------------------------------------------------------------*)
(* REDUCE_RULE and REDUCE_TAC - Inference rule and tactic versions.      *)
(*-----------------------------------------------------------------------*)

val REDUCE_RULE = Conv.CONV_RULE REDUCE_CONV;

val REDUCE_TAC = Conv.CONV_TAC REDUCE_CONV;


end;
