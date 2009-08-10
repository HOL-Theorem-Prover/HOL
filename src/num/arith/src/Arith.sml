(*****************************************************************************)
(* FILE          : arith.sml                                                 *)
(* DESCRIPTION   : Decision procedure for a subset of linear arithmetic.     *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 2nd October 1992                                          *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 16th February 1993                                        *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 16th February 1993                                        *)
(*****************************************************************************)

structure Arith :> Arith =
struct
 open Abbrev

val ARITH_CONV             = RJBConv.RULE_OF_CONV Gen_arith.ARITH_CONV
val ARITH_FORM_NORM_CONV   = RJBConv.RULE_OF_CONV Norm_ineqs.ARITH_FORM_NORM_CONV
val COND_ELIM_CONV          = RJBConv.RULE_OF_CONV Sub_and_cond.COND_ELIM_CONV
val DISJ_INEQS_FALSE_CONV   = RJBConv.RULE_OF_CONV Solve.DISJ_INEQS_FALSE_CONV
val EXISTS_ARITH_CONV       = RJBConv.RULE_OF_CONV Exists_arith.EXISTS_ARITH_CONV
val FORALL_ARITH_CONV       = RJBConv.RULE_OF_CONV Solve.FORALL_ARITH_CONV
val INSTANCE_T_CONV         = Instance.INSTANCE_T_CONV
val is_prenex               = Prenex.is_prenex
val is_presburger           = Gen_arith.is_presburger
val NEGATE_CONV             = Solve.NEGATE_CONV
val PRENEX_CONV             = RJBConv.RULE_OF_CONV Prenex.PRENEX_CONV
val non_presburger_subterms = Gen_arith.non_presburger_subterms
val SUB_AND_COND_ELIM_CONV  = RJBConv.RULE_OF_CONV
                                 Sub_and_cond.SUB_AND_COND_ELIM_CONV;

end
