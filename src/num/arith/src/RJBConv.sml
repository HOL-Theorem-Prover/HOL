(*****************************************************************************)
(* FILE          : qconv.sml                                                 *)
(* DESCRIPTION   : Conversions that use failure to avoid rebuilding          *)
(*                 unchanged subterms.                                       *)
(*                 Based on ideas of Roger Fleming and Tom Melham.           *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 15th March 1991                                           *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 3rd February 1993                                         *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 12th February 1993                                        *)
(*****************************************************************************)

structure RJBConv :> RJBConv =
struct

open HolKernel boolLib Arbint;

val ERR = mk_HOL_ERR "RJBconv";

fun failwith function = raise (ERR function "");

(*---------------------------------------------------------------------------*)
(* RULE_OF_CONV : conv -> (term -> thm)                                      *)
(*                                                                           *)
(* Takes a conversion that uses failure to indicate that it has not changed  *)
(* its argument term, and produces an ordinary conversion.                   *)
(*---------------------------------------------------------------------------*)

val RULE_OF_CONV = Conv.QCONV;

(*---------------------------------------------------------------------------*)
(* ARGS_CONV : conv -> conv                                                  *)
(*                                                                           *)
(* Applies a conversion to the arguments of a binary operator.               *)
(* Set up to detect UNCHANGED exceptions. If neither argument is modified    *)
(* the UNCHANGED exception is propagated. Otherwise, the failure information *)
(* is used to avoid unnecessary processing.                                  *)
(*---------------------------------------------------------------------------*)

val ARGS_CONV = BINOP_CONV

end
