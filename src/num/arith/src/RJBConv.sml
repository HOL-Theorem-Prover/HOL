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

infix THENC ORELSEC;

(*---------------------------------------------------------------------------*)
(* RULE_OF_CONV : conv -> (term -> thm)                                      *)
(*                                                                           *)
(* Takes a conversion that uses failure to indicate that it has not changed  *)
(* its argument term, and produces an ordinary conversion.                   *)
(*---------------------------------------------------------------------------*)

val RULE_OF_CONV = QConv.QCONV;

(*---------------------------------------------------------------------------*)
(* ALL_CONV : conv                                                           *)
(*                                                                           *)
(* Identity conversion for conversions using failure.                        *)
(*---------------------------------------------------------------------------*)

val ALL_CONV = QConv.ALL_QCONV

(*---------------------------------------------------------------------------*)
(* THENC : conv * conv -> conv                                               *)
(*                                                                           *)
(* Takes two conversions that use failure and produces a conversion that     *)
(* applies them in succession. The new conversion also uses failure. It      *)
(* fails if neither of the two argument conversions cause a change.          *)
(*---------------------------------------------------------------------------*)

fun (c1 THENC c2) = QConv.THENQC c1 c2;

(*---------------------------------------------------------------------------*)
(* ORELSEC : (conv * conv) -> conv                                           *)
(*                                                                           *)
(* Takes two conversions that use failure and produces a conversion that     *)
(* tries the first one, and if this fails for a reason other than that the   *)
(* term is unchanged, it tries the second one.                               *)
(*---------------------------------------------------------------------------*)

fun (c1 ORELSEC c2) = QConv.ORELSEQC c1 c2;

(*---------------------------------------------------------------------------*)
(* REPEATC : conv -> conv                                                    *)
(*                                                                           *)
(* Applies a conversion zero or more times.                                  *)
(*---------------------------------------------------------------------------*)

val REPEATC = QConv.REPEATQC;

(*---------------------------------------------------------------------------*)
(* CHANGED_CONV : conv -> conv                                               *)
(*                                                                           *)
(* Causes the conversion given to fail if it does not change its input.      *)
(* Alpha convertibility is only tested for if the term is changed in some    *)
(* way.                                                                      *)
(*---------------------------------------------------------------------------*)

val CHANGED_CONV = QConv.CHANGED_QCONV;

(*---------------------------------------------------------------------------*)
(* TRY_CONV : conv -> conv                                                   *)
(*                                                                           *)
(* Applies a conversion, and if it fails, raises an UNCHANGED exception.     *)
(*---------------------------------------------------------------------------*)

val TRY_CONV = QConv.TRY_QCONV

(*---------------------------------------------------------------------------*)
(* CONV_RULE : conv -> thm -> thm                                            *)
(*                                                                           *)
(* Generates a rule from a conversion that uses failure to avoid rebuilding  *)
(* unchanged subterms.                                                       *)
(*---------------------------------------------------------------------------*)

fun CONV_RULE conv th = EQ_MP (RULE_OF_CONV conv (concl th)) th;;

(*---------------------------------------------------------------------------*)
(* RAND_CONV : conv -> conv                                                  *)
(*                                                                           *)
(* Applies a conversion to the rand of a term, propagating any failure that  *)
(* indicates that the subterm is unchanged.                                  *)
(*---------------------------------------------------------------------------*)

fun RAND_CONV conv tm =
   let val (Rator,Rand) = with_exn dest_comb tm (ERR "RAND_CONV" "")
   in AP_TERM Rator (conv Rand)
   end;

(*---------------------------------------------------------------------------*)
(* RATOR_CONV : conv -> conv                                                 *)
(*                                                                           *)
(* Applies a conversion to the rator of a term, propagating any failure that *)
(* indicates that the subterm is unchanged.                                  *)
(*---------------------------------------------------------------------------*)

fun RATOR_CONV conv tm =
   let val (Rator,Rand) = with_exn dest_comb tm (ERR "RATOR_CONV" "")
   in AP_THM (conv Rator) Rand
   end;

(*---------------------------------------------------------------------------*)
(* ABS_CONV : conv -> conv                                                   *)
(*                                                                           *)
(* Applies a conversion to the body of an abstraction, propagating any       *)
(* failure that indicates that the subterm is unchanged.                     *)
(*---------------------------------------------------------------------------*)

fun ABS_CONV conv tm =
  let val (Bvar,Body) = with_exn dest_abs tm (ERR "ABS_CONV" "")
      val bodyth = conv Body
  in ABS Bvar bodyth
        handle (e as HOL_ERR _) => raise e
             | Interrupt => raise Interrupt
             | other => failwith "ABS_CONV"
  end;

(*---------------------------------------------------------------------------*)
(* ARGS_CONV : conv -> conv                                                  *)
(*                                                                           *)
(* Applies a conversion to the arguments of a binary operator.               *)
(* Set up to detect UNCHANGED exceptions. If neither argument is modified    *)
(* the UNCHANGED exception is propagated. Otherwise, the failure information *)
(* is used to avoid unnecessary processing.                                  *)
(*---------------------------------------------------------------------------*)

fun ARGS_CONV conv tm =
 let val (fx,y) = with_exn dest_comb tm (ERR "ARGS_CONV" "")
     val (f,x)  = with_exn dest_comb fx (ERR "ARGS_CONV" "")
 in let val th = AP_TERM f (conv x)
    in MK_COMB (th,conv y) handle QConv.UNCHANGED => AP_THM th y
    end
    handle QConv.UNCHANGED => AP_TERM fx (conv y)
 end;

end
