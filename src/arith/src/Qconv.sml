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

structure Qconv :> Qconv =
struct
  open arbint
  val << = String.<


open Drule;

fun failwith function = raise 
 Exception.HOL_ERR{origin_structure = "Qconv",
                    origin_function = function,
                            message = ""};

type conv = Abbrev.conv;
open HolKernel;

val rhs = Dsyntax.rhs;
val aconv = Term.aconv;

(*---------------------------------------------------------------------------*)
(* Exception indicating that a term has not been changed by the conversion   *)
(* applied to it.                                                            *)
(*---------------------------------------------------------------------------*)

exception UNCHANGED;

(*---------------------------------------------------------------------------*)
(* RULE_OF_CONV : conv -> (term -> thm)                                      *)
(*                                                                           *)
(* Takes a conversion that uses failure to indicate that it has not changed  *)
(* its argument term, and produces an ordinary conversion.                   *)
(*---------------------------------------------------------------------------*)

fun RULE_OF_CONV conv tm = conv tm
                           handle UNCHANGED => REFL tm;

(*---------------------------------------------------------------------------*)
(* ALL_CONV : conv                                                           *)
(*                                                                           *)
(* Identity conversion for conversions using failure.                        *)
(*---------------------------------------------------------------------------*)

val ALL_CONV:conv = fn _ => raise UNCHANGED;

(*---------------------------------------------------------------------------*)
(* THENC : (conv * conv) -> conv                                             *)
(*                                                                           *)
(* Takes two conversions that use failure and produces a conversion that     *)
(* applies them in succession. The new conversion also uses failure. It      *)
(* fails if neither of the two argument conversions cause a change.          *)
(*---------------------------------------------------------------------------*)

infix THENC;

fun ((conv1:conv) THENC (conv2:conv)) tm =
   let val th1 = conv1 tm
   in
   TRANS th1 (conv2 (rhs (concl th1)))
   handle UNCHANGED => th1
   end
   handle UNCHANGED => conv2 tm;

(*---------------------------------------------------------------------------*)
(* ORELSEC : (conv * conv) -> conv                                           *)
(*                                                                           *)
(* Takes two conversions that use failure and produces a conversion that     *)
(* tries the first one, and if this fails for a reason other than that the   *)
(* term is unchanged, it tries the second one.                               *)
(*---------------------------------------------------------------------------*)

infix ORELSEC;

fun ((conv1:conv) ORELSEC (conv2:conv)) tm =
   conv1 tm
   handle UNCHANGED => raise UNCHANGED
        | _ => conv2 tm;

(*---------------------------------------------------------------------------*)
(* REPEATC : conv -> conv                                                    *)
(*                                                                           *)
(* Applies a conversion zero or more times.                                  *)
(*---------------------------------------------------------------------------*)

fun REPEATC conv tm =
   ((conv THENC (REPEATC conv)) ORELSEC ALL_CONV) tm;

(*---------------------------------------------------------------------------*)
(* CHANGED_CONV : conv -> conv                                               *)
(*                                                                           *)
(* Causes the conversion given to fail if it does not change its input.      *)
(* Alpha convertibility is only tested for if the term is changed in some    *)
(* way.                                                                      *)
(*---------------------------------------------------------------------------*)

fun CHANGED_CONV conv (tm:term) =
   let val th = conv tm
                handle UNCHANGED => failwith "CHANGED_CONV"
       val {lhs,rhs} = dest_eq (concl th)
   in  if (aconv lhs rhs)
       then failwith "CHANGED_CONV"
       else th
   end;

(*---------------------------------------------------------------------------*)
(* TRY_CONV : conv -> conv                                                   *)
(*                                                                           *)
(* Applies a conversion, and if it fails, raises an UNCHANGED exception.     *)
(*---------------------------------------------------------------------------*)

fun TRY_CONV conv = conv ORELSEC ALL_CONV;

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
   let val {Rator,Rand} = dest_comb tm
           handle _ => failwith "RAND_CONV"
   in
   AP_TERM Rator (conv Rand)
   end;

(*---------------------------------------------------------------------------*)
(* RATOR_CONV : conv -> conv                                                 *)
(*                                                                           *)
(* Applies a conversion to the rator of a term, propagating any failure that *)
(* indicates that the subterm is unchanged.                                  *)
(*---------------------------------------------------------------------------*)

fun RATOR_CONV conv tm =
   let val {Rator,Rand} = dest_comb tm
           handle _ => failwith "RATOR_CONV"
   in
   AP_THM (conv Rator) Rand
   end;

(*---------------------------------------------------------------------------*)
(* ABS_CONV : conv -> conv                                                   *)
(*                                                                           *)
(* Applies a conversion to the body of an abstraction, propagating any       *)
(* failure that indicates that the subterm is unchanged.                     *)
(*---------------------------------------------------------------------------*)

fun ABS_CONV conv tm =
   let val {Bvar,Body} = dest_abs tm
           handle _ => failwith "ABS_CONV"
       val bodyth = conv Body
   in
   ABS Bvar bodyth
   handle (e as Exception.HOL_ERR _) => raise e
        | _ => failwith "ABS_CONV"
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
   let val {Rator=fx,Rand=y} = dest_comb tm handle _ => failwith "ARGS_CONV"
       val {Rator=f,Rand=x} = dest_comb fx handle _ => failwith "ARGS_CONV"
   in  (let val th = AP_TERM f (conv x)
        in  (MK_COMB (th,conv y) handle UNCHANGED => (AP_THM th y))
        end)
       handle UNCHANGED => (AP_TERM fx (conv y))
   end;

end
