(****************************************************************************)
(* FILE          : qconv.sml                                                *)
(* DESCRIPTION   : Conversions that use failure to avoid rebuilding         *)
(*                 unchanged subterms.                                      *)
(*                 Based on ideas of Roger Fleming and Tom Melham.          *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton, University of Cambridge                     *)
(* DATE          : 15th March 1991                                          *)
(*                                                                          *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                     *)
(* DATE          : 3rd February 1993                                        *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 21st August 1996                                         *)
(****************************************************************************)

structure DecisionConv :> DecisionConv =
struct

local open Exception
      open Lib
      open Thm
      open Term
      open Psyntax
      open Drule
in

fun failwith function = raise HOL_ERR{origin_structure = "FConv",
                                      origin_function = function,
                                      message = ""};

type term = Term.term
type thm = Thm.thm
type conv = Abbrev.conv


(*--------------------------------------------------------------------------*)
(* Exception indicating that a term has not been changed by the conversion  *)
(* applied to it.                                                           *)
(*--------------------------------------------------------------------------*)

exception UNCHANGED;

(*--------------------------------------------------------------------------*)
(* RULE_OF_CONV : conv -> (term -> thm)                                     *)
(*                                                                          *)
(* Takes a conversion that uses failure to indicate that it has not changed *)
(* its argument term, and produces an ordinary conversion.                  *)
(*--------------------------------------------------------------------------*)

fun RULE_OF_CONV conv tm = (conv tm handle UNCHANGED => REFL tm);

(*--------------------------------------------------------------------------*)
(* ALL_CONV : conv                                                          *)
(*                                                                          *)
(* Identity conversion for conversions using failure.                       *)
(*--------------------------------------------------------------------------*)

val ALL_CONV:conv = fn _ => raise UNCHANGED;

(*--------------------------------------------------------------------------*)
(* THENC : (conv * conv) -> conv                                            *)
(*                                                                          *)
(* Takes two conversions that use failure and produces a conversion that    *)
(* applies them in succession. The new conversion also uses failure. It     *)
(* fails if neither of the two argument conversions cause a change.         *)
(*--------------------------------------------------------------------------*)

infix THENC;

fun ((conv1:conv) THENC (conv2:conv)) tm =
   let val th1 = conv1 tm
   in
   TRANS th1 (conv2 (Dsyntax.rhs (concl th1)))
   handle UNCHANGED => th1
   end
   handle UNCHANGED => conv2 tm;

(*--------------------------------------------------------------------------*)
(* ORELSEC : (conv * conv) -> conv                                          *)
(*                                                                          *)
(* Takes two conversions that use failure and produces a conversion that    *)
(* tries the first one, and if this fails for a reason other than that the  *)
(* term is unchanged, it tries the second one.                              *)
(*--------------------------------------------------------------------------*)

infix ORELSEC;

fun ((conv1:conv) ORELSEC (conv2:conv)) tm =
   conv1 tm
   handle UNCHANGED => raise UNCHANGED
        | HOL_ERR _ => conv2 tm;

(*--------------------------------------------------------------------------*)
(* REPEATC : conv -> conv                                                   *)
(*                                                                          *)
(* Applies a conversion zero or more times.                                 *)
(*--------------------------------------------------------------------------*)

fun REPEATC conv tm =
   ((conv THENC (REPEATC conv)) ORELSEC ALL_CONV) tm;

(*--------------------------------------------------------------------------*)
(* CHANGED_CONV : conv -> conv                                              *)
(*                                                                          *)
(* Causes the conversion given to fail if it does not change its input.     *)
(* Alpha convertibility is only tested for if the term is changed in some   *)
(* way.                                                                     *)
(*--------------------------------------------------------------------------*)

fun CHANGED_CONV conv (tm:term) =
   let val th = conv tm
                handle UNCHANGED => failwith "CHANGED_CONV"
       val (lhs,rhs) = Psyntax.dest_eq (concl th)
   in  if (aconv lhs rhs)
       then failwith "CHANGED_CONV"
       else th
   end;

(*--------------------------------------------------------------------------*)
(* TRY_CONV : conv -> conv                                                  *)
(*                                                                          *)
(* Applies a conversion, and if it fails, raises an UNCHANGED exception.    *)
(*--------------------------------------------------------------------------*)

fun TRY_CONV conv = conv ORELSEC ALL_CONV;

(*--------------------------------------------------------------------------*)
(* CONV_RULE : conv -> thm -> thm                                           *)
(*                                                                          *)
(* Generates a rule from a conversion that uses failure to avoid rebuilding *)
(* unchanged subterms.                                                      *)
(*--------------------------------------------------------------------------*)

fun CONV_RULE conv th = EQ_MP (RULE_OF_CONV conv (concl th)) th;;

(*--------------------------------------------------------------------------*)
(* RAND_CONV : conv -> conv                                                 *)
(*                                                                          *)
(* Applies a conversion to the rand of a term, propagating any failure that *)
(* indicates that the subterm is unchanged.                                 *)
(*--------------------------------------------------------------------------*)

fun RAND_CONV conv tm =
   let val (rator,rand) = Psyntax.dest_comb tm
           handle HOL_ERR _ => failwith "RAND_CONV"
   in
   AP_TERM rator (conv rand)
   end;

(*--------------------------------------------------------------------------*)
(* RATOR_CONV : conv -> conv                                                *)
(*                                                                          *)
(* Applies a conversion to the rator of a term, propagating any failure     *)
(* that indicates that the subterm is unchanged.                            *)
(*--------------------------------------------------------------------------*)

fun RATOR_CONV conv tm =
   let val (rator,rand) = Psyntax.dest_comb tm
           handle HOL_ERR _ => failwith "RATOR_CONV"
   in
   AP_THM (conv rator) rand
   end;

(*--------------------------------------------------------------------------*)
(* ABS_CONV : conv -> conv                                                  *)
(*                                                                          *)
(* Applies a conversion to the body of an abstraction, propagating any      *)
(* failure that indicates that the subterm is unchanged.                    *)
(*--------------------------------------------------------------------------*)

fun ABS_CONV conv tm =
   let val (bvar,body) = dest_abs tm handle HOL_ERR _ => failwith "ABS_CONV"
       val bodyth = conv body
   in
     ABS bvar bodyth handle (e as HOL_ERR _) => raise e
   end;

(*--------------------------------------------------------------------------*)
(* ARGS_CONV : (conv list) -> conv                                          *)
(*                                                                          *)
(* Applies a list of conversions to the arguments of a curried function     *)
(* application. The number of conversions must be equal to the number of    *)
(* arguments obtained by fully stripping the application. Set up to detect  *)
(* UNCHANGED exceptions. If no argument is modified the UNCHANGED exception *)
(* is propagated. Otherwise, the failure information is used to avoid       *)
(* unnecessary processing.                                                  *)
(*                                                                          *)
(* ARGS_CONV [conv1,...,convn] `f a1 ... an` applies convi to ai.           *)
(*--------------------------------------------------------------------------*)

val ARGS_CONV =
   let fun args_conv convs tm =
          if (null convs)
          then if (is_comb tm)
               then failwith "ARGS_CONV"
               else ALL_CONV tm
          else let val (f,x) = dest_comb tm handle _ => failwith "ARGS_CONV"
               in  let val th = args_conv (tl convs) f
                   in  MK_COMB (th,hd convs x)
                       handle UNCHANGED => (AP_THM th x)
                   end
                   handle UNCHANGED => AP_TERM f (hd convs x)
               end
   in  args_conv o rev
   end;

end;

end; (* DecisionConv *)
