structure QConv :> QConv =
struct

open HolKernel boolSyntax Drule Abbrev;

val ERR = mk_HOL_ERR "QConv";

(* ===================================================================== *)
(* Conversions that use failure to indicate that they have not changed	*)
(* their input term, and hence save the term from being rebuilt		*)
(* unnecessarily.							*)
(*									*)
(* Based on ideas of Roger Fleming. Implemented by Richard Boulton.	*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* Failure exception used to indicate that a term has not been changed  *)
(* by the conversion applied to it.					*)
(* ---------------------------------------------------------------------*)

exception UNCHANGED;

(* ---------------------------------------------------------------------*)
(* QCONV : conv -> conv							*)
(*									*)
(* Takes a conversion that uses failure to indicate that it has not	*)
(* changed its argument term, and produces an ordinary conversion.	*)
(* ---------------------------------------------------------------------*)

fun QCONV conv tm = conv tm handle UNCHANGED => REFL tm;

(* ---------------------------------------------------------------------*)
(* ALL_QCONV : conv							*)
(*									*)
(* Identity conversion for conversions using failure.			*)
(* ---------------------------------------------------------------------*)

val ALL_QCONV:conv = fn _ => raise UNCHANGED;

(* ---------------------------------------------------------------------*)
(* THENQC : conv -> conv -> conv					*)
(*									*)
(* Takes two conversions that use failure and produces a conversion that*)
(* applies them in succession. The new conversion also uses failure. It	*)
(* fails if neither of the two argument conversions cause a change.	*)
(* ---------------------------------------------------------------------*)

fun THENQC conv1 conv2 tm =
   let val th1 = conv1 tm
   in TRANS th1 (conv2 (rhs (concl th1))) handle UNCHANGED => th1
   end
   handle UNCHANGED => conv2 tm;

(* ---------------------------------------------------------------------*)
(* ORELSEQC : conv -> conv -> conv					*)
(*									*)
(* Takes two conversions that use failure and produces a conversion that*)
(* tries the first one, and if this fails for a reason other than that	*)
(* the term is unchanged, it tries the second one.                      *)
(* ---------------------------------------------------------------------*)

fun ORELSEQC c1 c2 t = c1 t handle HOL_ERR _ => c2 t;

(* ---------------------------------------------------------------------*)
(* REPEATQC : conv -> conv						*)
(*									*)
(* Applies a conversion zero or more times.				*)
(* ---------------------------------------------------------------------*)

fun REPEATQC conv tm = ORELSEQC (THENQC conv (REPEATQC conv)) ALL_QCONV tm;

(* ---------------------------------------------------------------------*)
(* CHANGED_QCONV : conv -> conv						*)
(*									*)
(* Causes the conversion given to fail if it does not change its input.	*)
(* Alpha convertibility is only tested for if the term is changed in	*)
(* some way.								*)
(* ---------------------------------------------------------------------*)

local val CQERR = ERR "CHANGED_QCONV" ""
in
fun CHANGED_QCONV conv (tm:term) =
   let val th = conv tm handle UNCHANGED => raise CQERR
       val {lhs,rhs} = dest_eq (concl th)
   in
     if aconv lhs rhs then raise CQERR else th
   end
end;

(* ---------------------------------------------------------------------*)
(* TRY_QCONV : conv -> conv						*)
(*									*)
(* Applies a conversion, and if it fails, raises a `qconv' failure	*)
(* indicating that the term is unchanged.				*)
(* ---------------------------------------------------------------------*)

fun TRY_QCONV conv = ORELSEQC conv ALL_QCONV;

(* ---------------------------------------------------------------------*)
(* SUB_QCONV : conv -> conv						*)
(*									*)
(* Applies conv to all top-level subterms of a term. Set up to detect	*)
(* `qconv' failures when dealing with a combination. If neither the 	*)
(* rator nor the rand are modified the `qconv' failure is propagated.	*)
(* Otherwise, the failure information is used to avoid unnecessary	*)
(* processing.								*)
(* ---------------------------------------------------------------------*)

fun SUB_QCONV conv tm =
 case dest_term tm
  of COMB{Rator,Rand} =>
        (let val th = conv Rator
         in MK_COMB (th, conv Rand) handle UNCHANGED => AP_THM th Rand
         end
         handle UNCHANGED => AP_TERM Rator (conv Rand))
   | LAMB{Bvar,Body} =>
         let val Bth = conv Body  (* UNCHANGED will propagate, as it should *)
         in ABS Bvar Bth
            handle HOL_ERR _ =>
              let val v = genvar (type_of Bvar)
                   val th1 = ALPHA_CONV v tm
                   val {rhs,...} = dest_eq(concl th1)
                   val {Body=Body',...} = dest_abs rhs (* v = Bvar *)
                   val eq_thm' = ABS v (conv Body')
                   (* The next 3 lines are new *)
                   val at = #rhs(dest_eq(concl eq_thm'))
                   val v' = variant (free_vars at) Bvar
                   val th2 = ALPHA_CONV v' at
               in
                 TRANS (TRANS th1 eq_thm') th2
               end
         end
   | _ => ALL_QCONV tm;


(*  Pre-August 1993
 * fun SUB_QCONV conv tm =
 *    if (is_comb tm)
 *    then let val {Rator,Rand} = dest_comb tm
 *         in
 *            let val th = conv Rator
 *            in
 *            MK_COMB (th, conv Rand)
 *            handle UNCHANGED => AP_THM th Rand
 *            end
 *            handle UNCHANGED => AP_TERM Rator (conv Rand)
 *         end
 *    else if (is_abs tm)
 *         then let val {Bvar,Body} = dest_abs tm
 *              in ABS Bvar (conv Body)
 *              end
 * (*               val bodyth = conv Body
 *  *           in
 *  *           MK_ABS (GEN Bvar bodyth)
 *  *           end
 *  ***)
 *         else ALL_QCONV tm;
 * *)

(* ---------------------------------------------------------------------*)
(* Apply a conversion recursively to a term and its parts.		*)
(* The abstraction around "t" avoids infinite recursion.		*)
(*									*)
(* Old version:								*)
(*									*)
(* letrec DEPTH_CONV conv t =						*)
(*    (SUB_CONV (DEPTH_CONV conv) THENC (REPEATC conv))			*)
(*    t;;								*)
(* ---------------------------------------------------------------------*)

fun DEPTH_QCONV conv tm =
 THENQC (SUB_QCONV (DEPTH_QCONV conv)) (REPEATQC conv) tm;

(* ---------------------------------------------------------------------*)
(* Like DEPTH_CONV, but re-traverses term after each conversion		*)
(* Loops if the conversion function never fails				*)
(*									*)
(* Old version:								*)
(*									*)
(* letrec REDEPTH_CONV conv t =						*)
(*    (SUB_CONV (REDEPTH_CONV conv) THENC				*)
(*     ((conv THENC (REDEPTH_CONV conv)) ORELSEC ALL_CONV))		*)
(*    t;;								*)
(* ---------------------------------------------------------------------*)

fun REDEPTH_QCONV conv tm =
 THENQC
   (SUB_QCONV (REDEPTH_QCONV conv))
   (ORELSEQC (THENQC conv (REDEPTH_QCONV conv)) ALL_QCONV)   tm;


(* ---------------------------------------------------------------------*)
(* Rewrite the term t trying conversions at top level before descending.*)
(* Not true Normal Order evaluation, but may terminate where		*)
(* REDEPTH_CONV would loop.  More efficient than REDEPTH_CONV for	*)
(* rewrites that throw away many of their pattern variables.		*)
(*									*)
(* Old version:								*)
(*									*)
(* letrec TOP_DEPTH_CONV conv t =					*)
(*    (REPEATC conv  THENC						*)
(*     (TRY_CONV							*)
(*         (CHANGED_CONV (SUB_CONV (TOP_DEPTH_CONV conv)) THENC		*)
(*          TRY_CONV(conv THENC TOP_DEPTH_CONV conv))))			*)
(*    t;;								*)
(*									*)
(* Slower, simpler version (tries conv even if SUB_CONV does nothing)	*)
(*									*)
(* letrec TOP_DEPTH_CONV conv t =					*)
(*    (REPEATC conv  THENC						*)
(*     SUB_CONV (TOP_DEPTH_CONV conv) THENC				*)
(*     ((conv THENC TOP_DEPTH_CONV conv)  ORELSEC ALL_CONV))		*)
(*    t;;								*)
(* ---------------------------------------------------------------------*)

fun TOP_DEPTH_QCONV conv tm =
 THENQC
 (REPEATQC conv)
 (TRY_QCONV
     (THENQC (CHANGED_QCONV (SUB_QCONV (TOP_DEPTH_QCONV conv)))
             (TRY_QCONV (THENQC conv (TOP_DEPTH_QCONV conv)))))   tm;


(* ---------------------------------------------------------------------*)
(* ONCE_DEPTH_CONV conv tm: applies conv ONCE to the first suitable	*)
(* sub-term(s) encountered in top-down order.				*)
(*									*)
(* Old Version:								*)
(*									*)
(* letrec ONCE_DEPTH_CONV conv tm =					*)
(*        (conv ORELSEC (SUB_CONV (ONCE_DEPTH_CONV conv))) tm;;		*)
(*									*)
(*									*)
(* Reimplemented: TFM 90.07.04 (optimised for speed)			*)
(*									*)
(* This version uses failure to avoid rebuilding unchanged subterms	*)
(* (now superseded by more general use of failure for optimisation).	*)
(*									*)
(* let ONCE_DEPTH_CONV =						*)
(*     letrec ODC conv tm =						*)
(*        conv tm ?							*)
(*        (let l,r = dest_comb tm in					*)
(*             (let lth = ODC conv l in					*)
(* 	         (MK_COMB(lth,ODC conv r)) ? AP_THM lth r) ?		*)
(*             AP_TERM l (ODC conv r)) ?				*)
(*        let v,body = dest_abs tm in					*)
(*        let bodyth = ODC conv body in					*)
(*            MK_ABS (GEN v bodyth) in					*)
(*        \conv tm. ODC conv tm ? REFL tm;;				*)
(* ---------------------------------------------------------------------*)

fun ONCE_DEPTH_QCONV conv tm =
 TRY_QCONV (ORELSEQC conv (SUB_QCONV (ONCE_DEPTH_QCONV conv))) tm;


(* -- From John Harrison's Hol-Lite  -- *)

fun TOP_SWEEP_QCONV conv tm =
  (THENQC (REPEATQC conv)
          (SUB_QCONV (TOP_SWEEP_QCONV conv))) tm;

end;
