local open HolKernel boolTheory
in

fun RULES_ERR function message =
    HOL_ERR{origin_structure = "rules",
		      origin_function = function,
		      message = message};

(* Serious anomaly of the code (an internal invariant was broken). We don't
 * want these to be caught. We prefer a bug report.
 *)
exception DEAD_CODE of string;

(* less efficient implementation of Mk_comb, Mk_abs and Beta: *)

fun Mk_comb th =
  let val {Rator,Rand} = dest_comb(rhs (concl th)) in
  (REFL Rator, REFL Rand, (fn th1 => fn th2 => TRANS th (MK_COMB(th1,th2))))
  end;

fun Mk_abs th =
  let val {Bvar,Body} = dest_abs(rhs (concl th)) in
  (Bvar, REFL Body, (fn th1 => TRANS th (ABS Bvar th1)))
  end;

val Beta = Drule.RIGHT_BETA;

fun Eta thm = TRANS thm (ETA_CONV (rhs (concl thm)));

val lazy_beta_conv = beta_conv;

fun dest_eq_ty tm =
  let val{lhs,rhs} = dest_eq tm in
  {lhs=lhs, rhs=rhs, ty=type_of lhs}
  end;

fun Spec tm thm = SPEC tm thm;

(* end of inefficient implementation. *)


fun try_eta thm = (Eta thm) handle HOL_ERR _ => thm;



fun APPL_DOWN_FUN f (thm,stk) =
  let val (thma,thmb,mkthm) = Mk_comb thm in
  (thma, (mkthm, f thmb)::stk)
  end
;

fun APPL_UP (thma,((mka,thmb)::stk)) = (mka thma thmb, stk)
  | APPL_UP _ = raise RULES_ERR "APPL_UP" ""

fun APPL_UP_FUN f (thma,((thm,thmb)::stk)) = (thm thma (f thmb), stk)
  | APPL_UP_FUN f _ = raise RULES_ERR "APPL_UP_FUN" ""


fun until_fun p f x = if p x then x else until_fun p f (f x);

fun out_stk x = (fst o (until_fun (null o snd) APPL_UP)) x;
fun out_stk_fun f = fst o (until_fun (null o snd) (APPL_UP_FUN f));


(* Does conversions between
                            FUNIFY
     (c t_1 .. t_n x) = M    --->   (c t_1 .. t_n) = \x. M
                             <---
                           UNFUNIFY
   In UNFUNIFY, we must avoid choosing an x that appears free in t_1..t_n.
 *)
local open Conv
in
fun FUNIFY thm =
  let val x = rand (lhs (concl thm)) in
  CONV_RULE (RATOR_CONV (RAND_CONV (REWR_CONV ETA_AX))) (ABS x thm)
  end
  handle HOL_ERR _ => raise RULES_ERR "FUNIFY" ""

and UNFUNIFY thm =
  let val {lhs,rhs} = dest_eq (concl thm)
      val x = variant (free_vars lhs) (bvar rhs) in
  CONV_RULE (RAND_CONV BETA_CONV) (AP_THM thm x)
  end
  handle HOL_ERR _ => raise RULES_ERR "UNFUNIFY" ""

end;
  
fun lazyfy_thm thm =
  lazyfy_thm (FUNIFY thm)
  handle HOL_ERR _ => thm
;

fun strictify_thm thm =
  strictify_thm (UNFUNIFY thm)
  handle HOL_ERR _ => thm
;

end;
