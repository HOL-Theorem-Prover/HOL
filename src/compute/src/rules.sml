local open HolKernel
in

fun RULES_ERR function message =
    HOL_ERR{origin_structure = "rules",
		      origin_function = function,
		      message = message};

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

val lazy_beta_conv = beta_conv;

fun dest_eq_ty tm =
  let val{lhs,rhs} = dest_eq tm in
  {lhs=lhs, rhs=rhs, ty=type_of lhs}
  end;

(**)




fun APPL_DOWN_FUN f (thm,stk) =
  let val (thma,thmb,mkthm) = Mk_comb thm in
  (thma, (mkthm, f thmb)::stk)
  end
;

fun APPL_UP (thma,((mka,thmb)::stk)) = (mka thma thmb, stk)
  | APPL_UP _ = raise RULES_ERR "APPL_UP" ""

fun APPL_UP_FUN f (thma,((thm,thmb)::stk)) = (thm thma (f thmb), stk)
  | APPL_UP_FUN f _ = raise RULES_ERR "APPL_UP_FUN" ""


fun while_fun p f x = if p x then x else while_fun p f (f x);
fun is_nil [] = true | is_nil _ = false;

fun out_stk thstk = fst (while_fun (null o snd) APPL_UP thstk);

fun out_stk_fun f thstk = fst (while_fun (null o snd) (APPL_UP_FUN f) thstk);


(* More Beta, less matching! *)
local open Conv
in
fun FUN_IFY thm =
  let val {lhs,...} = dest_eq(concl thm)
      val x = rand lhs
      val _ = dest_var x in
  CONV_RULE (RATOR_CONV (RAND_CONV (REWR_CONV boolTheory.ETA_AX)))
    (ABS x thm)
  handle HOL_ERR _ => raise RULES_ERR "FUNIFY" ""
  end;
end;
    
fun prepare_thm thm =
  prepare_thm (FUN_IFY thm)
  handle HOL_ERR _ => thm
;


end;
