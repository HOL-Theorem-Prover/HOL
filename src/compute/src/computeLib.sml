structure computeLib :> computeLib =
struct 

open HolKernel clauses rules equations;

(* reexporting types from clauses *)
type rewrite = rewrite;
type comp_rws = comp_rws;


fun push_in_stk env (arg,(th,stk)) =
      let val (tha,thb,mka) = Mk_comb th in
      (tha, (mka,(thb,mk_clos(env,arg)))::stk)
      end
;

(* [cbv_wk ((th,cl),stk)] puts the closure cl (useful information about
 * the rhs of th) in head normal form (weak reduction). It returns either
 * a closure which term is an abstraction, a variable applied to strongly
 * reduced arguments, or a constant applied to weakly reduced arguments
 * which does not match any rewriting rule.
 * 
 * - substitution is propagated through applications.
 * - if the rhs is an abstraction and there is one arg on the stack,
 *   this means we found a beta redex. mka rebuilds the application of
 *   the function to its argument, and Beta does the actual beta step.
 * - if there is no argument, then we reached the head normal form.
 * - closures are not delayed on variables: only applications and abstractions.
 * - for a neutral value (ie. a variable applied to args), we strongly
 *   normalize its arguments, and this makes up a neutral value.
 * - for an applied constant, we look for a rewrite matching it.
 *   If we found one, then we apply the instanciated rule, and go on.
 *   Otherwise, we call cbv_wk_cst, which weakly reduces the first argument,
 *   append it to the constant, and resumes weak head reduction.
 *)
fun cbv_wk ((th,CLOS{Env, Term=App(a,args)}), stk) = 
      let val (tha,stk') = foldl (push_in_stk Env) (th,stk) args in
      cbv_wk ((tha, mk_clos(Env,a)), stk')
      end
  | cbv_wk ((th,CLOS{Env, Term=Abs body}), (mka,(thb,cl))::s') =
      cbv_wk ((Beta(mka th thb), mk_clos(cl :: Env, body)), s')
  | cbv_wk (clos as (_,CLOS _), []) = clos
  | cbv_wk ((_, CLOS _), _) = raise DEAD_CODE "cbv_wk"
  | cbv_wk ((th, NEUTR), stk) =
      (out_stk_fun (fn clos => strong(cbv_wk(clos,[]))) (th,stk), NEUTR)
  | cbv_wk ((th, CST cargs), stk) =
      (case reduce_cst cargs of
	LEFT{Thm,Residue} => cbv_wk ((TRANS th Thm, Residue), stk)
      |	RIGHT cst => cbv_wk_cst (th,cst,stk))

and cbv_wk_cst (th, cargs, [])                = (th, CST cargs)
  | cbv_wk_cst (th, cargs, (mka,clos) :: stk) =
      let val (thb',v) = cbv_wk (clos,[]) in
      cbv_wk ((mka th thb', comb_ct cargs (rand (concl thb'),v)), stk)
      end

(* [strong] continues the reduction of a term in head normal form under
 * abstractions, and in the arguments of non reduced constant.
 * - the arguments of a constant are first moved to the stack, and then
 *   out_stk_fun strongly normalize them from left to right (they already 
 *   are in head normal form).
 * - in the case of neutral terms, we are already done
 * - we cross an abstraction by creating a new free variable we push in the
 *   environment, reduce the body, and rebuild the abstraction. We then try
 *   eta-reduction.
 *) 
and strong (th, CST {Args,...}) =
      let fun eval_arg ((_,arg),tstk) = 
	        APPL_DOWN_FUN (fn thb => (thb,arg)) tstk in
      out_stk_fun strong (foldl eval_arg (th,[]) Args)
      end
  | strong (th, NEUTR) = th
  | strong (th, CLOS{Env, Term=Abs t}) =
      let val (_,thb,mkl) = Mk_abs th in
      try_eta(mkl(strong (cbv_wk ((thb, mk_clos(NEUTR :: Env, t)),[]))))
      end
  | strong _ = raise DEAD_CODE "strong: closure should be an abstraction"
;

fun norm_wk rws t =
  let val clos = mk_clos([],from_term rws [] t) in
  cbv_wk ((REFL t, clos), [])
  end;


(* [CBV_CONV rws t] is a conversion that does the full normalization of t,
 * using rewrites rws.
 *)
fun CBV_CONV rws t = strong (norm_wk rws t);
fun WEAK_CBV_CONV rws t = fst (norm_wk rws t);

end;
