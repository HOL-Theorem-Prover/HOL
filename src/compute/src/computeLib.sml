structure computeLib :> computeLib =
struct 

open HolKernel clauses rules equations;

(* reexporting types from clauses *)
type rewrite = rewrite;
type comp_rws = comp_rws;


datatype stack =
    Ztop
  | Zappl of (thm->thm->thm) * (thm * db fterm) * stack
  | Zappr of (thm->thm->thm) * (thm * db fterm) * stack
  | Zabs of (thm->thm) * stack
;

fun initial_state rws t =
  ((REFL t, mk_clos([],from_term rws [] t)), Ztop);


(* Precondition: f(arg) is a closure corresponding to b.
 * Given   (arg,(|- M = (a b), Stk)),
 * returns (|- a = a, (<fun>,(|- b = b, f(arg)))::Stk)
 * where   <fun> =  (|- a = a' , |- b = b') |-> |- M = (a' b')
 *)
fun push_in_stk f (arg,(th,stk)) =
      let val (tha,thb,mka) = Mk_comb th in
      (tha, Zappl(mka,(thb,f arg),stk))
      end
;

(* [cbv_wk ((th,cl),stk)] puts the closure cl (useful information about
 * the rhs of th) in head normal form (weak reduction). It returns either
 * a closure which term is an abstraction, in a context other than Zappl,
 * a variable applied to strongly
 * reduced arguments, or a constant applied to weakly reduced arguments
 * which does not match any rewriting rule.
 * 
 * - substitution is propagated through applications.
 * - if the rhs is an abstraction and there is one arg on the stack,
 *   this means we found a beta redex. mka rebuilds the application of
 *   the function to its argument, and Beta does the actual beta step.
 * - for an applied constant, we look for a rewrite matching it.
 *   If we found one, then we apply the instanciated rule, and go on.
 *   Otherwise, we try to rebuild the thm.
 * - for an already strongly normalized term, we try to rebuild the thm.
 *)
fun cbv_wk ((th,CLOS{Env, Term=App(a,args)}), stk)                    = 
      let val (tha,stk') =
            foldl (push_in_stk (curry mk_clos Env)) (th,stk) args in
      cbv_wk ((tha, mk_clos(Env,a)), stk')
      end
  | cbv_wk ((th,CLOS{Env, Term=Abs body}),    Zappl(mka,(thb,cl),s')) =
      cbv_wk ((Beta(mka th thb), mk_clos(cl :: Env, body)), s')
  | cbv_wk ((th, CST cargs),                  stk)                    =
      (case reduce_cst cargs of
	LEFT{Thm,Residue} => cbv_wk ((TRANS th Thm, Residue), stk)
      |	RIGHT cst => cbv_up ((th,CST cst), stk))
  | cbv_wk (clos,                             stk)                    =
      cbv_up (clos,stk)

(* *)
and cbv_up (cl,          Zappl(mka,clos,stk))           =
      cbv_wk (clos,Zappr(mka,cl,stk))
  | cbv_up ((thb,v),     Zappr(mka,(th,CST cargs),stk)) =
      cbv_wk ((mka th thb, comb_ct cargs (rand (concl thb),v)), stk)
  | cbv_up ((thb,NEUTR), Zappr(mka,(th,NEUTR),stk))     =
      cbv_up ((mka th thb, NEUTR), stk)
  | cbv_up (_,           Zappr(_,(_,CLOS _),_))         =
      raise DEAD_CODE "cbv_up"
  | cbv_up (clos,        stk)                           =
      (clos,stk)
;

(* [strong] continues the reduction of a term in head normal form under
 * abstractions, and in the arguments of non reduced constant.
 *
 * Note: we lose the info that args of CST are already weak normal forms...
 *) 
fun strong ((th, CLOS{Env,Term=Abs t}), stk) =
      let val (_,thb,mkl) = Mk_abs th in
      strong (cbv_wk ((thb, mk_clos(NEUTR :: Env, t)), Zabs(mkl,stk)))
      end
  | strong ((_, CLOS _),                _) =
      raise DEAD_CODE "strong"
  | strong ((th,CST {Args,...}),        stk) =
      strong_up (foldl (push_in_stk snd) (th,stk) Args)
  | strong ((th, NEUTR),                stk) =
      strong_up (th,stk)

and strong_up (th, Ztop) = th
  | strong_up (th, Zappl(mka,clos,stk)) =
      strong (cbv_wk (clos, Zappr(mka,(th,NEUTR),stk)))
  | strong_up (th, Zappr(mka,(tha,_),stk)) = strong_up (mka tha th, stk)
  | strong_up (th, Zabs(mkl,stk)) = strong_up (try_eta (mkl th), stk)
;


(* [CBV_CONV rws t] is a conversion that does the full normalization of t,
 * using rewrites rws.
 *)
fun CBV_CONV rws t = strong (cbv_wk (initial_state rws t));

(* WEAK_CBV_CONV is the same as CBV_CONV except that it does not reduce
 * under abstractions, and reduce weakly the arguments of constants.
 *)
fun WEAK_CBV_CONV rws t = fst (fst (cbv_wk (initial_state rws t)));

end;
