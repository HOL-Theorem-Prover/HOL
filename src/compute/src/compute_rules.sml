structure compute_rules :> compute_rules =
struct

open HolKernel boolTheory boolSyntax Drule Conv Abbrev;

(*---------------------------------------------------------------------------
 * Useful data structure to build tail recursive functions of type 'a -> 'b
 * (left to right) or 'b -> 'a (right to left), when the domain has a
 * term-like  structure.
 *---------------------------------------------------------------------------*)

datatype ('a,'b,'c) stack =
    Ztop
  | Zrator of { Rand : 'a, Ctx : ('a,'b,'c) stack }
  | Zrand of { Rator : 'b, Ctx : ('a,'b,'c) stack }
  | Zabs of { Bvar : 'c, Ctx : ('a,'b,'c) stack }
;

fun RULES_ERR function message =
    HOL_ERR{origin_structure = "compute_rules",
		      origin_function = function,
		      message = message};

(*---------------------------------------------------------------------------
 * Serious anomaly of the code (an internal invariant was broken). We don't
 * want these to be caught. We prefer a bug report.
 *---------------------------------------------------------------------------*)

exception DEAD_CODE of string;

val rhs_concl = rand o concl;

val refl_thm = REFL;
val trans_thm = TRANS;
val beta_thm = Beta;

fun evaluate th = th;


(*
val mk_comb_r = ref Thm.Mk_comb;
val mk_abs_r = ref Thm.Mk_abs;
val beta_r = ref Thm.Beta;
val eta_r = ref Thm.Eta;
val spec_r = ref Thm.Specialize;


local open timing in
fun Mk_comb th = tickt "Mk_cmb" (!mk_comb_r) th;
fun Mk_abs th = tickt "Mk_abs" (!mk_abs_r) th;
fun Beta th = tickt "Beta" (!beta_r) th;
fun Eta th = tickt "Eta" (!eta_r) th;
fun Spec th = tickt "Specialize" (!spec_r) th;
end;
*)

(* Other impl. of thm with boolean indicating progress: *)
(* about 5 to 10 % faster
type thm = Thm.thm * bool
fun rhs_concl x = (rand o concl o fst) x
val evaluate = fst

fun Mk_comb (t as (thm,_)) =
  let val (tha,thb,mka) = Thm.Mk_comb thm
      fun mka' (_,false) (_,false) = t
	| mka' (th1,_) (th2,_) = (mka th1 th2, true)
  in ((tha,false),(thb,false),mka')
  end;

fun Mk_abs (t as (thm,_)) =
  let val (bv,thb,mkl) = Thm.Mk_abs thm
      fun mkl' (_,false) = t
	| mkl' (th1,_) = (mkl th1, true)
  in (bv,(thb,false),mkl')
  end;

fun refl_thm tm = (REFL tm, false);
fun trans_thm (th1,_) th2 = (TRANS th1 th2, true);
fun beta_thm (thm,_) = (Beta thm, true);

fun try_eta' (t as (thm,_)) = ((Eta thm),true) handle HOL_ERR _ => t;
*)
(* End of alt. thm impl. *)


fun try_eta thm = (Eta thm) handle HOL_ERR _ => thm;

(*---------------------------------------------------------------------------
 * Precondition: f(arg) is a closure corresponding to b.
 * Given   (arg,(|- M = (a b), Stk)),
 * returns (|- a = a, (<fun>,(|- b = b, f(arg)))::Stk)
 * where   <fun> =  (|- a = a' , |- b = b') |-> |- M = (a' b')
 *---------------------------------------------------------------------------*)

fun push_in_stk f (arg,(th,stk)) =
      let val (tha,thb,mka) = Mk_comb th in
      (tha, Zrator{Rand=(mka,(thb,f arg)), Ctx=stk})
      end
;

fun push_lam_in_stk (th, stk) =
      let val (_,thb,mkl) = Mk_abs th in
      (thb, Zabs{Bvar=try_eta o mkl, Ctx=stk})
      end
;


(*---------------------------------------------------------------------------
  Does conversions between
                              FUNIFY
    |- (c t_1 .. t_n x) = M    --->   |- (c t_1 .. t_n) = \x. M
                               <---
                             UNFUNIFY
   In UNFUNIFY, we must avoid choosing an x that appears free in t_1..t_n.
 ---------------------------------------------------------------------------*)

local fun RAND_CONV conv tm =
        let val (Rator,Rand) = dest_comb tm in AP_TERM Rator (conv Rand) end
      fun RATOR_CONV conv tm =
        let val (Rator,Rand) = dest_comb tm in AP_THM (conv Rator) Rand end
      fun CONV_RULE conv th = EQ_MP (conv(concl th)) th;
in
fun FUNIFY thm =
  let val x = rand (lhs (concl thm)) in
  CONV_RULE (RATOR_CONV (RAND_CONV (REWR_CONV ETA_AX))) (ABS x thm)
  end
  handle HOL_ERR _ => raise RULES_ERR "FUNIFY" ""

fun UNFUNIFY thm =
  let val (lhs,rhs) = dest_eq (concl thm)
      val x = variant (free_vars lhs) (bvar rhs) in
  CONV_RULE (RAND_CONV BETA_CONV) (AP_THM thm x)
  end
  handle HOL_ERR _ => raise RULES_ERR "UNFUNIFY" ""

end;

fun repeat_on_conj f thm =
  let fun iter th = iter (f th) handle HOL_ERR _ => th
  in LIST_CONJ (List.map iter (BODY_CONJUNCTS thm))
  end;

val lazyfy_thm = repeat_on_conj FUNIFY;
val strictify_thm = repeat_on_conj UNFUNIFY;

(* Ensures a theorem is an equality. *)
fun eq_intro thm =
  if is_eq (concl thm) then thm else 
  if is_neg (concl thm) then EQF_INTRO thm
                        else EQT_INTRO thm;

end;
