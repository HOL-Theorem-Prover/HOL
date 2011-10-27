structure compute_rules :> compute_rules =
struct

open HolKernel boolTheory boolSyntax Drule Conv Abbrev;

(*---------------------------------------------------------------------------
 * Useful data structure to build tail recursive functions of type 'a -> 'b
 * (left to right) or 'b -> 'a (right to left), when the domain has a
 * term-like  structure.
 *---------------------------------------------------------------------------*)

datatype ('a,'b,'c,'d,'e) stack =
    Ztop
  | Zrator of { Rand : 'a, Ctx : ('a,'b,'c,'d,'e) stack }
  | Zrand of { Rator : 'b, Ctx : ('a,'b,'c,'d,'e) stack }
  | Zabs of { Bvar : 'c, Ctx : ('a,'b,'c,'d,'e) stack }
  | Ztyrator of { Rand : 'd, Ctx : ('a,'b,'c,'d,'e) stack }
  | Ztyabs of { Bvar : 'e, Ctx : ('a,'b,'c,'d,'e) stack }
;

fun pp_stack (ppa, ppb, ppc, ppd, ppe) pps (stk : ('a,'b,'c,'d,'e) stack) =
  let open Portable
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     val ppa = ppa pps
     val ppb = ppb pps
     val ppc = ppc pps
     val ppd = ppd pps
     val ppe = ppe pps
     fun pp (Ztop) =
          ( add_string "Ztop" )
       | pp (Zrator{Rand,Ctx}) =
          ( add_string "Zrator:   "; ppa Rand;
            add_string ","; add_break (1,0);
            pp Ctx )
       | pp (Zrand{Rator,Ctx}) =
          ( add_string "Zrand:    "; ppb Rator;
            add_string ","; add_break (1,0);
            pp Ctx )
       | pp (Zabs{Bvar,Ctx}) =
          ( add_string "Zabs:     "; ppc Bvar;
            add_string ","; add_break (1,0);
            pp Ctx )
       | pp (Ztyrator{Rand,Ctx}) =
          ( add_string "Ztyrator: "; ppd Rand;
            add_string ","; add_break (1,0);
            pp Ctx )
       | pp (Ztyabs{Bvar,Ctx}) =
          ( add_string "Ztyabs:   "; ppe Bvar;
            add_string ","; add_break (1,0);
            pp Ctx );
 in
   add_string "[";
   begin_block CONSISTENT 0;
   pp stk;
   end_block();
   add_string "]"
 end

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
val tybeta_thm = TyBeta;

fun evaluate th = th;


(*
val mk_comb_r = ref Thm.Mk_comb;
val mk_abs_r = ref Thm.Mk_abs;
val beta_r = ref Thm.Beta;
val tybeta_r = ref Thm.TyBeta;
val eta_r = ref Thm.Eta;
val tyeta_r = ref Thm.TyEta;
val spec_r = ref Thm.Specialize;
val tyspec_r = ref Thm.TySpecialize;


local open timing in
fun Mk_comb th = tickt "Mk_cmb" (!mk_comb_r) th;
fun Mk_abs th = tickt "Mk_abs" (!mk_abs_r) th;
fun Beta th = tickt "Beta" (!beta_r) th;
fun TyBeta th = tickt "TyBeta" (!tybeta_r) th;
fun Eta th = tickt "Eta" (!eta_r) th;
fun TyEta th = tickt "TyEta" (!tyeta_r) th;
fun Spec th = tickt "Specialize" (!spec_r) th;
fun TySpec th = tickt "TySpecialize" (!tyspec_r) th;
end;
*)

(* Other impl. of thm with boolean indicating progress: *)
(* about 5 to 10 % faster
type thm = Thm.thm * bool
fun rhs_concl x = (rand o concl o fst) x
val evaluate = fst

fun Mk_comb (t as (thm,_)) =
  let val (tha,thb,mka) = Thm.Mk_comb thm
          handle e => (print "Mk_comb:\n"; print_thm thm; Raise e)
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

fun Mk_tycomb (t as (thm,_)) =
  let val (tha,tyb,mka) = Thm.Mk_tycomb thm
      fun mka' (_,false) = t
	| mka' (th1,_) = (mka th1, true)
  in ((tha,false),tyb,mka')
  end;

fun Mk_tyabs (t as (thm,_)) =
  let val (bv,thb,mkl) = Thm.Mk_tyabs thm
      fun mkl' (_,false) = t
	| mkl' (th1,_) = (mkl th1, true)
  in (bv,(thb,false),mkl')
  end;

fun refl_thm tm = (REFL tm, false);
fun trans_thm (th1,_) th2 = (TRANS th1 th2, true);
fun beta_thm (thm,_) = (Beta thm, true);
fun tybeta_thm (thm,_) = (TyBeta thm, true);

fun try_eta' (t as (thm,_)) = ((Eta thm),true) handle HOL_ERR _ => t;
fun try_tyeta' (t as (thm,_)) = ((TyEta thm),true) handle HOL_ERR _ => t;
*)
(* End of alt. thm impl. *)


fun try_eta thm = (RIGHT_ETA thm) handle HOL_ERR _ => thm;
fun try_tyeta thm = (RIGHT_TY_ETA thm) handle HOL_ERR _ => thm;

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

fun push_tycomb_in_stk (arg,(th,stk)) =
      let val (tha,_,mkl) = Mk_tycomb th in
      (tha, Ztyrator{Rand=(mkl,arg), Ctx=stk})
      end
;

fun push_tylam_in_stk (th, stk) =
      let val (_,thb,mkl) = Mk_tyabs th in
      (thb, Ztyabs{Bvar=try_tyeta o mkl, Ctx=stk})
      end
;

fun push_arg_in_stk (inL arg,(th,stk)) = push_tycomb_in_stk (arg,(th,stk))
  | push_arg_in_stk (inR arg,(th,stk)) = push_in_stk snd (arg,(th,stk))
;


(*---------------------------------------------------------------------------
  Does conversions between
                              FUNIFY
    |- (c t_1 .. t_n x) = M    --->   |- (c t_1 .. t_n) = \x. M
                               <---
                             UNFUNIFY
   In UNFUNIFY, we must avoid choosing an x that appears free in t_1..t_n.
   The t_i's may be individually either terms (c t_1 ...)
                                     or types (c [:ty_1:] ...)
 ---------------------------------------------------------------------------*)

local fun RAND_CONV conv tm =
        let val (Rator,Rand) = dest_comb tm in AP_TERM Rator (conv Rand) end
      fun RATOR_CONV conv tm =
        let val (Rator,Rand) = dest_comb tm in AP_THM (conv Rator) Rand end
      fun CONV_RULE conv th = EQ_MP (conv(concl th)) th;
in
fun FUNIFY thm =
  let val left = lhs (concl thm) in
  if is_comb left then
    let val x = rand left in
      CONV_RULE (RATOR_CONV (RAND_CONV (REWR_CONV ETA_AX))) (ABS x thm)
    end
  else
    let val ty = tyrand left in
      CONV_RULE (RATOR_CONV (RAND_CONV (REWR_CONV TY_ETA_AX))) (TY_ABS ty thm)
    end
  end
  handle HOL_ERR _ => raise RULES_ERR "FUNIFY" ""

fun UNFUNIFY thm =
  let val (lhs,rhs) = dest_eq (concl thm) in
  if is_abs rhs then
    let val x = variant (free_vars lhs) (bvar rhs) in
      CONV_RULE (RAND_CONV BETA_CONV) (AP_THM thm x)
    end
  else
    let val a = variant_type (type_vars_in_term lhs) (btyvar rhs) in
      CONV_RULE (RAND_CONV TY_BETA_CONV) (TY_COMB thm a)
    end
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
