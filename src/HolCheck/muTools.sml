(*List.app load ["bossLib","stringTheory","stringLib","HolBddLib","pairTheory","pred_setLib","listLib","CTL","pairSyntax","pairRules","pairTools","muTheory","boolSyntax","Drule","Tactical","Conv","Rewrite","Tactic","boolTheory"];*)

structure muTools =
struct

local

open Globals HolKernel Parse goalstackLib

open bossLib pairTheory pred_setTheory pred_setLib stringLib listTheory simpLib pairSyntax pairLib PrimitiveBddRules DerivedBddRules Binarymap PairRules pairTools boolSyntax Drule Tactical Conv Rewrite Tactic boolTheory listSyntax stringTheory boolSimps pureSimps listSimps numLib
open setLemmasTheory muSyntax muSyntaxTheory muTheory reachTheory stringBinTree bddTools envTheory envTools lazyTools commonTools

in

val _ = set_trace "notify type variable guesses" 0;
val IS_PROP_tm = ``muSyntax$IS_PROP``; (* FIXME: this should be in muSyntax? *)
val _ = set_trace "notify type variable guesses" 0;

fun mk_tysimps sel p_ty = 
(fn _ => ((List.hd(CONJUNCTS(List.last(tsimps ``:'a mu``))))
				     ::((List.filter (fn th => can (match_term 
									(``~(((RV a):'prop mu) = (b:'prop mu))``)) 
								   (concl (SPEC_ALL th))) (tsimps ``:'a mu``))@
					(List.filter (fn th => can (match_term 
									(``~(((Not a):'prop mu) = (b:'prop mu))``)) 
								   (concl (SPEC_ALL th))) (tsimps ``:'a mu``))),sel))

fun mk_imf_thm imftm mf tysimps prop_type = 
    let val jf = (fn _ => 
		     let val (tysimps,sel) = tysimps() 
		     in prove(``IMF (^mf)``,SIMP_TAC std_ss ([IMF_def,MU_SUB_def,NNF_def,RVNEG_def]@tysimps@sel)) end) 
    in  mk_lthm (fn _ => (mk_comb(imftm,mf),jf)) jf end

fun prove_is_prop p_ty mf = 
    let val th1 = PURE_REWRITE_CONV [IS_PROP_def] (mk_comb (inst [alpha |-> p_ty] IS_PROP_tm,mf))
    in REWRITE_RULE [ISPEC (rhs(concl th1)) EQ_CLAUSES] th1 end

(* FIXME: in many places, awkward use of BddEqMp can be replaced by cleaner eqToTermBdd *)  
end
end
