
(* check ctl formulas via muCheck *)
structure ctlCheck =
struct

local 

open Globals HolKernel Parse goalstackLib

open boolSyntax
open pairSyntax
open PairRules
open muTheory
open ctl2muTheory
open ksTheory
open muCheck
open ctl2muTools
open Drule
open ksTools
open PrimitiveBddRules
open ctlTools
open bddTools
open bossLib
open Drule
open Tactical
open Conv
open Rewrite
open Tactic
open ctlTheory
open cearTools
open Binarymap
open boolTheory
open holCheckTools

in

fun ctlCheck I1 R1 state vm apl ksname init_cache ctlf  = 
    let val ((c2m,c2mm),abs_init_cache) = 
	    if Option.isSome init_cache andalso Option.isSome (fst (Option.valOf init_cache))
		then (Option.valOf(fst(Option.valOf init_cache)),snd(Option.valOf init_cache))
	    else let val RTm = if Option.isSome init_cache andalso (Option.isSome (snd (Option.valOf init_cache))) 
				   then let val (_,_,_,RTm) = Option.valOf(#1(Option.valOf (snd (Option.valOf init_cache))))
					in SOME RTm end 
			       else NONE (* pick up RTm from init_cache; rest of model needs to be recreated from scratch *)
		     val (apl,cks_def,totth,RTm,Rthm) = mk_ctlKS I1 R1 RTm state apl vm ksname (* make ctl model *)
		     val ks_def = ctl2muks_CONV Rthm cks_def (* convert to mu model *)
		     val wfKS_ks = prove_wfKS ks_def 
		     val finS = prove(``FINITE (^(lhs(concl ks_def))).S``,
					PROVE_TAC[wfKS_def,wfKS_ks,
						  BOOLVEC_UNIV_FINITE_CONV (List.length (strip_pair state))])
		     val c2m = (MATCH_MP CTL2MU (LIST_CONJ [totth,wfKS_ks,finS])) (* translation theorem *)
		     val c2mm = (MATCH_MP CTL2MU_MODEL (LIST_CONJ [totth,wfKS_ks,finS])) (* translation theorem at model level *)
		     val abs_init_cache_snd = 
			 if Option.isSome init_cache andalso (Option.isSome (snd (Option.valOf init_cache))) 
			     then  #2(Option.valOf (snd (Option.valOf init_cache)))
			 else NONE
		     val abs_init_cache_thd = 
			 if Option.isSome init_cache andalso (Option.isSome (snd (Option.valOf init_cache))) 
			     then let val (a,b,c,d,e,_,f) = Option.valOf(#3(Option.valOf (snd (Option.valOf init_cache))))
				  in SOME (a,b,c,d,e,(TRUTH,TRUTH,TRUTH),f) end 
			 else NONE
		 in ((c2m,c2mm),SOME (SOME (apl,ks_def,wfKS_ks,RTm),abs_init_cache_snd,abs_init_cache_thd)) end
	val Ric = is_conj R1
	val mf_thm = ctl2mu_CONV ctlf (* translate property to mu *)
	val mf = rhs(concl mf_thm)
	val ((tb,resthm,trace),abs_init_cache) = absCheck I1 [(".",R1)] state Ric vm apl ksname abs_init_cache mf 
	val tb2 = BddConv (PURE_ONCE_REWRITE_CONV [SYM (ISPEC ctlf c2m)]) (BddConv (PURE_ONCE_REWRITE_CONV [SYM mf_thm]) tb)
	val resthm2 = if Option.isSome resthm 
		      then SOME (PURE_ONCE_REWRITE_RULE [SYM(ISPEC ctlf c2mm)](PURE_ONCE_REWRITE_RULE[SYM mf_thm](Option.valOf resthm)))
		      else resthm
    in ((tb2,resthm2,trace), SOME (SOME (c2m,c2mm),abs_init_cache)) end

end
end


