
(* check ctl formulas via muCheck *)
structure ctlCheck =
struct

local

open Globals HolKernel Parse

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
open commonTools
open lazyTools

val dpfx = "cc_"

in

fun ctlCheck I1 T1 state Ric vm ksname (ic,cc) (nf,ctlf) (apl,apsubs) =
    let val _ = dbgTools.DEN dpfx "cc"(*DBG*)
	val _ = profTools.bgt (dpfx^"cc")(*PRF*)
	val (ic,cc) =
	    if Option.isSome(#th(ic)) (* possibly empty if first call *)
		then (ic,cc)
	    else let val _ = profTools.bgt (dpfx^"cc_init")(*PRF*)
		     val RTm = if Option.isSome (#ks(#mu(#abs(ic))))
				   then let val RTm = #4(Option.valOf(#ks(#mu(#abs(ic)))))
					in SOME RTm end
			       else NONE (* pick up RTm from ic; rest of model needs to be recreated from scratch *)
		     val R1 = if Ric then list_mk_conj(snd(ListPair.unzip T1)) else list_mk_disj(snd(ListPair.unzip T1))
		     val _ = profTools.bgt (dpfx^"cc_init_cks")(*PRF*)
		     val (apl,cks_def,totth,RTm,Rthm,Ithm) = mk_ctlKS I1 R1 RTm state apl vm ksname (* make ctl model *)
		     val _ = profTools.ent (dpfx^"cc_init_cks")(*PRF*)
		     val _ = profTools.bgt (dpfx^"cc_init_mks")(*PRF*)
		     val ks_def = ctl2muks_CONV Ithm Rthm cks_def (* convert to mu model *)
		     val _ = profTools.ent (dpfx^"cc_init_mks")(*PRF*)
		     val _ = dbgTools.DTH (dpfx^"cc_ ctl2muks") ks_def(*DBG*)
		     val _ = profTools.bgt (dpfx^"cc_init_pfs")(*PRF*)
		     val wfKS_ks = prove_wfKS ks_def
		     val fS = mk_comb (inst [alpha |-> type_of state] pred_setSyntax.finite_tm,mk_ks_dot_S (lhs(concl ks_def)))
		     val jf = (fn _ => prove(fS(*``FINITE (^(lhs(concl ks_def))).S``*),
					PROVE_TAC[wfKS_def,wfKS_ks,
						  BOOLVEC_UNIV_FINITE_CONV (List.length (strip_pair state))]))
		     val finS = mk_lthm (fn _ => (fS(*``FINITE (^(lhs(concl ks_def))).S``*),jf)) jf
		     val c2m = (MATCH_MP CTL2MU (LIST_CONJ [totth,wfKS_ks,finS])) (* translation theorem *)
		     val c2mm = (MATCH_MP CTL2MU_MODEL (LIST_CONJ [totth,wfKS_ks,finS])) (* translation theorem at model level *)
		     val _ = profTools.ent (dpfx^"cc_init_pfs")(*PRF*)
		     val _ = profTools.ent (dpfx^"cc_init")(*PRF*)
		 in ({ks=SOME (apl,cks_def,totth,RTm,Rthm,R1),
		     th=SOME (c2m,c2mm),
		     abs={mu={ks=SOME(apl,ks_def,wfKS_ks,RTm,SOME (Ithm,Rthm)),th=NONE},
			  mth=NONE,ks=NONE,th=NONE}},
		     cc) end
	val _ = profTools.bgt (dpfx^"cc_c2m")(*PRF*)
	val mf_thm = ctl2mu_CONV ctlf (* translate property to mu *)
	val mf = rhs(concl mf_thm)
	val _ = profTools.ent (dpfx^"cc_c2m")(*PRF*)
	val _ = profTools.ent (dpfx^"cc")(*PRF*)
	val ((tb,resthm,trace),(aic,cc)) = absCheck I1 [(".",#6(valOf(#ks(ic))))] state Ric vm ksname (#abs(ic),cc) (nf,mf) (apl,apsubs)
	val _ = profTools.bgt (dpfx^"cc")(*PRF*)
	val _ = profTools.bgt (dpfx^"cc_fin")(*PRF*)
	val (c2m,c2mm) = valOf(#th(ic))
	val tb2 = BddConv (PURE_ONCE_REWRITE_CONV [SYM (ISPEC ctlf c2m)]) (BddConv (PURE_ONCE_REWRITE_CONV [SYM mf_thm]) tb)
	val resthm2 = if isSome resthm
		      then SOME (PURE_ONCE_REWRITE_RULE [SYM(ISPEC ctlf c2mm)](PURE_ONCE_REWRITE_RULE[SYM mf_thm](valOf resthm)))
		      else resthm
	val _ = profTools.ent (dpfx^"cc_fin")(*PRF*)
	val _ = profTools.ent (dpfx^"cc")(*PRF*)
	val _ = dbgTools.DEX dpfx "cc"(*DBG*)
    in ((tb2,resthm2,trace), ({ks= #ks(ic),th = #th(ic), abs=aic},cc)) end

end
end


