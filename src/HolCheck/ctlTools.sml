structure ctlTools =
struct

local 

open Globals HolKernel Parse

open bossLib
open pairTheory
open pred_setTheory
open pred_setLib
open stringLib
open listTheory
open simpLib
open pairSyntax 
open pairLib
open PrimitiveBddRules
open DerivedBddRules
open Binarymap
open PairRules
open pairTools
open setLemmasTheory
open boolSyntax
open Drule
open Tactical
open Conv
open Rewrite
open Tactic
open bddTools
open stringBinTree
open ctlTheory
open boolTheory
open ksTheory
open ksTools
open commonTools
open lzPairRules
open lazyTools

val dpfx = "cto_"

in 

(* attempt to prove R1 is total by confirming that term-bdd for !s . ?s'. R(s,s') is true. *)
(* this raises an exception if R1 is not total. totalisation is done elsewhere (see totalise and mk_ctlKS below) *)
(* ASSERT: Rtb's term is just R(s,s') *)
fun total_CONV R1 state Rtb = 
    let val _ = dbgTools.DEN dpfx "tC" (*DBG*)
	val state' = mk_primed_state state
	val (st,st') = (strip_pair##strip_pair) (state,state')
	val tb = BddForall st (BddExists st' Rtb)
	val th1 = BddThmOracle tb handle ex => (dbgTools.DEX dpfx "tC"; raise ex)
	val th2 = CONV_RULE (RHS_CONV (STRIP_QUANT_CONV commonTools.ELIM_TUPLED_QUANT_CONV)) 
	    (commonTools.ELIM_TUPLED_QUANT_CONV (mk_pforall(state,mk_pexists(state',R1))))(*mk_comb( rator(getTerm Rtb),
											mk_pair(state,state'))))))*)
	val th3 = PURE_ONCE_REWRITE_RULE [SYM th2] th1 
	val th4 = CONV_RULE (RHS_CONV (GEN_PALPHA_CONV state)) (CONV_RULE (RHS_CONV (QUANT_CONV (GEN_PALPHA_CONV state'))) 
								(ISPEC (mk_pabs(mk_pair(state,state'),R1)) TOTAL_def))
	val th5 = PURE_ONCE_REWRITE_RULE [PBETA_CONV (snd(dest_pexists(snd(dest_pforall(rhs(concl th4))))))] th4
	val th6 = PURE_ONCE_REWRITE_RULE [SYM th5] th3
	val _ = dbgTools.DEX dpfx "tC" (*DBG*)
    in th6 end 

(* Convert map from names to terms to names to term_bdds.
   NOTE: the use of termToTermBddFun requires that the term argument not contain any uninterpreted constants.  
   T is a (string * term) list where each pair is (action name, corresponding transition relation)
   vm is term_bdd varmap
   OUT: a map : name of action -> termbdd of corresponding transition relation also add the dot action      
   FIXME: fix NOTE issue above *)
fun RmakeTmap T vm Ric =
	let fun makeR (h::t) mp = makeR t (insert(mp,(fst h),
		DerivedBddRules.GenTermToTermBdd (!DerivedBddRules.termToTermBddFun) vm (snd h)))
		|   makeR [] mp = mp
            val mp = mkDict String.compare
	    val U_T = if Ric then list_mk_conj(snd(unzip T)) else list_mk_disj(snd(unzip T))
            val Tmap = makeR T mp	
	in insert(Tmap,".",DerivedBddRules.GenTermToTermBdd (!DerivedBddRules.termToTermBddFun) vm (U_T)) end

(* return totalised version of transition relation with proof, as well as appropriately modified term-bdd *)
fun totalise state state' total_tm Rtb vm R1 = 
    let val _ = dbgTools.DEN dpfx "tot" (*DBG*)
	val (s,sp) = (strip_pair##strip_pair) (state,state')	
	val self = list_mk_conj(List.map (fn v => mk_eq(mk_bool_var (v^"'"),mk_bool_var v)) (List.map term_to_string s))
	val tbt = BddNot(BddExists sp Rtb) (* terminal states*)
	val _ = profTools.bgt (dpfx^"tot_tbl")(*PRF*)
	val tbl = BddConv(PURE_ONCE_REWRITE_CONV[REWRITE_CONV[GEN_ALL(SYM PAIR_EQ)]self])(t2tb vm self)(* all states have self loops*) 
	val _ = profTools.ent (dpfx^"tot_tbl")(*PRF*)
	val tbtl = BddOp(bdd.And,tbt,tbl) (* terminal states with self loops *)
	val _ = dbgTools.DTB (dpfx^"tot_ tbtl") tbtl (*DBG*)
	val _ = dbgTools.DTM (dpfx^"tot_ pexists state' Rtb")  (mk_pexists(state',getTerm Rtb)) (*DBG*)
	val _ = profTools.bgt (dpfx^"tot_Rt2")(*PRF*)
	val Rtb2 = BddConv (PURE_ONCE_REWRITE_CONV [SYM (commonTools.lzELIM_TUPLED_QUANT_CONV (mk_pexists(state',getTerm Rtb)))]) 
			   (BddOp(bdd.Or,Rtb,tbtl))
	val _ = profTools.ent (dpfx^"tot_Rt2")(*PRF*)
	val _ = dbgTools.DTB (dpfx^"tot_ Rtb2") Rtb2 (*DBG*)
	val _ = dbgTools.DTM (dpfx^"tot_ R1") R1 (*DBG*)
	val R1t = getTerm Rtb2 (* new totalised transition relation*)
	val _ = profTools.bgt (dpfx^"tot_th")(*PRF*)
	val jf = (fn _ => lzPBETA_RULE 
			      (CONV_RULE (RAND_CONV (lzGEN_PALPHA_CONV (mk_pair(state,state'))))(* proof R1t is total*) 
					 (CONV_RULE(RAND_CONV(lzPABS_CONV(RAND_CONV (LAND_CONV (RAND_CONV(lzGEN_PALPHA_CONV state'))))))
 						    (ISPEC  (mk_pabs(mk_pair(state,state'),R1)) TOTAL_THM))))
	val totth = mk_lthm (fn _ => (mk_comb(total_tm,mk_pabs(mk_pair(state,state'),R1t)),jf)) jf
	val _ = profTools.ent (dpfx^"tot_th")(*PRF*)
	val _ = dbgTools.DTH (dpfx^"tot_ totth") totth (*DBG*)
	val _ = dbgTools.DEX dpfx "tot" (*DBG*)
    in (R1t,totth,Rtb2) end

(* create ks:('prop,'state) kripke_structure, making sure R is total (totalise if necessary); also return tb of R for model checker*)
fun mk_ctlKS I1 R1 RTm state apl vm ksname = 
    let 
	val _ = dbgTools.DEN dpfx "mc" (*DBG*)
	val state' = mk_primed_state state  
	val Ric = is_conj R1
	val _ = profTools.bgt (dpfx^"mc_rm")(*PRF*) 
	val RTm = if Option.isSome RTm then Option.valOf RTm else RmakeTmap [(".",R1)] vm Ric 
	val Rtb = Binarymap.find(RTm,".")
	val _ = profTools.ent (dpfx^"mc_rm")(*PRF*) 
	val _ = profTools.bgt (dpfx^"mc_totc")(*PRF*)
	val totth = total_CONV R1 state Rtb handle ex => TRUTH
	val _ = profTools.ent (dpfx^"mc_totc")(*PRF*)
	val _ = dbgTools.DTH (dpfx^"mc_ totth1") totth (*DBG*)
        val _ = dbgTools.DTB (dpfx^"mc_ Rtb3") Rtb (*DBG*)
	val state_type = type_of state
	val total_tm = inst [alpha|->state_type,beta|->state_type] (rator(lhs(concl(SPEC_ALL TOTAL_def))))
	val _ = profTools.bgt (dpfx^"mc_tot")(*PRF*) 
	val (R1t,totth,Rtb) = if (Term.compare(concl(totth),T)=EQUAL) then totalise state state' total_tm Rtb vm R1 else (R1,totth,Rtb)
	val _ = profTools.ent (dpfx^"mc_tot")(*PRF*)
        val _ = dbgTools.DTB (dpfx^"mc_ Rtb4") Rtb (*DBG*)
	val _ = profTools.bgt (dpfx^"mc_kd")(*PRF*)
	val _ = profTools.bgt (dpfx^"mc_kd_a")(*PRF*)
	val apl =  if (Option.isSome apl) then Option.valOf apl
		   else List.map (fn ap => mk_pabs(state,ap)) (get_APs (mk_conj (R1,I1)))
	val _ = profTools.ent (dpfx^"mc_kd_a")(*PRF*)
	val _ = profTools.bgt (dpfx^"mc_kd_r")(*PRF*)
	val stset_ty = state_type --> bool
	val avar= mk_var("a",stringSyntax.string_ty)
	val ins_tm = inst [alpha|->stset_ty] pred_setSyntax.insert_tm
	val KS_ap = List.foldl (fn (e,ac) => list_mk_comb(ins_tm,[e,ac])(*``^e INSERT ^ac``*)) 
			       (inst [alpha|->stset_ty] pred_setSyntax.empty_tm (*``{}``*)) apl 
	val KS_states = inst [alpha|->state_type] pred_setSyntax.univ_tm (*``UNIV``*)
	val KS_initstates = mk_pabs(state, I1) 
	val pvar = mk_var("p",stset_ty)
	val KS_valids =  list_mk_pabs([state,pvar],mk_comb(pvar,state)) 
	val KS_trans = mk_pabs(mk_pair(state,state'), R1t)
	val _ = profTools.ent (dpfx^"mc_kd_r")(*PRF*)
	val _ = profTools.bgt (dpfx^"mc_kd_d")(*PRF*)
	val kn = if (Option.isSome ksname) then "ctlKS_"^(Option.valOf ksname) else "ctlKS"
	val ks_ty = mk_thy_type {Tyop="kripke_structure", Thy="ctl", Args=[stset_ty,state_type]}
	val ksnm = (new_constant(kn,ks_ty); mk_const(kn,ks_ty))
	val ks_def =  mk_adf kn  (ctlSyntax.mk_cks state_type stset_ty ks_ty KS_states KS_initstates KS_trans KS_ap KS_valids )
			     (*``<| S := ^KS_states; S0:= ^KS_initstates; R := ^KS_trans; P:= ^KS_ap; L:= ^KS_valids |>``*)
	val _ = profTools.ent (dpfx^"mc_kd_d")(*PRF*) 
	val _ = profTools.ent (dpfx^"mc_kd")(*PRF*)
	val _ = profTools.bgt (dpfx^"mc_th")(*PRF*)
	val (totth,Rtb,Rthm,Ithm) = 
	    let val _ = profTools.bgt (dpfx^"mc_th_Rth")(*PRF*)
		val ksR = inst [alpha |-> stset_ty,beta|->state_type] ctlSyntax.ksR_tm
		val ksdotR_tm = mk_comb(ksR,rhs(concl ks_def))
		val ksnmdotR_tm = mk_comb(ksR,lhs(concl ks_def))
		val jf = (fn _ => PBETA_RULE (AP_THM (PURE_REWRITE_RULE [SYM ks_def](*mk totth and Rtb in terms of ks.R*) 
								(PURE_REWRITE_CONV [combinTheory.K_THM,kripke_structure_accfupds] 
										   ksdotR_tm)) (mk_pair(state,state'))))
		val Rthm = mk_lthm (fn _ => (mk_eq(mk_comb(ksnmdotR_tm,mk_pair(state,state')),R1t),jf)) jf			       
		val _ = profTools.ent (dpfx^"mc_th_Rth")(*PRF*)
		val _ = dbgTools.DTB (dpfx^"mc_th Rtb1") Rtb (*DBG*)
		val _ = profTools.bgt (dpfx^"mc_th_Rtb")(*PRF*)
                val Rtb = BddConv (PURE_ONCE_REWRITE_CONV [SYM Rthm]) Rtb
		val _ = profTools.ent (dpfx^"mc_th_Rtb")(*PRF*)
		val _ = dbgTools.DTB (dpfx^"mc_th Rtb2") Rtb (*DBG*)
		val _ = dbgTools.DTH (dpfx^"mc_th totth") totth (*DBG*)
		val _ = dbgTools.DTH (dpfx^"mc_th Rthm") Rthm (*DBG*)
		val _ = profTools.bgt (dpfx^"mc_th_tot")(*PRF*)
		val jf = (fn _ => CONV_RULE (RAND_CONV lzPETA_CONV) (PURE_ONCE_REWRITE_RULE [SYM Rthm] totth))
		val totth =  mk_lthm (fn _ => (mk_comb(total_tm,ksnmdotR_tm),jf)) jf 			     
		val _ = profTools.ent (dpfx^"mc_th_tot")(*PRF*)
		val _ = dbgTools.DTH (dpfx^"mc_th totth3") totth (*DBG*)
		val _ = profTools.bgt (dpfx^"mc_th_Ith")(*PRF*)
		val ksS0 = inst [alpha |-> stset_ty,beta|->state_type] ctlSyntax.ksS0_tm
		val ksdotS0_tm = mk_comb(ksS0,rhs(concl ks_def))
		val ksnmdotS0_tm = mk_comb(ksS0,lhs(concl ks_def))
		val jf = (fn _ => PBETA_RULE (AP_THM (PURE_REWRITE_RULE [SYM ks_def](*used by ctl2muks to abbrev I1 to  ks.I*) 
						(PURE_REWRITE_CONV [combinTheory.K_THM,kripke_structure_accfupds] 
						 ksdotS0_tm)) state))
		val Ithm =  mk_lthm (fn _ => (mk_eq(mk_comb(ksnmdotS0_tm,state),I1),jf)) jf			       
		val _ = profTools.ent (dpfx^"mc_th_Ith")(*PRF*)
                val _ = dbgTools.DTH (dpfx^"mc_th Ithm") Ithm (*DBG*)
	    in (totth,Rtb,Rthm,Ithm) end (* Rthm is required when translating to mu KS (in ctlCheck) to abbrev R1 to ks.R *) 
	val _ = profTools.ent (dpfx^"mc_th")(*PRF*)
	val _ = dbgTools.DEX dpfx "mc" (*DBG*)
    in (apl,ks_def,totth,Binarymap.insert(RTm,".",Rtb),Rthm,Ithm) end

end

end