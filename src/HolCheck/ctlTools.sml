structure ctlTools =
struct

local 

open Globals HolKernel Parse goalstackLib

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
open ksTools
open holCheckTools

val dbgctlt = holCheckTools.dbgall

fun DMSG m v = if v then let val _ = print "ctlTools: " val _ = holCheckTools.DMSG m v in () end else ()

in 

(* attempt to prove R1 is total by confirming that term-bdd for !s . ?s'. R(s,s') is true. *)
(* this raises an exception if R1 is not total. totalisation is done elsewhere (see totalise and mk_ctlKS below) *)
(* ASSERT: Rtb's term is just R(s,s') *)
fun total_CONV R1 state Rtb = 
    let val _ = DMSG (ST "total_CONV\n") (dbgctlt)(*DBG*)
	val state' = mk_primed_state state
	val (st,st') = (strip_pair##strip_pair) (state,state')
	val tb = BddForall st (BddExists st' Rtb)
	val th1 = BddThmOracle tb
	val th2 = CONV_RULE (RHS_CONV (STRIP_QUANT_CONV holCheckTools.ELIM_TUPLED_QUANT_CONV)) 
	    (holCheckTools.ELIM_TUPLED_QUANT_CONV (mk_pforall(state,mk_pexists(state',R1))))(*mk_comb( rator(getTerm Rtb),
											mk_pair(state,state'))))))*)
	val th3 = PURE_ONCE_REWRITE_RULE [SYM th2] th1 
	val th4 = CONV_RULE (RHS_CONV (GEN_PALPHA_CONV state)) (CONV_RULE (RHS_CONV (QUANT_CONV (GEN_PALPHA_CONV state'))) 
								(ISPEC (mk_pabs(mk_pair(state,state'),R1)) TOTAL_def))
	val th5 = PURE_ONCE_REWRITE_RULE [PBETA_CONV (snd(dest_pexists(snd(dest_pforall(rhs(concl th4))))))] th4
	val th6 = PURE_ONCE_REWRITE_RULE [SYM th5] th3
	val _ = DMSG (ST "total_CONV done\n") (dbgctlt)(*DBG*)
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
fun totalise state state' Rtb vm R1 = 
    let val _ = DMSG (ST "totalise\n") (dbgctlt)(*DBG*)
	val (s,sp) = (strip_pair##strip_pair) (state,state')	
	val self = list_mk_conj(List.map (fn v => mk_eq(mk_bool_var (v^"'"),mk_bool_var v)) (List.map term_to_string s))
	val tbt = BddNot(BddExists sp Rtb) (* terminal states*)
	val tbl = BddConv(PURE_ONCE_REWRITE_CONV[REWRITE_CONV[GEN_ALL(SYM PAIR_EQ)]self])(t2tb vm self)(* all states have self loops*) 
	val tbtl = BddOp(bdd.And,tbt,tbl) (* terminal states with self loops *)
	val _ = with_flag(show_types,true) DMSG (TM  (mk_pexists(state',getTerm Rtb))) (dbgctlt)
	val Rtb2 = BddConv (PURE_ONCE_REWRITE_CONV [SYM (holCheckTools.ELIM_TUPLED_QUANT_CONV (mk_pexists(state',getTerm Rtb)))]) 
			   (BddOp(bdd.Or,Rtb,tbtl))
	val R1t = getTerm Rtb2 (* new totalised transition relation*)
	val totth = PBETA_RULE (CONV_RULE (RAND_CONV (GEN_PALPHA_CONV (mk_pair(state,state'))))(* proof R1t is total*) 
		(CONV_RULE (RAND_CONV (PABS_CONV (RAND_CONV (LAND_CONV (RAND_CONV (GEN_PALPHA_CONV state'))))))
 									       (ISPEC  (mk_pabs(mk_pair(state,state'),R1))  TOTAL_THM)))
	val _ = DMSG (ST "totalise done\n") (dbgctlt)(*DBG*)
    in (R1t,totth,Rtb2) end

(* create ks:('state,'prop) kripke_structure, making sure R is total (totalise if necessary); also return term-bdd of R for model checker*)
fun mk_ctlKS I1 R1 RTm state apl vm ksname = 
    let 
	val _ = DMSG (ST "mk_ctlKS\n") (dbgctlt)(*DBG*)
	val state' = mk_primed_state state
	val Ric = is_conj R1
	val RTm = if Option.isSome RTm then Option.valOf RTm else RmakeTmap [(".",R1)] vm Ric 
	val Rtb = Binarymap.find(RTm,".")
	val totth = total_CONV R1 state Rtb handle ex => TRUTH
	val (R1t,totth,Rtb) = if (Term.compare(concl(totth),T)=EQUAL) then totalise state state' Rtb vm R1 else (R1,totth,Rtb)   
	val apl =  if (Option.isSome apl) then Option.valOf apl
		   else List.map (fn ap => mk_pabs(state,ap)) (get_APs (mk_conj (R1,I1)))
	val state_type = type_of state
	val stset_ty = mk_type("fun",[state_type,``:bool``])
	val avar= mk_var("a",``:string``)
	val KS_ap = List.foldl (fn (e,ac) => ``^e INSERT ^ac``) (inst [alpha|->stset_ty] ``{}``) apl (*TODO: string->'prop*) 
	val KS_states = inst [{redex=``:'a``,residue=state_type}] ``UNIV``
	val KS_initstates = mk_pabs(state, I1) 
	val pvar = mk_var("p",stset_ty)
	val KS_valids =  list_mk_pabs([state,pvar],mk_comb(pvar,state)) 
	val KS_trans = mk_pabs(mk_pair(state,state'), R1t)
	val kn = if (Option.isSome ksname) then Option.valOf ksname else "ctlKS"
	val _ = new_constant(kn,``:(^state_type,^stset_ty) kripke_structure``)
	val ksnm = mk_const(kn,``:(^state_type,^stset_ty) kripke_structure``)
	val ks_def =  hd(Defn.eqns_of(Hol_defn (kn) 
				      `^ksnm = <| S := ^KS_states; S0:= ^KS_initstates; R := ^KS_trans; P:= ^KS_ap; L:= ^KS_valids |>`))
	val (totth,Rtb,Rthm) = let val Rthm = PBETA_RULE (AP_THM (PURE_REWRITE_RULE [SYM ks_def](*mk totth and Rtb in terms of ks.R*) 
					(PURE_REWRITE_CONV [combinTheory.K_THM,kripke_structure_accfupds] 
				       ``(^(rhs(concl ks_def))).R``)) (mk_pair(state,state')))
			      val Rtb = BddConv (PURE_ONCE_REWRITE_CONV [SYM Rthm]) Rtb
			      val totth =  CONV_RULE (RAND_CONV PETA_CONV) (PURE_ONCE_REWRITE_RULE [SYM Rthm] totth)
			  in (totth,Rtb,Rthm) end (* Rthm is required when translating to mu KS (in ctlCheck) to abbrev R1 to ks.R *) 
	val _ = DMSG (ST "mk_ctlKS done\n") (dbgctlt)(*DBG*)
    in (apl,ks_def,totth,Binarymap.insert(RTm,".",Rtb),Rthm) end

end

end