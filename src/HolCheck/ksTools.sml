structure ksTools =
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
open ksTheory
open holCheckTools
open boolTheory

val dbgkt = holCheckTools.dbgall

fun DMSG m v = if v then let val _ = print "ksTools: " val _ = holCheckTools.DMSG m v in () end else ()

in 

fun mk_bool_var s = mk_var(s,bool)

fun mk_AP state ap = mk_pabs(state,ap)

fun has_primed_vars t = List.exists (fn v => Char.compare(#"'",List.last(String.explode( (with_flag(show_types,false) term_to_string) v)))=EQUAL) (free_vars t)

fun get_APs_aux tm =
if (is_neg tm orelse is_conj tm orelse is_imp tm orelse is_disj tm orelse is_cond tm orelse is_eq tm)
then let val (_,args) = strip_comb tm
	 val res = List.concat (List.map get_APs_aux args)
     in if is_eq tm (* an eq which has no AP's on either side is itself an AP *)
	   andalso List.null res (* either lhs nor rhs contained an AP *) 
	   andalso List.null (List.filter has_primed_vars args) (* neither lhs nor rhs contain a primed var *)
	then [tm] else res end 
else if Term.compare(tm,T)=EQUAL orelse Term.compare(tm,F)=EQUAL then []
else if (Type.compare(type_of tm,bool)=EQUAL) andalso not (has_primed_vars tm) then [tm] 
else [];
    
(* given a term tm of type bool, return the list of all atomic propositions in tm, removing duplicates *)
(* FIXME: should we fail if tm is not of type :bool? *)
(* we do not count any atomic propositions over next state variables since by defn AP's are :state->bool *)
fun get_APs tm = Binaryset.listItems(Binaryset.addList(Binaryset.empty Term.compare,get_APs_aux tm))

(* Convert map from names to terms to names to term_bdds.
   NOTE: the use of termToTermBddFun requires that the term argument not contain any uninterpreted constants.  
   T is a (string * term) list where each pair is (action name, corresponding transition relation)
   vm is term_bdd varmap
   OUT: a map : name of action -> termbdd of corresponding transition relation also add the dot action      
   TODO: fix NOTE issue above *)
fun RmakeTmap T vm Ric =
	let fun makeR (h::t) mp = makeR t (insert(mp,(fst h),
		DerivedBddRules.GenTermToTermBdd (!DerivedBddRules.termToTermBddFun) vm (snd h)))
		|   makeR [] mp = mp
            val mp = mkDict String.compare
	    val U_T = if Ric then list_mk_conj(snd(unzip T)) else list_mk_disj(snd(unzip T))
            val Tmap = makeR T mp	
	in insert(Tmap,".",DerivedBddRules.GenTermToTermBdd (!DerivedBddRules.termToTermBddFun) vm (U_T)) end

(* R is a term_bdd representing a transition relation. return totalised version *)
(* FIXME: do I really need  here? *)
fun totalise tbR I1  vm =
   let val sv = strip_pair(rand (lhs (concl(SPEC_ALL(I1)))))	
       val s = List.map (with_flag(show_types,false) term_to_string) sv	
       val sp =  List.map (fn v => mk_bool_var (v^"'")) s
       val s2sp = List.map (fn(v,v') => (BddVar true vm v,BddVar true vm v')) (ListPair.zip(sv,sp))
       val self = list_mk_conj(List.map (fn v => mk_eq(mk_bool_var (v^"'"),mk_bool_var v)) (List.map term_to_string sv))
       val tbt = BddNot(BddAppex sp (bdd.And,tbR,(BddReplace  s2sp (BddCon true vm)))) (*reachable terminal states*)
       val tbl = t2tb vm self (* property saying all states have self loops *)
       val tbtl = BddOp(bdd.And,tbt,tbl) (* terminal states with self loops *)
  in BddOp(bdd.Or,tbR,tbtl) end  

fun prove_wfKS ks_def =  prove(``wfKS ^(lhs (concl ks_def))``, PURE_ONCE_REWRITE_TAC [wfKS_def] THEN CONJ_TAC THENL [
					     PURE_REWRITE_TAC [ks_def,KS_accfupds,combinTheory.K_DEF] 
					     THEN (CONV_TAC (DEPTH_CONV BETA_CONV)) THEN PURE_REWRITE_TAC [SUBSET_UNIV],
					     PURE_REWRITE_TAC [ks_def,KS_accfupds,combinTheory.K_DEF] 
					     THEN (CONV_TAC (DEPTH_CONV BETA_CONV)) THEN REFL_TAC])

(* T1 is the (nm,term) list derived from the output of RmakeTmap, I is the initial state set *)
fun mk_wfKS I1 T1 RTm state vm Ric apl abs_fun ksname = 
    let val state' = mk_primed_state state
	val apl =  if (Option.isSome apl) then Option.valOf apl
		   else if (Option.isSome abs_fun) then
		       List.map (fn ap => mk_pabs(state,ap)) (strip_pair state) 
			else List.map (fn ap => mk_pabs(state,ap)) (get_APs (mk_conj (list_mk_conj (List.map snd T1),I1)))
	val state_type = type_of state
	val stset_ty = mk_type("fun",[state_type,``:bool``])
	val avar= mk_var("a",``:string``)
	val KS_ap = List.foldl (fn (e,ac) => ``^e INSERT ^ac``) (inst [alpha|->stset_ty] ``{}``) apl (*TODO: string->'prop*) 
	val KS_states = inst [{redex=``:'a``,residue=state_type}] ``UNIV``
	val KS_initstates = mk_pabs(state,I1) 
	val pvar = mk_var("p",stset_ty)
	val KS_valids = if (Option.isSome abs_fun) then 
			    let val htb = Option.valOf abs_fun 
				val ht = getTerm htb 
				val cstate = fst(dest_pair(List.hd (snd (strip_comb ht))))
			    in list_mk_pabs([state,pvar],list_mk_exists(strip_pair cstate,mk_conj(ht,mk_comb(pvar,cstate)))) end 
			else list_mk_pabs([state,pvar],mk_comb(pvar,state)) 
	val Rvar = mk_var("R",mk_type("fun",[mk_prod(state_type,state_type),bool]))	
	val KS_trans = mk_tree (List.map (fn (nm,tm)=>(nm,mk_pabs((mk_pair(state,state')),tm))) T1)
	val kn = if (Option.isSome ksname) then Option.valOf ksname else "muKS"
	val _ = new_constant(kn,``:(^state_type,^stset_ty) KS``)
	val ksnm = mk_const(kn,``:(^state_type,^stset_ty) KS``)
	(* skip M.ap for abstracted M since cearTheory.ABS_KS_def does not define M.ap *)
	(* FIXME: since aks.ap is simply the set of state variables, we could pass it in to ABS_KS_def *)
	val ks_def = if (Option.isSome abs_fun)  
			then hd(Defn.eqns_of(Hol_defn (kn) 
					     `^ksnm = <| S := ^KS_states; S0:= ^KS_initstates; T := ^KS_trans; L:= ^KS_valids |>`))
		      else hd(Defn.eqns_of(Hol_defn (kn) 
				    `^ksnm = <| S := ^KS_states; S0:= ^KS_initstates; T := ^KS_trans; ap:= ^KS_ap; L:= ^KS_valids |>`))
	val ksnm = lhs(concl ks_def)
	val tmrpg = Timer.startRealTimer()(*PRF*)
	val wfKS_ks = prove_wfKS ks_def
	val RTm = if Option.isSome RTm then Option.valOf RTm else RmakeTmap T1 vm Ric
	val _ = DMSG (ST (Time.toString(Timer.checkRealTimer tmrpg))) (dbgkt) val _ = DMSG (ST (" (wfKS proof)\n")) (dbgkt)(*PRF*)
    in (apl,ks_def,wfKS_ks,RTm) end

(* prove that the set of all boolean tuples of size k is finite *)
fun BOOLVEC_UNIV_FINITE_CONV k = 
if k = 0 then FINITE_EMPTY
else if k = 1 then BOOL_UNIV_FINITE
else let val th2 = BOOLVEC_UNIV_FINITE_CONV (k-1)
         val u1 = ``UNIV:bool -> bool``
	 val ty = (hd(snd(dest_type(type_of(snd(dest_comb(concl th2)))))))
         val u2 = inst [alpha |-> ty ] ``UNIV``
         val ucuth =  INST_TYPE [alpha |-> ty] UNIV_CROSS_UNIV
         val fcth = ISPECL [u1,u2] FINITE_CROSS
in ONCE_REWRITE_RULE [ucuth] (MP fcth (LIST_CONJ [BOOL_UNIV_FINITE,th2])) end

(* called by muCheck.mk_gen_thms *)
fun mk_Lth ksname state_type prop_type ks_def =
    let val _ = DMSG (ST ("(make_Lth)\n")) (dbgkt)(*DBG*)
	val ksL = mk_comb(``KS_L:^(ty_antiq(list_mk_fun([type_of ksname,state_type,prop_type],bool)))``,ksname)
    in  PBETA_RULE (REWRITE_CONV [ks_def,KS_accfupds,combinTheory.K_DEF] ksL) end 

(* return Tth and dmdth of mk_gen_dmd_thms *)
fun mk_Tth ks_def ksname msd2 msb2 state' state_type prop_type = 
    let 
	val _ = DMSG (ST ("(make_Tth)\n")) (dbgkt)(*DBG*)
        val ksT = mk_comb(``KS_T:^(ty_antiq(list_mk_fun([type_of ksname,``:string``,mk_prod(state_type,state_type)],bool)))``,ksname)  
    in (PURE_ONCE_REWRITE_RULE [GEN_ALL (hd(tl(CONJUNCTS(SPEC_ALL EQ_CLAUSES))))] 
	(((REWRITE_CONV [ks_def,DB.fetch "ks" "KS_accfupds",combinTheory.K_DEF]) 
	  THENC (DEPTH_CONV BETA_CONV) 
	  THENC (REWRITE_CONV []))				
	 (mk_eq(ksT,snd(dest_comb(snd(dest_comb (hd(find_terms (can (match_term 
		   (inst [alpha|->state_type,beta |-> prop_type] ``KS_T_fupd x``)))  (rhs(concl(ks_def))))))))))),
	(CONV_RULE (STRIP_QUANT_CONV (RHS_CONV holCheckTools.ELIM_TUPLED_QUANT_CONV)) 
	((CONV_RULE ((STRIP_QUANT_CONV (RHS_CONV (GEN_PALPHA_CONV state'))) 
		     THENC SWAP_PFORALL_CONV)) msd2),
	 CONV_RULE (STRIP_QUANT_CONV (RHS_CONV holCheckTools.ELIM_TUPLED_QUANT_CONV)) 
	((CONV_RULE ((STRIP_QUANT_CONV (RHS_CONV (GEN_PALPHA_CONV state'))) 
		     THENC SWAP_PFORALL_CONV)) msb2))) end

fun mk_state I1 (T1:(string * term) list) = 
    let val R1 = list_mk_conj (List.map snd T1) (* whether conj or disj doesn't matter for our purposes here *)
	val vars = (free_vars I1) @ (free_vars R1)
	val (st1',st1) = List.partition (fn v => is_prime v) (Binaryset.listItems(Binaryset.addList(Binaryset.empty Term.compare,vars)))
	val sts = Binaryset.addList(Binaryset.empty Term.compare,st1)
	val st2 = List.foldl (fn (v,l) => if (Binaryset.member(sts,unprime v)) then l else (unprime v)::l) [] st1'
	val st = st1@st2
	val state = list_mk_pair st
    in state end

end

end