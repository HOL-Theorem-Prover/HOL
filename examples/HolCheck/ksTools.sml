structure ksTools =
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
open ksTheory
open commonTools
open boolTheory
open lazyTools
open lzPairRules

val dpfx = "kt_";

in

fun mk_bool_var s = mk_var(s,bool)

fun mk_AP state ap = mk_pabs(state,ap)

(* take a state and return it with all vars primed, preserving nested tuple structure if any *)
fun mk_primed_state s =
if is_pair s then list_mk_pair(List.map mk_primed_state (spine_pair s))
else mk_var((term_to_string2 s)^"'",type_of s)

fun has_primed_vars t = List.exists (fn v => Char.compare(#"'",
							  List.last(String.explode ((with_flag(show_types,false)
											       term_to_string) v)))=EQUAL) (free_vars t)

val ks_p_ty = ``:'prop``
val ks_s_ty = ``:'state``
val ks_as_ty = ``:'astate``

fun get_types ksname = let val (_,l) = dest_type (type_of ksname) in (hd l,last l) end

val dotacn = ``"."``

val _ = set_trace "notify type variable guesses" 0;
val ksS_tm = ``ks$KS_S``
val ksS0_tm = ``ks$KS_S0``
val ksT_tm = ``ks$KS_T``
val ksap_tm = ``ks$KS_ap``
val ksL_tm = ``ks$KS_L``

val ksSu_tm = ``ks$KS_S_fupd``
val ksS0u_tm = ``ks$KS_S0_fupd``
val ksTu_tm = ``ks$KS_T_fupd``
val ksapu_tm = ``ks$KS_ap_fupd``
val ksLu_tm = ``ks$KS_L_fupd``
val _ = set_trace "notify type variable guesses" 1;

val getS = (rand o rand o rator)
val getS0 = rand o rand o rator o rand
val getT = rand o rand o rator o rand o rand
val getap = (rand o rand o rator o rand o rand o rand)
fun getL tm = (rand o rand o rator o rand o rand o rand o rand) tm
    handle ex => (rand o rand o rator o rand o rand o rand) tm (* in case there is no ap *)

(* FIXME: this assumes alpha stands for st_ty etc. This could change if HOL records change *)
fun mk_ks s_ty p_ty ks_ty S S0 T ap L =
let val _ =  dbgTools.DEN dpfx "mk" (*DBG*)
    val ksSu = inst [alpha |-> s_ty,beta |-> p_ty] ksSu_tm
    val ksS0u = inst [alpha |-> s_ty,beta |-> p_ty] ksS0u_tm
    val ksTu = inst [alpha |-> s_ty,beta |-> p_ty] ksTu_tm
    val ksapu = inst [alpha |-> p_ty,beta |-> s_ty] ksapu_tm (* FIXME: why are alpha and beta inverted here?*)
    val ksLu = inst [alpha |-> s_ty,beta |-> p_ty] ksLu_tm
    val arb_ks = inst [alpha |-> ks_ty] boolSyntax.arb
    val _ = dbgTools.DTY (dpfx^"mk_arb_ks") (type_of arb_ks) (*DBG*)
    val upds = if isSome ap then [(ksSu,S),(ksS0u,S0),(ksTu,T),(ksapu,valOf ap),(ksLu,L)]
	       else [(ksSu,S),(ksS0u,S0),(ksTu,T),(ksLu,L)]
    val res = List.foldr (fn ((u,v),ks) =>
			     let val _ = dbgTools.DTY (dpfx^"mk_u_ty") (type_of u) (*DBG*)
				 val _ = dbgTools.DTY (dpfx^"mk_v_ty") (type_of v) (*DBG*)
				 val _ = dbgTools.DTY (dpfx^"mk_ks_ty") (type_of ks) (*DBG*)
			     in mk_comb(mk_comb (u,mk_comb(inst [alpha |-> type_of v, beta |->type_of v]
									   combinSyntax.K_tm,v)),ks) end)
			 arb_ks upds
    val _ =  dbgTools.DEX dpfx "mk" (*DBG*)
in res end

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

(* R is a term_bdd representing a transition relation. return totalised version *)
fun totalise tbR S0 vm =
   let val sv = strip_pair(rand (lhs (concl(SPEC_ALL(S0)))))
       val s = List.map (with_flag(show_types,false) term_to_string) sv
       val sp =  List.map (fn v => mk_bool_var (v^"'")) s
       val s2sp = List.map (fn(v,v') => (BddVar true vm v,BddVar true vm v')) (ListPair.zip(sv,sp))
       val self = list_mk_conj(List.map (fn v => mk_eq(mk_bool_var (v^"'"),mk_bool_var v)) (List.map term_to_string sv))
       val tbt = BddNot(BddAppex sp (bdd.And,tbR,(BddReplace  s2sp (BddCon true vm)))) (*reachable terminal states*)
       val tbl = t2tb vm self (* property saying all states have self loops *)
       val tbtl = BddOp(bdd.And,tbt,tbl) (* terminal states with self loops *)
  in BddOp(bdd.Or,tbR,tbtl) end

(* Convert map from names to terms to names to term_bdds.
   NOTE: the use of termToTermBddFun requires that the term argument not contain any uninterpreted constants.
   T is a (string * term) list where each pair is (action name, corresponding transition relation)
   vm is term_bdd varmap
   OUT: a map : name of action -> termbdd of corresponding transition relation also add the dot action
   TODO: fix NOTE issue above *)
fun RmakeTmap KS_trans_def TS vm Ric state state' avar =
    let val _ =  dbgTools.DEN dpfx "rt" (*DBG*)
	val _ = profTools.bgt (dpfx^"rt")(*PRF*)
	fun makeR (h::t) mp = makeR t (insert(mp,(fst h), t2tb vm (snd h)))
		|   makeR [] mp = mp
        val mp = mkDict String.compare
	(*val U_T = if Ric then list_mk_conj(snd(unzip T)) else list_mk_disj(snd(unzip T))*)
	val Tmap = makeR TS mp (*,".",DerivedBddRules.GenTermToTermBdd (!DerivedBddRules.termToTermBddFun) vm (U_T))*)
	val _ = profTools.bgt (dpfx^"rt_fc")(*PRF*)
	val kstdnm = fst(strip_comb(lhs(concl (SPEC_ALL KS_trans_def))))
	val Tmap' = Binarymap.map (fn (nm,tb) =>
		let val holnm = fromMLstring nm
		    val jf = (fn _ => SYM (CONV_RULE (RHS_CONV find_CONV) (SPEC_ALL (SPEC holnm KS_trans_def))))
		    val th = mk_lthm
				 (fn _ => (mk_eq(getTerm tb,list_mk_comb(kstdnm,[holnm,mk_pair(state,state')])),
					   jf)) jf
		    val _ = dbgTools.DTH (dpfx^"rt_"^nm) th (*DBG*)
		in BddEqMp th tb end) Tmap
	val _ = profTools.ent (dpfx^"rt_fc")(*PRF*)
	val _ = Binarymap.app (fn (nm,tb) => dbgTools.DTB (dpfx^"rt_"^nm) tb) Tmap'(*DBG*)
	val _ = profTools.ent (dpfx^"rt")(*PRF*)
	val _ = dbgTools.DEX dpfx "rt" (*DBG*)
    in Tmap' end

fun prove_wfKS ks_def =
    let val jf = (fn _ => prove(``wfKS ^(lhs (concl ks_def))``,
			PURE_ONCE_REWRITE_TAC [wfKS_def] THEN CONJ_TAC THENL
			[PURE_REWRITE_TAC [ks_def,KS_accfupds,combinTheory.K_DEF]
					  THEN (CONV_TAC (DEPTH_CONV BETA_CONV)) THEN PURE_REWRITE_TAC [SUBSET_UNIV],
			 PURE_REWRITE_TAC [ks_def,KS_accfupds,combinTheory.K_DEF]
					  THEN (CONV_TAC (DEPTH_CONV BETA_CONV)) THEN REFL_TAC]))
    in mk_lthm (fn _ => (``wfKS ^(lhs (concl ks_def))``,jf)) jf end


fun mk_model_names ksname state_type prop_type =
    let val _ = dbgTools.DEN dpfx "mmn" (*DBG*)
	val kn = if (Option.isSome ksname) then "muKS_"^(Option.valOf ksname) else "muKS"
	val Tn = "T_"^kn
	val _ = new_constant(Tn,stringLib.string_ty --> (mk_prod(state_type,state_type)) --> bool)
	val Tnm = mk_const(Tn,stringLib.string_ty --> (mk_prod(state_type,state_type)) --> bool)
	val S0n = "S0_"^kn
	val _ = new_constant(S0n,state_type --> bool)
	val S0nm = mk_const(S0n, state_type --> bool)
	val _ = dbgTools.DEX dpfx "mmn" (*DBG*)
in (kn,Tnm,Tn,S0nm,S0n) end


(* TS is the (nm,term) list derived from the output of RmakeTmap, S0 is the initial state set *)
fun mk_formal_KS S0 TS state Ric apl abs_fun ksname =
    let val _ = dbgTools.DEN dpfx "mw" (*DBG*)
	val _ = profTools.bgt (dpfx^"mw")(*PRF*)
	val _ = profTools.bgt (dpfx^"mw_init")(*PRF*)
	val state' = mk_primed_state state
	val _ = dbgTools.DTM (dpfx^"mw_state'") state'(*DBG*)
	val (cstate,cstate',cstate_type,cpvar,ht,htc,cT) = (*compute concrete stuff in case this is building abstract ks*)
	    if isSome abs_fun
	    then let val (aftb,cT,cstate,cstate') = valOf abs_fun
		     val _ = dbgTools.DTM (dpfx^"mw_cstate") cstate(*DBG*)
		     val ht = getTerm aftb
		     val _ = dbgTools.DTM (dpfx^"mw_ht") ht(*DBG*)
		     val cstate_type = type_of cstate
		     val cpvar = mk_var("p",cstate_type --> bool)
		     val htc = rator ht (* name of abs fun *)
		 in (SOME cstate,SOME cstate',SOME cstate_type,SOME cpvar,SOME ht,SOME htc,SOME cT) end
	    else (NONE,NONE,NONE,NONE,NONE,NONE,NONE)
	val apl =  if (Option.isSome apl) then Option.valOf apl
		   else if (Option.isSome abs_fun)
		   then List.map (fn ap => mk_pabs(valOf cstate,ap)) (strip_pair (valOf cstate))
		   else List.map (fn ap => mk_pabs(state,ap)) (strip_pair state)
	              (*(get_APs(mk_conj(list_mk_conj(List.map snd TS),S0)))*)
	val _ = List.app (dbgTools.DTM (dpfx^"mw_apl")) apl(*DBG*)
	val state_type = type_of state
	val prop_type = if isSome abs_fun then (valOf cstate_type) --> bool else state_type --> bool
	val (kn,Tnm,Tn,S0nm,S0n) = mk_model_names ksname state_type prop_type
	val ks_ty = mk_thy_type {Tyop="KS", Thy="ks", Args=[prop_type,state_type]}
	val avar= mk_var("t",stringLib.string_ty)
	val _ = dbgTools.DTM (dpfx^"mw_pvar") avar(*DBG*)
	val _ = profTools.ent (dpfx^"mw_init")(*PRF*)
	val _ = profTools.bgt (dpfx^"mw_ap")(*PRF*)
	val KS_ap = List.foldl (fn (e,ac) => list_mk_comb (inst [alpha|->prop_type] pred_setSyntax.insert_tm,[e,ac]))
			       (inst [alpha|->prop_type] pred_setSyntax.empty_tm) apl
	val _ = profTools.ent (dpfx^"mw_ap")(*PRF*)
	val KS_states = inst [alpha|->state_type] pred_setSyntax.univ_tm
	val KS_initstates = S0
	val _ = profTools.bgt (dpfx^"mw_L")(*PRF*)
	val pvar = mk_var("p",prop_type)
	val _ = dbgTools.DTM (dpfx^"mw_pvar") pvar(*DBG*)
	val KS_valids = if (isSome abs_fun)
			then let val (cv,cs,ht) = (valOf cpvar,valOf cstate,valOf ht)
			     in list_mk_pabs([state,cv],list_mk_exists(strip_pair cs,mk_conj(ht,mk_comb(cv,cs)))) end
			else list_mk_pabs([state,pvar],mk_comb(pvar,state))
	val _ = profTools.ent (dpfx^"mw_L")(*PRF*)
	val _ = dbgTools.DTM (dpfx^"mw_KS_valids") KS_valids(*DBG*)
	val _ = profTools.bgt (dpfx^"mw_df_i")(*PRF*)
	val KS_init_def = hd(Defn.eqns_of(Hol_defn (S0n) `^(mk_eq(mk_comb(S0nm,state),KS_initstates))`))
	val _ = profTools.ent (dpfx^"mw_df_i")(*PRF*)
	val _ = dbgTools.DTH (dpfx^"mw_KS_init_def") KS_init_def (*DBG*)
	val _ = profTools.bgt (dpfx^"mw_T")(*PRF*)
	val Rvar = mk_var("R",(mk_prod(state_type,state_type)) --> bool)
	val TS = (".",if Ric then list_mk_conj (snd(unzip TS))
		      else  list_mk_disj (snd(unzip TS)))::TS (*add wildcard action *)
	val KS_trans = if isSome abs_fun
		       then let val (cs,cs') = (valOf cstate,valOf cstate')
			    in list_mk_pabs([avar,mk_pair(state,state')],
					    list_mk_pexists([cs,cs'],
							    list_mk_conj [list_mk_comb(valOf cT,[avar,mk_pair(cs,cs')]),
									  mk_comb(valOf htc,mk_pair(cs,state)),
									  mk_comb(valOf htc,mk_pair(cs',state'))])) end
		       else mk_tree (SOME (mk_pair(state,state'))) TS
	val _ = profTools.ent (dpfx^"mw_T")(*PRF*)
	val _ = dbgTools.DTM (dpfx^"mw_KS_trans") KS_trans(*DBG*)
	val _ = profTools.bgt (dpfx^"mw_df_t")(*PRF*)
	val KS_trans_def =hd(Defn.eqns_of(Hol_defn(Tn)
				`^(mk_eq(list_mk_comb(Tnm,[avar,mk_pair(state,state')]),pbody(body KS_trans)))`))
	val _ = profTools.ent (dpfx^"mw_df_t")(*PRF*)
	val _ = dbgTools.DTH (dpfx^"mw_KS_trans_def") KS_trans_def (*DBG*)
	(* skip M.ap for abstracted M since cearTheory.ABS_KS_def does not define M.ap *)
	(* FIXME: since aks.ap is simply the set of abstract state variables, we could pass it in to ABS_KS_def *)
	val _ = profTools.bgt (dpfx^"mw_df_k")(*PRF*)
	val ks_def = if (isSome abs_fun)
		     then mk_adf kn (mk_ks state_type prop_type ks_ty KS_states (mk_pabs(state,KS_initstates))
					   KS_trans NONE KS_valids)
		     else mk_adf kn (mk_ks state_type prop_type ks_ty KS_states
					   (rator (lhs (snd(strip_forall(concl KS_init_def)))))
					   (rator (rator (lhs (snd (strip_forall(concl KS_trans_def))))))
					   (SOME KS_ap) KS_valids)
	val _ = profTools.ent (dpfx^"mw_df_k")(*PRF*)
	val ksnm = lhs(concl ks_def)
	val _ = profTools.bgt (dpfx^"mw_pw")(*PRF*)
	val wfKS_ks = prove_wfKS ks_def
	val _ = profTools.ent (dpfx^"mw_pw")(*PRF*)
	val ITdf = if isSome abs_fun then NONE else SOME (SPEC_ALL KS_init_def,SPEC_ALL KS_trans_def)
	val _ = profTools.ent (dpfx^"mw")(*PRF*)
        val _ = dbgTools.DEX dpfx "mw" (*DBG*)
    in (apl,ks_def,wfKS_ks,ITdf,KS_trans_def,state',avar) end

fun mk_wfKS S0 TS RTm state vm Ric apl abs_fun ksname =
    let
	val (apl,ks_def,wfKS_ks,ITdf,KS_trans_def,state',avar) = mk_formal_KS S0 TS state Ric apl abs_fun ksname
	val RTm = if Option.isSome RTm then Option.valOf RTm else RmakeTmap KS_trans_def TS vm Ric state state' avar
    in  (apl,ks_def,wfKS_ks,RTm,ITdf) end

(* construct state var tuple from I and T*)
fun mk_state S0 (TS:(string * term) list) =
    let val R1 = list_mk_conj (List.map snd TS) (* whether conj or disj doesn't matter for our purposes here *)
	val vars = (free_vars S0) @ (free_vars R1)
	val (st1',st1) = List.partition (fn v => is_prime v)
					(Binaryset.listItems(Binaryset.addList(Binaryset.empty Term.compare,vars)))
	val sts = Binaryset.addList(Binaryset.empty Term.compare,st1)
	val st2 = List.foldl (fn (v,l) => if (Binaryset.member(sts,unprime v)) then l else (unprime v)::l) [] st1'
	val st = st1@st2
	val state = list_mk_pair st
    in state end

(* this does not require or create BDD's. Mainly for experimenting with ideas on combining mc and tp *)
fun auto_mk_formal_ks S0 TS Ric apl ksname =
    let val state = mk_state S0 TS
    in mk_formal_KS S0 TS state Ric apl NONE ksname end

val getT = rand o rand o rator o rand o rand

val getS0 = rand o rand o rator o rand

fun getL tm = (rand o rand o rator o rand o rand o rand o rand) tm
    handle ex => (rand o rand o rator o rand o rand o rand) tm (* in case there is no ap *)

(* S0_CONV conv will apply conv to the S0 part of the ks *)
val S0_CONV = (RAND_CONV o RATOR_CONV o RAND_CONV o RAND_CONV)

(* T_CONV conv will apply conv to the T part of the ks *)
val T_CONV = (RAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV o RAND_CONV)

(* prove that the set of all boolean tuples of size k is finite *)
fun BOOLVEC_UNIV_FINITE_CONV k =
if k = 0 then FINITE_EMPTY
else if k = 1 then BOOL_UNIV_FINITE
else let val th2 = BOOLVEC_UNIV_FINITE_CONV (k-1)
         val u1 = inst [alpha |-> bool ] pred_setSyntax.univ_tm
	 val ty = (hd(snd(dest_type(type_of(snd(dest_comb(concl th2)))))))
         val u2 = inst [alpha |-> ty ] pred_setSyntax.univ_tm
         val ucuth =  INST_TYPE [alpha |-> ty] UNIV_CROSS_UNIV
         val fcth = ISPECL [u1,u2] FINITE_CROSS
in ONCE_REWRITE_RULE [ucuth] (MP fcth (LIST_CONJ [BOOL_UNIV_FINITE,th2])) end

fun empty_ks p_ty s_ty =
    let val ks_ty = mk_thy_type {Tyop="KS", Thy="ks", Args=[p_ty,s_ty]}
    in inst [alpha |-> ks_ty] boolSyntax.arb end

fun set_L ks Lv =
    let val (p_ty,s_ty) = get_types ks
	val ksLu = inst [alpha |-> s_ty,beta |-> p_ty] ksLu_tm
    in mk_comb(mk_comb (ksLu,mk_comb(inst [alpha |-> type_of Lv, beta |->type_of Lv]
					  combinSyntax.K_tm,Lv)),ks) end

fun set_ap ks apv =
    let  val (p_ty,s_ty) = get_types ks
	 val ksapu = inst [alpha |-> p_ty,beta |-> s_ty] ksapu_tm
    in mk_comb(mk_comb (ksapu,mk_comb(inst [alpha |-> type_of apv, beta |->type_of apv]
					   combinSyntax.K_tm,apv)),ks) end

fun mk_ks_dot_ap ks =
    let val (p_ty,s_ty) = get_types ks
	val ksap = inst [alpha|->p_ty,beta|->s_ty] ksap_tm
    in  mk_comb(ksap,ks) end

fun mk_ks_dot_L ks =
    let val (p_ty,s_ty) = get_types ks
	val ksL = inst [alpha|->p_ty,beta|->s_ty] ksL_tm
    in  mk_comb(ksL,ks) end

fun mk_ks_dot_S0 ks =
    let val (p_ty,s_ty) = get_types ks
	val ksS0 = inst [alpha|->p_ty,beta|->s_ty] ksS0_tm
    in  mk_comb(ksS0,ks) end

fun mk_ks_dot_S ks =
    let val (p_ty,s_ty) = get_types ks
	val ksS = inst [alpha|->p_ty,beta|->s_ty] ksS_tm
    in  mk_comb(ksS,ks) end

fun mk_ks_dot_T ks =
    let val (p_ty,s_ty) = get_types ks
	val ksT = inst [alpha|->p_ty,beta|->s_ty] ksT_tm
    in  mk_comb(ksT,ks) end

(* called by muCheck.mk_gen_thms *)
fun mk_Lth ks_def =
    let val _ = dbgTools.DEN dpfx "ml" (*DBG*)
	(*val L = ``KS_L:^(ty_antiq(list_mk_fun([type_of ksname,state_type,prop_type],bool)))``
	val ksL = mk_comb(L,ksname)*)
	val ksname = lhs(concl ks_def)
	val (p_ty,s_ty) = get_types ksname
	val L = inst [alpha|->p_ty,beta|->s_ty] ksL_tm
	val ksL = mk_comb(L,ksname)
	(*val _ = DMSG (TM ksL) dbgkt (*DBG*)
	val _ = DMSG (TH (REWRITE_CONV [ks_def,KS_accfupds,combinTheory.K_DEF] ksL)) dbgkt (*DBG*)*)
	val kt = type_of ksL
	(* FIXME: get rid of the quotations *)
	val tm = mk_eq(ksL,list_mk_comb(``(\(x:(^(ty_antiq kt))) (y:(^(ty_antiq kt))). x)``,
				       [getL (rhs(concl ks_def)),mk_comb(L,``ARB:(^(ty_antiq(type_of ksname)))``)]))
	(*val _ = with_flag (show_types,true) (DMSG (TM tm)) dbgkt val _ = DMSG (ST "own term") dbgkt*)
	(*val res =  (REWRITE_CONV [ks_def,KS_accfupds,combinTheory.K_DEF] ksL)
	val _ = with_flag (show_types,true) (DMSG (TM (concl res))) dbgkt val _ = DMSG (ST "rw term") dbgkt
	val _ = if (Term.compare(concl res,tm)=EQUAL) then () else Raise Match*)
	val jf = (fn _ => REWRITE_CONV [ks_def,KS_accfupds,combinTheory.K_DEF] ksL)
	val res = BETA_RULE (mk_lthm (fn _ => (tm,jf)) jf)
	val _ = dbgTools.DEX dpfx "ml" (*DBG*)
    in res end

val ksTupx_tm = ``KS_T_fupd x``

(* return Tth and dmdth of mk_gen_dmd_thms *)
fun mk_Tth ks_def ksname msd2 msb2 state' state_type prop_type =
    let
	val _ = dbgTools.DEN dpfx "mt" (*DBG*)
	val ksT = mk_ks_dot_T ksname
	val jf = (fn _ => PURE_ONCE_REWRITE_RULE
		       [GEN_ALL (hd(tl(CONJUNCTS(SPEC_ALL EQ_CLAUSES))))]
		       (((REWRITE_CONV [ks_def,DB.fetch "ks" "KS_accfupds",combinTheory.K_DEF])
			     THENC (DEPTH_CONV BETA_CONV)
			     THENC (REWRITE_CONV []))
			    (mk_eq(ksT,rand((rand((hd(find_terms (can (match_term (inst [alpha|->state_type,beta |-> prop_type]
										ksTupx_tm)))  (rhs(concl(ks_def))))))))))))
	val Tth = mk_lthm (fn _ => (mk_eq(ksT,getT (rhs(concl ks_def))),jf)) jf
	val (dmdth,boxth) = (CONV_RULE (STRIP_QUANT_CONV (RHS_CONV commonTools.lzELIM_TUPLED_QUANT_CONV))
				       ((CONV_RULE ((STRIP_QUANT_CONV (RHS_CONV (lzGEN_PALPHA_CONV state')))
							THENC lzSWAP_PFORALL_CONV)) msd2),
		             CONV_RULE (STRIP_QUANT_CONV (RHS_CONV commonTools.lzELIM_TUPLED_QUANT_CONV))
				       ((CONV_RULE ((STRIP_QUANT_CONV (RHS_CONV (lzGEN_PALPHA_CONV state')))
							THENC lzSWAP_PFORALL_CONV)) msb2))
    val _ = dbgTools.DTH (dpfx^"mt_Tth") Tth(*DBG*)
    val _ = dbgTools.DTH (dpfx^"mt_msd2") msd2(*DBG*)
    val _ = dbgTools.DTH (dpfx^"mt_dmdth") dmdth(*DBG*)
    val _ = dbgTools.DTH (dpfx^"mt_msb2") msb2(*DBG*)
    val _ = dbgTools.DTH (dpfx^"mt_boxth") boxth(*DBG*)
    val _ = dbgTools.DEX dpfx "mt" (*DBG*)
    in (Tth,(dmdth,boxth)) end

(*given t of the form \s. P s = \s. Q s, prove t=T or die, where P s and Q s must be completely propositional *)
fun AP_EQ vm t =
    let val _ = dbgTools.DEN dpfx "ae" (*DBG*)
	val (l,r) = dest_eq t
	val ((ls,lb),(rs,rb)) = (dest_pabs ## dest_pabs)(l,r)
	val eq = mk_eq(lb,rb)
	val tb = t2tb vm eq
	val th1 = PABS ls (BddThmOracle tb)
	    handle ex => (dbgTools.DBD (dpfx^"ae_toe_bdd") (getBdd tb);(*DBG*)
			  dbgTools.DTM (dpfx^"ae_toe_tm") t;(*DBG*)
			  dbgTools.DBD (dpfx^"ae_toe_neg_bdd") (getBdd (BddNot tb));(*DBG*)
			  dbgTools.DEX dpfx "ae" (*DBG*);
			  failwith "AP_EQ failure")
	val eqth = GEN_ALL (SYM (List.nth(CONJUNCTS (SPEC_ALL EQ_CLAUSES),1)))
	val th2 = PURE_ONCE_REWRITE_RULE [ISPEC (concl th1) eqth] th1
	val _ = dbgTools.DEX dpfx "ae" (*DBG*)
    in th2 end

end
end
