(*load "bossLib"; 
load "pairSyntax";
load "boolSyntax";
load "muLib";
load "CTL" *)

structure cearTools =
struct

local 

open Globals HolKernel Parse goalstackLib;

open boolSyntax;
open pairSyntax;
open pairTools;
open PairRules;
open bossLib;
open Tactical;
open Tactic;
open Drule;
open Rewrite;
open cearTheory;
open ksTheory;
open setLemmasTheory;
open pred_setTheory;
open boolTheory;
open Conv;
open pairTheory;
open pred_setTheory;
open pred_setLib;
open stringLib;
open listTheory;
open simpLib;
open pairLib;
open PrimitiveBddRules;
open DerivedBddRules;
open Binarymap;
open muSyntaxTheory
open muSyntax
open muTheory;
open muTools;
open ksTheory;
open HolSatLib;
open defCNF;
open muCheck;
open sumSyntax
open numSyntax;
open bddTools
open envTheory
open ksTools
open holCheckTools

val _ = numLib.prefer_num();

val dbgceart = holCheckTools.dbgall

fun DMSG m v = if v then let val _ = print "cearTools: " val _ = holCheckTools.DMSG m v in () end else ()

in

(* prove that ABS_KS ks h = aks *)
(* where hd is the definition h(s,sh) = ... (required only to get our hands on the constant h) *)
fun mk_abs_eq_thm state state' astate astate' n hd_def ks_def aks_def goal =
    prove(goal,
	  REWRITE_TAC [GSYM hd_def]
	  THEN REWRITE_TAC [ks_def,aks_def,ABS_KS_def,KS_component_equality,KS_accfupds,combinTheory.K_DEF]
	  THEN BETA_TAC
	  THEN REPEAT CONJ_TAC THENL 
	  [
	   REWRITE_TAC [EXTENSION]
           THEN CONV_TAC (GEN_PALPHA_CONV astate)
	   THEN PairRules.PGEN_TAC
	   THEN CONV_TAC (RHS_CONV pred_setLib.SET_SPEC_CONV)
	   THEN CONV_TAC (RHS_CONV (GEN_PALPHA_CONV state))
	   THEN CONV_TAC (RHS_CONV ELIM_TUPLED_QUANT_CONV)
	   THEN SIMP_TAC std_ss [IN_DEF] THEN PBETA_TAC, (* S0 *)
	   SIMP_TAC (pure_ss++boolSimps.LET_ss) []
	   THEN CONV_TAC (RHS_CONV (ABS_CONV (GEN_PALPHA_CONV (mk_pair(astate,astate')))))
	   THEN CONV_TAC (RHS_CONV (PABS_CONV (PABS_CONV(QUANT_CONV(GEN_PALPHA_CONV state')))))
	   THEN CONV_TAC (RHS_CONV (ABS_CONV (PABS_CONV(QUANT_CONV(ELIM_TUPLED_QUANT_CONV)))))
	   THEN CONV_TAC (RHS_CONV (ABS_CONV (PABS_CONV(GEN_PALPHA_CONV state))))
	   THEN CONV_TAC (RHS_CONV (ABS_CONV (PABS_CONV ELIM_TUPLED_QUANT_CONV)))
	   THEN PBETA_TAC
	   THEN ONCE_REWRITE_TAC [FUN_EQ_THM] 
	   THEN GEN_TAC
	   THEN BETA_TAC
	   THEN ONCE_REWRITE_TAC [FUN_EQ_THM] 
	   THEN CONV_TAC (GEN_PALPHA_CONV (mk_pair(astate,astate')))
	   THEN PairRules.PGEN_TAC
	   THEN PBETA_TAC
	   THEN metisLib.METIS_TAC [], (* T *) (*FIXME: this can get very slow because we are working with the expanded T here *)
           REWRITE_TAC [SET_SPEC,BIGUNION]
	   THEN ONCE_REWRITE_TAC [FUN_EQ_THM]
	   THEN CONV_TAC (GEN_PALPHA_CONV astate)
	   THEN PairRules.PGEN_TAC 	  
	   THEN CONV_TAC (FORK_CONV(PBETA_CONV,PBETA_CONV))
	   THEN ONCE_REWRITE_TAC [FUN_EQ_THM]
	   THEN GEN_TAC
	   THEN CONV_TAC (FORK_CONV(PBETA_CONV,ONCE_REWRITE_CONV [GSYM SPECIFICATION]))
	   THEN CONV_TAC (RHS_CONV (SIMP_CONV std_ss [SET_SPEC]))
	   THEN CONV_TAC (RHS_CONV (QUANT_CONV (LAND_CONV(GEN_PALPHA_CONV state))))
	   THEN PBETA_TAC
	   THEN CONV_TAC (RHS_CONV (QUANT_CONV (LAND_CONV ELIM_TUPLED_QUANT_CONV)))
	   THEN NTAC n (CONV_TAC (RHS_CONV (STRIP_QUANT_CONV LEFT_AND_EXISTS_CONV)))
	   THEN RW_TAC std_ss [IN_DEF]
	   THEN REFL_TAC
	  ])

(* given a list of SCC terms SCC R (seed 0 j) (pf 0 s), return thms for SCC_FOLD_BASE and STEP *)
fun mk_scc_fold_thms sccl_ state = 
    let val _ = DMSG (ST "mk_scc_fold_thms\n") (dbgceart)
	val sccl = List.map (fn (n,t) => let val (scc,ll) = strip_comb t
			                     val osd = List.nth(ll,1)
					     val sd_tm = list_mk_comb(``seed``,[n, mk_var("j",``:num``)])
                                             val sd = subst [(find_term (can (match_term ``seed x 0``)) osd) |-> sd_tm] osd
                                      in list_mk_comb(scc,[List.hd ll,sd, List.last ll]) end) 
	    (ListPair.zip(List.tabulate(List.length sccl_,fn n => numSyntax.mk_numeral(Arbnum.fromInt(n))),sccl_))
	val syml = (list_mk_conj sccl)
	val l0 = list_mk_conj (List.map (subst [``j:num`` |-> ``0:num``]) sccl)
	val l1 = list_mk_conj (List.map (subst [``j:num`` |-> ``1:num``]) sccl)
	val symsuc = list_mk_conj (List.map (subst  [``j:num`` |-> ``SUC (n:num)``] ) sccl)	    
    in (prove(``!g sh. ((^l0) /\ g (0:num) sh) \/ ((^l1) /\ g (1:num) sh) 
	      = ((^state) IN {(^state) | ?j. j<=1 /\ ((^syml) /\ (g j sh))})``,
	      REPEAT STRIP_TAC THEN EQ_TAC THENL 
	      [
	       STRIP_TAC 
	       THEN (CONV_TAC pred_setLib.SET_SPEC_CONV) 
	       THEN SIMP_TAC std_ss [] THENL 
               [
		Q.EXISTS_TAC `0`
		THEN FULL_SIMP_TAC arith_ss [],
		Q.EXISTS_TAC `1`
		THEN FULL_SIMP_TAC arith_ss []
	       ],	       
	       (CONV_TAC (LAND_CONV pred_setLib.SET_SPEC_CONV)) 
	       THEN REPEAT STRIP_TAC
	       THEN FULL_SIMP_TAC arith_ss [DECIDE ``j<=1 = (j=0) \/ (j=1)``] THENL 
	       [
		DISJ1_TAC THEN ASSUM_LIST metisLib.METIS_TAC,
		DISJ2_TAC THEN ASSUM_LIST metisLib.METIS_TAC
	       ]
	      ]),
	prove(``!g sh n. ((^state) IN {(^state) | ?(j:num). j<=n /\  ((^syml)/\  (g j sh))}) \/ ((^symsuc) /\ g (SUC n) sh)
	      = (^state) IN {(^state) | ?(j:num). j<=(SUC n) /\ ((^syml) /\ (g j sh))}``,
	      REPEAT STRIP_TAC 
	      THEN CONV_TAC (FORK_CONV ((LAND_CONV (pred_setLib.SET_SPEC_CONV)),pred_setLib.SET_SPEC_CONV))
	      THEN SIMP_TAC std_ss []
	      THEN EQ_TAC THEN DISCH_TAC THEN (TRY CONJ_TAC) THENL 
	      [
	       RW_TAC std_ss [] THENL 
	       [
		Q.EXISTS_TAC `j` THEN FULL_SIMP_TAC arith_ss [],
		 Q.EXISTS_TAC `SUC n` THEN FULL_SIMP_TAC arith_ss []
	       ],
	       RW_TAC std_ss []
	       THEN Cases_on `j=SUC n` THENL
	       [
		DISJ2_TAC THEN FULL_SIMP_TAC arith_ss [],
		DISJ1_TAC THEN Q.EXISTS_TAC `j` THEN FULL_SIMP_TAC arith_ss []
	       ]
	      ])) end

fun mk_sum_component_aux n i s = 
    if (i=0) then sumSyntax.mk_inl(s,mk_vartype("'a"^(int_to_string i))) 
    else if (i=1 andalso n=2) then sumSyntax.mk_inr(s,mk_vartype("'a"^(int_to_string i))) 
    else sumSyntax.mk_inr(mk_sum_component_aux (n-1) (i-1) s,mk_vartype("'a"^(int_to_string i))) 

(* returns s tagged with INL's and INR's so that its type is the i'th component of the sum ty_0+ty_1+...+ty_(n-1) *)
fun mk_sum_component ty i s = 
    if ((List.length (sumSyntax.strip_sum ty)) = 1) then s
    else let val tys = sumSyntax.strip_sum ty
	     val n = List.length tys
	     val res = mk_sum_component_aux n i s
	     val tysp = split_after i tys
	     val stl = if (i=(n-1)) then [] else [(sumSyntax.list_mk_sum o List.tl) (snd tysp)] 
             val nl = if i = (n-1) then List.tabulate(n-1,fn n => n +1) else List.tabulate(n-(n-i)+1,I)   
	 in inst (List.map (fn (j,t) => mk_vartype("'a"^(int_to_string j)) |-> t) 
			   (ListPair.zip(List.rev nl,(fst tysp)@stl))) res 
	 end

(* returns s:(ty_0+ty_1+...+ty_(n-1)) tagged with OUTL's and OUTR's to strip away the sum type 
 assuming s is the i'th component in the sum *)
fun dest_sum_component styl n i s =
if (n=1) then s (* there is only one component *)
else if (i = 0) then mk_comb(inst [alpha |-> List.hd styl,beta |-> list_mk_sum (List.tl styl)] outl_tm,s)
else if (i = 1 andalso n = 2) then mk_comb(inst [alpha |-> List.hd styl,beta |-> list_mk_sum (List.tl styl)] outr_tm,s)
else dest_sum_component (List.tl styl) (n-1) (i-1) (mk_comb(inst [alpha |-> List.hd styl,beta |->list_mk_sum (List.tl styl)] outr_tm,s))

(* return a HL function proj i that returns the substate of st corresponding to the i'th VC (given here by vc) *) 
(* basically we reorder vc to respect that of st *)
(* ASSERT: this assumes that order in st is the state order *)
fun find_substate_proj_fn st vcl = 
    let val state = pairSyntax.list_mk_pair st
	val substates = List.map (fn vc => pairSyntax.list_mk_pair (List.foldr (fn (t,ass) => if Binaryset.member(vc,t) 
											      then t::ass else ass) 
									   [] st))
			     vcl
	val sty = sumSyntax.list_mk_sum(List.map (type_of o pairSyntax.list_mk_pair o Binaryset.listItems) vcl)
	val (_,res) = List.foldl (fn (si,(n,ac)) => (n+1,mk_cond(mk_eq(mk_var("i",``:num``),
								       numSyntax.mk_numeral(Arbnum.fromInt(n))),
								 mk_sum_component sty n si,ac)))
				 (0,``ARB:(^(ty_antiq(sty)))``) substates
    in  hd(Defn.eqns_of(Hol_defn "ss_proj" `ss_proj (i:num) (^state) = (^res)`)) end

(* abbreviates the hiR so eventual h term is more succinct *)
fun mk_hR_thms hiRl sty vcl = 
    let val (substates,substates') = ListPair.unzip(ListPair.map (pairSyntax.list_mk_pair ## (pairSyntax.list_mk_pair o 
									  (List.map (mk_primed_bool_var o term_to_string2)))) (vcl,vcl))
    in list2imap (List.map (fn ((n,hiR),(si,si')) =>
		 let val hiRty =  mk_type("fun",[mk_prod(type_of si,type_of si'),``:bool``])
		     val _ = new_constant("hR_"^(int_to_string n),hiRty)
		 in (n, hd(Defn.eqns_of(Hol_defn ("hR_"^(int_to_string n)) 
					`(^(mk_const("hR_"^(int_to_string n),hiRty))) (^(mk_pair(si,si'))) = (^hiR)`))) 
		 end) 		     
		  (ListPair.zip(ListPair.zip(List.tabulate(List.length vcl,I),hiRl),	
				ListPair.zip(substates,substates'))))

    end

fun mk_FC'' ((fvt',t')::fvl) (fvt,t) ofvl = 
       if (Binaryset.isEmpty(Binaryset.intersection(fvt,fvt'))) 
       then mk_FC'' fvl (fvt,t) ofvl
       else let val ofvl' = List.filter (fn (_,t) => not(Term.compare(t,t')=EQUAL)) ofvl 
	    in Binaryset.add(mk_FC'' ofvl' (Binaryset.union(fvt,fvt'),t) ofvl',(fvt',t')) end
| mk_FC'' [] (fvt,t) ofvl = Binaryset.add (Binaryset.empty (Term.compare o (snd ## snd)),(fvt,t))

fun mk_FC' ((fvt,t)::fvl) = 
    let val fvs' = mk_FC'' fvl (fvt,t) fvl
	val fvs = Binaryset.addList(Binaryset.empty (Term.compare o (snd ## snd)),fvl)
    in (fvs'::(mk_FC' (Binaryset.listItems (Binaryset.difference(fvs,fvs'))))) end
| mk_FC' [] = [] 

(* T : (string * term) list is (action name, transition relation) *)
(* FIXME: for the moment we assume each transition is of the form v' = f(v1...vn) for each next state variable v' *)
(* however note that not all next-state vars are used i.e. some are read-only, or don't cares *)
(*  because of these assums this will only run for the alu example *)
(* output: list of (VC:``bool`` set,FC:``term`` list) clusters (Clarke's ce guided abs ref paper)
   as well as |VC| HOL projection thms on the concrete state of the form |- (substate for the i'th VC) = ss_proj i conc_state *) 
fun mk_FC T1 state apl =
    let val t = if (List.length T1)>1 then list_mk_conj (List.map snd T1) else snd (List.hd T1)
        val tc = List.map pbody apl
        val fvl = ListPair.zip(List.map (fn t => Binaryset.addList(Binaryset.empty Term.compare, free_vars t)) tc,tc)
	val vcfc = mk_FC' fvl
        val vcfcl = List.map (fn l => List.foldl (fn ((fvt,t),(fvta,ta)) => (Binaryset.union(fvt,fvta),t::ta)) 
						 (Binaryset.empty Term.compare,[]) l) (List.map Binaryset.listItems vcfc) 
        val st = strip_pair state
        val pfn_def = find_substate_proj_fn st (List.map fst vcfcl)
	val pfn_thms = List.foldl (fn ((t,n),ba) => 
				    Binarymap.insert(ba,n,
						     GSYM (SIMP_CONV arith_ss [pfn_def] 
							   (mk_comb(mk_comb(fst(strip_comb(lhs(concl 
											       (SPEC_ALL pfn_def)))),t),state))))) 
	    (Binarymap.mkDict Int.compare) (List.tabulate(List.length vcfcl,fn n => (numSyntax.mk_numeral(Arbnum.fromInt(n)),n)))
    in (vcfcl,pfn_thms) end 

fun bdd_list_conj (h::t) = bdd.AND (h,bdd_list_conj t)
|   bdd_list_conj [] = bdd.TRUE;      

(* t is a monomial over the vars in state *)
(* return a concrete tuple of bools such that assigning the bools to state gives a satisfying assignment for t *)
fun mk_conc_state state t = 
    let val st = strip_pair state
        val cs = List.map (fn v => find_term (fn t => Term.compare(mk_neg(v),t)=EQUAL) t handle ex => T) st
        in list_mk_pair (List.map (fn t => if (Term.compare(t,T)=EQUAL) then T else F) cs) end 

(* the disj of tb with the appex'd stuff is required to ensure correct construction of reachable set if R is not total
     currently the way we construct h requires R to be defined functionally which automatically makes it total
     so that the disj is not really necessary but this is just to make the formalization easier (i.e. not reliant on total R) *)
fun findSCC' T1 ee sp s2sp s sp2s state state' conc_seed fb =
      let val _ = DMSG (ST " fSCC'\n") (dbgceart)(*DBG*)
	  fun iter e2 n = 
	  let 
	      val _ = DMSG (ST "iter ") (dbgceart)(*DBG*)
	      val _ = DMSG (TM  n) (dbgceart)(*DBG*)
	      val _ = DMSG (ST "\n") (dbgceart)(*DBG*)
	      val tb = Binarymap.find(e2,"Q")
	      val (Step_def,ReachRec_def,bb) = 
		  if fb (* if ReachFrom *)
		  then (Next_def, ReachFromRec_def,(BddOp(bdd.Or,tb,BddReplace sp2s (BddAppex s (bdd.And,Binarymap.find(T1,"."),tb)))) )
		  else (Prev_def,ReachToRec_def,(BddOp(bdd.Or,tb,BddAppex sp (bdd.And,Binarymap.find(T1,"."),(BddReplace s2sp tb)))))
	      val th1 = CONV_RULE 
			    (RHS_CONV SET_SPEC_CONV) 
			    ((CONV_RULE (RHS_CONV (ONCE_REWRITE_CONV [GSYM SPECIFICATION])))  
				 (AP_THM (ISPECL [conc_seed,n]  
						 ((REWRITE_RULE [Step_def](ISPEC (mk_pabs(mk_pair(state,state'),
											  getTerm(Binarymap.find(T1,"."))))
										 (List.last(CONJUNCTS ReachRec_def)))))) state))
              val th2 =  REWRITE_RULE [SPECIFICATION] 
				      (CONV_RULE 
					   (DEPTH_CONV PairRules.PBETA_CONV) 
					   (ONCE_REWRITE_RULE [PairRules.GEN_PALPHA_CONV state' ( snd(dest_disj(rhs(concl th1))))] th1))
	      val th3 = SYM(ONCE_REWRITE_RULE [holCheckTools.ELIM_TUPLED_QUANT_CONV (snd(dest_disj(rhs(concl th2))))] th2)
	      val bb = BddEqMp (REWRITE_CONV [] (getTerm bb)) bb handle ex => bb (* FIXME: ad hoc *) 
	      val itr = BddEqMp (REWRITE_RULE [] th3) bb 
	  in if (bdd.equal (getBdd tb) (getBdd itr)) then 
		 let val eqbdd = BddThmOracle(BddOp(bdd.Biimp,tb,itr))
		     val mpthm = (if fb then ReachFromFP else ReachToFP)
		     val thm = MATCH_MP mpthm (PEXT (PairRules.PGEN state eqbdd))
		     val thm2 = BddEqMp (AP_THM (SYM thm) state) tb 
		     val _ = DMSG (ST "fSCC' done\n") (dbgceart)(*DBG*)		
		 in thm2 end
	     else iter (Binarymap.insert(e2,"Q",itr)) ``SUC ^n`` end
      in iter ee ``0:num`` end

(* currently T1 has only the . transition and the aim is to find all states reachable from tb and all states that can reach tb *)
(* this is technically not an SCC detection since T1(".") need not be total but I'll call it that anyway *)
fun findSCC T1 state tb vm sty n = 
    let val _ = DMSG (ST "fSCC\n") (dbgceart)
	val state' = mk_primed_state state
	val s = strip_pair state
	val sp = strip_pair state'
	val conc_seed = (mk_conc_state state (getTerm tb))
	val s2sp = List.map (fn(v,v') => (BddVar true vm v,BddVar true vm v')) (ListPair.zip(s,sp))
	val sp2s = List.map (fn(v,v') => (BddVar true vm v,BddVar true vm v')) (ListPair.zip(sp,s))
	val tbRFthm = (CONV_RULE (DEPTH_CONV SET_SPEC_CONV) 
			  ((CONV_RULE (RHS_CONV (ONCE_REWRITE_CONV [GSYM SPECIFICATION])) 
				    (AP_THM (REWRITE_CONV [ReachFromRec_def] 
					     ``ReachFromRec ^(mk_pabs(mk_pair(state,state'),getTerm(Binarymap.find(T1,".")))) 
					     (^(conc_seed)) 0``) state))))
	val tbRF = BddEqMp (SYM (ONCE_REWRITE_RULE [prove(``(^( rhs(concl(tbRFthm))))=(^(getTerm tb))``,
							  REWRITE_TAC [IN_SING] 
							  THEN SIMP_TAC std_ss [AC CONJ_ASSOC CONJ_COMM])] tbRFthm)) tb
        val tbRTthm = (CONV_RULE ((DEPTH_CONV SET_SPEC_CONV)) 
			  ((CONV_RULE (RHS_CONV (ONCE_REWRITE_CONV [GSYM SPECIFICATION])) 
				    (AP_THM (REWRITE_CONV [ReachToRec_def] 
					     ``ReachToRec ^(mk_pabs(mk_pair(state,state'),getTerm(Binarymap.find(T1,".")))) 
					     (^(conc_seed)) 0``) state)))) 
	val tbRT = BddEqMp (SYM (ONCE_REWRITE_RULE [prove(``(^( rhs(concl(tbRTthm))))=(^(getTerm tb))``,
							  REWRITE_TAC [IN_SING] 
							  THEN SIMP_TAC std_ss [AC CONJ_ASSOC CONJ_COMM])] tbRTthm)) tb
	val tbr =findSCC' T1 (Binarymap.insert(Binarymap.mkDict String.compare,"Q",tbRF)) 
	    sp s2sp s sp2s state state' conc_seed true
        val tbc =findSCC' T1 (Binarymap.insert(Binarymap.mkDict String.compare,"Q",tbRT)) 
	    sp s2sp s sp2s state state' conc_seed false
	val res = BddEqMp (SYM (REWRITE_RULE  [SPECIFICATION] (CONV_RULE (RHS_CONV SET_SPEC_CONV) 
			 (CONV_RULE (RHS_CONV ((ONCE_REWRITE_CONV [GSYM SPECIFICATION]))) (AP_THM 
		       (ISPECL [(mk_pabs(mk_pair(state,state'),getTerm(Binarymap.find(T1,".")))),mk_conc_state state (getTerm tb)] 
					    (REWRITE_RULE [UNION_DEF] SCC_def)) state)))))
			  (BddOp(bdd.Or,tbr,tbc))
	val _ = DMSG (ST "fSCC done\n") (dbgceart)(*DBG*)
    in res  end

(* h_iR is conjunction of f_j(s)=f_j(s') where f_j \in FC_i
   We start with S = all states over VC_i
   Then pick a random state in S (using SAT) and call it vbar3 (all the other v*** vars are used to compute this 
   Then compute eqc as the equivalence class of vbar3 wrt hi_R.
     This uses findSCC which computes EF(vbar3) \/ EP(vbar3) and pretends that h_iR is a transition relation.
   Add eqc to the list h_i^k (which we call hikl)
   Compute S' = S\eqc and repeat mk_eqc with S' until S is empty. 
   At this point h_i^k contains the partitions of S wrt h_iR *)
fun mk_eqc S vm vm2 hikl state hiR proj_thm sty n = 
    if (bdd.equal (getBdd S) bdd.FALSE)
    then let val _ = DMSG (ST "mk_eqc done\n") (dbgceart)(*DBG*)
	 in hikl end
    else 
    let val _ = DMSG (ST "SC:") (dbgceart) val _ = DMSG (NM (round(DerivedBddRules.statecount (getBdd S)))) (dbgceart)(*DBG*)
        val lvm = List.map term_to_string (strip_pair state)
        val vbar = List.map (fn (v,tv) => mk_eq(mk_bool_var v,if tv then T else F)) 
	                (List.map ((Option.valOf o (getVarForInt vm)) ## I) (bdd.getAssignment (bdd.satone (getBdd S))))
        val vall = List.map (mk_bool_var o fst) (List.filter 
		      (fn (v,i) => Option.isSome(List.find (fn v' => (String.compare(v,v')=EQUAL)) lvm)) (Binarymap.listItems vm2))
        val vmap = List.foldl (fn (v,bm) => Binarymap.insert(bm,v,T)) (Binarymap.mkDict Term.compare) (List.map (fst o dest_eq) vbar)
	val vbar = List.foldl (fn (v,vbar') => if (Option.isSome(Binarymap.peek(vmap,v))) then vbar' else (mk_eq(v,T))::vbar') vbar vall
        val vbar2 = List.map (rhs o concl o (REWRITE_CONV [])) vbar
        val vbar3 = t2tb vm (list_mk_conj vbar2)
	val T2 = Binarymap.insert(Binarymap.mkDict String.compare,".",hiR)
        val eqc = findSCC T2 state vbar3 vm sty n
	val (proj,ll) = strip_comb(lhs(concl(SYM (SPEC_ALL proj_thm))))
	val i = List.nth(ll,0)
	val state = List.nth(ll,1)
        val eqc2 = BddConv (REWRITE_CONV [SIMP_CONV (arith_ss++sumSimps.SUM_ss) [SYM proj_thm] 
			    (dest_sum_component (strip_sum sty) (List.length(strip_sum sty)) n (list_mk_comb(proj,[i,state])))]) eqc  
        val hikl = eqc2::hikl        
    in mk_eqc (BddOp(bdd.And,S,BddNot eqc2)) vm vm2 hikl state hiR proj_thm sty n end 

(* returns the bool equiv of n as a monomial over {av_0,...,av_nabsv} *) 
fun n2b nabsv n = 
    let val n1 = (rhs o concl o (REWRITE_CONV []) o fst) 
	(List.foldr 
	 (fn (b,(t,n'))=> (mk_conj(let val av = mk_bool_var("av"^(int_to_string n')) 
				   in if (Char.compare(b,#"0")=EQUAL) then mk_neg av else av end,t),n'+1)) 
	 (``T``,0) (String.explode(Word.fmt StringCvt.BIN (Word.fromInt n))))
    in if (List.length(strip_conj n1)=nabsv) then n1 
       else List.foldl (fn (t,n2) => mk_conj(t,n2)) n1 
	   (List.tabulate(nabsv-(List.length(strip_conj n1)),
			  fn n => mk_neg(mk_bool_var("av"^(int_to_string (List.length(strip_conj n1)+n)))))) end

(* returns the bool equiv of n as a vector *) 
fun n2bv nabsv n = pairSyntax.list_mk_pair(list_dest_conj (n2b nabsv n))

(* given a list of n ``SCC R s_i s`` term-bdds, returns the types of the s_i as a sum type *)
fun get_eqc_type sccl = sumSyntax.list_mk_sum(List.map type_of ( List.map (fn tb => List.nth(snd(strip_comb (getTerm tb)),1)) sccl))

(* given a list of n ``SCC R s_i s`` term-bdds, returns the conditional mapping i to s_i *)
(* since the s_i are substates of varying size, the target type of the conditional is a sum given by get_eqc_type sccl *)
(* later make the conditional a binary tree for faster eval, and to drop the test if n = 1 *)
fun mk_cond_seed_state sccl = 
    let val _ = DMSG (ST " mk_cond_seed_state\n") (dbgceart)
	val l = List.map (fn tb => List.nth(snd(strip_comb (getTerm tb)),1)) sccl
	val (_,res) = List.foldl (fn (si,(n,ac)) => (n+1,mk_cond(mk_eq(mk_var("i",``:num``),
								       numSyntax.mk_numeral(Arbnum.fromInt(n))),
								 mk_sum_component (get_eqc_type sccl) n si,ac)))
		  (0,``ARB:^(ty_antiq(get_eqc_type sccl))``) l 
    in res end

(* given a list of i=0..(n-1)  ``SCC R (seed i j) s`` terms, return the thm
   |- !j. SCC R (seed 0 j) s  /\ ... /\ SCC R (seed (n-1) j) s = s IN {s | !i. i<=n-1 ==> SCC R (seed i j) s}   *)
fun mk_seed_conj_spec_thm sccl = 
    let val n = List.length sccl
        val l = List.map (fn t => let val (scc,ll) = strip_comb t
				      val (sd,_) = strip_comb (List.nth(ll,1))
                                      in list_mk_comb(scc,[List.hd ll,list_mk_comb(sd,[mk_var("i",``:num``),
										       mk_var("j",``:num``)]),
							   List.last ll]) end) sccl
    in if n=1 then GEN (mk_var("j",``:num``)) (let val (scc,ll) = strip_comb (List.hd sccl)
						    val (sd,ll2) = strip_comb (List.nth(ll,1))
						    val i = List.hd ll2
						    val j = List.last ll2
						    val s = List.last ll
						    val scc2 = list_mk_comb(scc,[List.hd ll,
										 list_mk_comb(sd,[i, mk_var("j",``:num``)]),
										 s])
						in REWRITE_CONV [SCC_INNER_FOLD_BASE1] scc2 end)
       else GEN (mk_var("j",``:num``)) (List.foldl (fn (t, th) => ((REWRITE_RULE [GSYM th]) o 
							      (ONCE_REWRITE_CONV [SCC_INNER_FOLD_STEP] THENC numLib.REDUCE_CONV)) 
				  (mk_conj (rhs(concl th),rhs(concl((ONCE_DEPTH_CONV numLib.num_CONV) t)) ))) 
	       (ONCE_REWRITE_CONV [SCC_INNER_FOLD_BASE] (mk_conj(List.hd l,List.hd(List.tl l)))) 
	       (List.tl (List.tl l))) end

(* the h_iR are conjunctions over j of f_j(s)=f_j(s') where f_j \in FC_i
   each eqcl_i is a list containing the partitions of S (all states over VC_i) wrt h_iR. each partition eqcl_i_j is a tb (called b).
   abvt is the bit representation (as a monomial over av_i) of j e.g. abvt of 2 would be ~av0 /\ av1 (av0 being the lsb)
   eqccombs is the cartesian product of the sets (i.e. lists) in eqcl
   then each element in eqccombs corresponds to an abstract state 
     note that each element is a list of partitions (from the FC's) that are conjuncted (see May 29, 2003 notes on fixing h) 
   then abs_fun is the conjunction over eqccombs of all eqccombs_i = abvt of i 
   aref is the refinement. 
      if NONE then no refinement is required i.e. this is the initial abstraction
      else aref is SOME (n,dead,bad)  returned from ref_abs and the computation proceeds as before 
        except the nth abstract state is to be replaced by dead and a new abstract state created for bad *)
fun mk_abs_fun (vcfcl,pfn_thms) vm state hname aref = 
    let val state' = mk_primed_state state
	(*val s = strip_pair state
	val s' = strip_pair state'*)
	val vcl  = List.map (Binaryset.listItems o fst) vcfcl
        val vctbl = List.map (List.map (t2tb vm)) vcl
        val vctbl' = List.map (List.map (fn v => t2tb vm (mk_bool_var((term_to_string v)^"'")))) vcl
        val fctbl = List.map ((List.map (t2tb vm)) o snd) vcfcl
	val fctbl' = List.map (fn ((vctb,vctb'),fctb) => List.map (PrimitiveBddRules.BddReplace (ListPair.zip(vctb,vctb'))) fctb) 
	    (ListPair.zip((ListPair.zip(vctbl,vctbl'),fctbl)))
        val hiRl = List.map ((BddListConj vm) o (ListPair.map (fn (fctb,fctb') => PrimitiveBddRules.BddOp(bdd.Biimp,fctb,fctb')))) 
	    (ListPair.zip(fctbl,fctbl'))
        val vm2 = list2map (List.filter (fn (v,i) => not (List.last(explode(v))=(#"'")))  (Binarymap.listItems vm))
	val sty = sumSyntax.list_mk_sum(List.map (type_of o pairSyntax.list_mk_pair) vcl)
        val hR_thms =  mk_hR_thms (List.map getTerm hiRl) sty vcl
	val _ = List.app (fn th => DMSG (TH th) (dbgceart)) (List.map snd (Binarymap.listItems hR_thms))
        val eqcl = List.map (fn (n,(hiR,vc)) => mk_eqc (BddCon true vm) vm vm2 [] 
						       state
						       (BddEqMp (SYM (SPEC_ALL (Binarymap.find(hR_thms,n)))) hiR)
						         (Binarymap.find(pfn_thms,n)) sty n) 
	    (ListPair.zip(List.tabulate(List.length vcl,I),ListPair.zip(hiRl,vcl)))
	(* |eqc_combs| = # of abstract states needed. FIXME: construct abs_fun while doing the cartprod *)
        val eqc_combs = cartprod eqcl 
        val nhi = List.length eqcl (* # of h_i in h *)
        val nabsv = Real.ceil(log2(Real.fromInt(List.length eqc_combs))) (* # of abs state vars needed *)    
        val astate = pairSyntax.list_mk_pair(List.tabulate(nabsv,fn i => mk_bool_var("av"^(int_to_string i))))
        val (rn,dead,bad) = if Option.isSome aref then Option.valOf aref else (~1,BddCon true vm,BddCon true vm) 
	val (n,ab,st,vm) = List.foldl (fn (eqc_comb,(n,aag,aaf,vm)) =>
				     let val abvt = n2b nabsv n
					 val vm' = List.foldl (* add any newly created abstract vars to the varmap *) 
						  (fn (v,bm) => 
						      if Option.isSome(Binarymap.peek(bm,v)) then bm
						      else let val n = Binarymap.numItems bm
							   in Binarymap.insert(Binarymap.insert(bm,v,n),v^"'",n+1) end)
						  vm  (List.map term_to_string (free_vars abvt))
					 val _ = if (bdd.getVarnum()<(Binarymap.numItems vm')) 
						 then bdd.setVarnum (Binarymap.numItems vm') else ()
					 val (ss,ab) = if (rn=n) (* this never happens if aref is NONE becuase then rn is -1 *)
						  then (``T``,``T``) (* FIXME: fix this for refinement case *)
						  else (mk_cond_seed_state eqc_comb,abvt)
				     in (n+1,mk_cond(mk_eq(mk_var("j",``:num``),numSyntax.mk_numeral(Arbnum.fromInt(n))),ab,aag),
					     mk_cond(mk_eq(mk_var("j",``:num``),numSyntax.mk_numeral(Arbnum.fromInt(n))),ss,aaf),
					 vm')
				     end)  
	    (0,``ARB:bool``,``ARB:^(ty_antiq(get_eqc_type (List.hd eqc_combs)))``,vm) eqc_combs
	(* FIXME: would it be faster to define abst as a monomial generator? *)
        val abst_def = hd(Defn.eqns_of(Hol_defn "abst"  `abst (j:num) (^astate) = (^ab)` ))
        val seed_def =  hd(Defn.eqns_of(Hol_defn "seed" `seed (i:num) (j:num) = (^st)`))
        (*val seeds = List.map mk_prod_seed_state eqc_combs*)
        val abst_thms = List.foldl (fn ((t,n),ba) => 
				    Binarymap.insert(ba,n,
						     GSYM (SIMP_CONV arith_ss [abst_def] 
							   (mk_comb(mk_comb(fst(strip_comb(lhs(concl 
											       (SPEC_ALL abst_def)))),t),astate))))) 
	    (Binarymap.mkDict Int.compare) (List.tabulate(List.length eqc_combs,fn n => (numSyntax.mk_numeral(Arbnum.fromInt(n)),n)))
        val seed_thms = List.foldl  
	    (fn ((tj,j),ba) => 
	     Binarymap.insert(ba,j,
			      (List.map (GSYM o (SIMP_CONV (arith_ss++sumSimps.SUM_ss) [seed_def]))
			       (List.map (fn (ti,i) => 
					  (dest_sum_component 
					   (strip_sum (get_eqc_type (List.nth(eqc_combs,j)))) 
					   (List.length(List.nth(eqc_combs,j))) i 
					   (list_mk_comb(fst(strip_comb(lhs(concl(SPEC_ALL seed_def)))),[ti,tj]))))
					  (List.tabulate(List.length(List.nth(eqc_combs,j)),
							 fn n =>(numSyntax.mk_numeral(Arbnum.fromInt(n)),
								 n)))))))      
	     (Binarymap.mkDict Int.compare)
	     (List.tabulate(List.length eqc_combs, fn n => (numSyntax.mk_numeral(Arbnum.fromInt(n)),n)))
        val lhs_tbs = List.map (fn (j,eqc_comb) => BddListConj vm 
				(List.map (fn (tb,i) => 
					   BddConv (PURE_REWRITE_CONV [List.nth(Binarymap.find(seed_thms,j),i)]) tb) 
				 (ListPair.zip(List.map (BddExtendVarmap vm) eqc_comb,List.tabulate(List.length eqc_comb,I)))))
	     (ListPair.zip(List.tabulate(List.length eqc_combs,I),eqc_combs))
        (*val scs_thm = mk_seed_conj_spec_thm (list_dest_conj (getTerm (List.hd lhs_tbs1)))
        val lhs_tbs = List.map (BddConv (ONCE_REWRITE_CONV [scs_thm])) lhs_tbs1*)
        val sc_tbs = List.map (fn (j,tb) => BddOp(bdd.And,tb,
						  BddConv (PURE_ONCE_REWRITE_CONV [Binarymap.find(abst_thms,j)])
						  (t2tb vm (n2b nabsv j)))) 
	    (ListPair.zip(List.tabulate(List.length lhs_tbs,I),lhs_tbs))
	val (SCC_FOLD_BASE,SCC_FOLD_STEP) = mk_scc_fold_thms (list_dest_conj (getTerm (List.hd lhs_tbs))) state
	val abs_fun_base = BddConv (ONCE_REWRITE_CONV [SCC_FOLD_BASE]) (BddOp(bdd.Or,BddExtendVarmap vm (List.hd sc_tbs),   
									      BddExtendVarmap vm (List.hd (List.tl sc_tbs))))
	val (n,abs_fun) = List.foldl (fn (sc_tb,(n,aaf)) =>
				      let val atb = if (rn=n) (* this never happens if aref is NONE becuase then rn is -1 *)
							then BddOp(bdd.Biimp,BddExtendVarmap vm dead,t2tb vm (n2b nabsv n))
						    else sc_tb
				      in (n+1,BddConv (ONCE_REWRITE_CONV [SCC_FOLD_STEP] THENC numLib.REDUCE_CONV)
					  (BddOp(bdd.Or, BddExtendVarmap vm aaf,
						 BddConv 
						 (REWRITE_CONV 
						  ((List.map (RAND_CONV numLib.num_CONV) 
						    (find_terms (can (match_term ``seed x y``)) (getTerm atb))) @
						  (List.map (LAND_CONV numLib.num_CONV) 
						   (find_terms (can (match_term ``abst x y``)) (getTerm atb))))) atb)))
				      end) 
	    (0,abs_fun_base) (List.tl (List.tl sc_tbs))
        val abs_fun = if (rn=(~1)) then abs_fun 
		      else BddOp(bdd.And,abs_fun,BddOp(bdd.Biimp,BddExtendVarmap vm bad,t2tb vm (n2b nabsv (n+1))))
	val hn = if (Option.isSome hname) then Option.valOf hname else "af"
	val _ = new_constant(hn,mk_type("fun",[mk_prod(type_of state,type_of astate),``:bool``]))
	val hnc = mk_const(hn,mk_type("fun",[mk_prod(type_of state,type_of astate),``:bool``]))
        val hd_def =  hd(Defn.eqns_of(Hol_defn hn `(^hnc)(^state,^(astate)) = ^(getTerm abs_fun)`))
    in (astate,abst_def,hR_thms,hd_def,BddEqMp (SYM (SPEC_ALL hd_def)) abs_fun) end


(* prove that the concrete abs_funs is total, by building the bdd *)
(* FIXME: can we prove this offline by completely formalizing the construction of the abs fun? *)
fun mk_abs_fun_total_thm abs_fun = 
    let val (state,astate) = (strip_pair ## strip_pair) (dest_pair(snd(dest_comb(getTerm abs_fun))))
    in  REWRITE_RULE [SYM (CONV_RULE (RHS_CONV (STRIP_QUANT_CONV ELIM_TUPLED_QUANT_CONV)) 
			   (ELIM_TUPLED_QUANT_CONV (mk_pforall(list_mk_pair state,mk_pexists(list_mk_pair astate,getTerm abs_fun)))))] 
	(BddThmOracle(BddForall state (BddExists astate abs_fun)))
    end

(* function the alpha-convs IS_ABS_FUN_def to use concrete state, astate and h *)
fun mk_conc_is_abs_fun_def st1 st2 astate abs_fun ks_def = 
    let val hit_tot = STRIP_QUANT_CONV o RHS_CONV  o LAND_CONV 
	val th = INST_TYPE [``:'state`` |-> type_of st1, ``:'astate`` |-> type_of astate] IS_ABS_FUN_def
	val th1 = CONV_RULE (hit_tot (QUANT_CONV (GEN_PALPHA_CONV astate))) th 
	val th2 = CONV_RULE (hit_tot (GEN_PALPHA_CONV st1)) th1
	val hit_ap = STRIP_QUANT_CONV o RHS_CONV  o RAND_CONV
	val th3 = CONV_RULE (hit_ap (QUANT_CONV (QUANT_CONV (GEN_PALPHA_CONV astate)))) th2 
	val th4 = CONV_RULE (hit_ap (QUANT_CONV (GEN_PALPHA_CONV st2))) th3 
	val th5 = CONV_RULE (hit_ap (GEN_PALPHA_CONV st1)) th4
	val aht  = mk_pabs(mk_pair(st1,astate),getTerm abs_fun)
	val ksname = lhs(concl ks_def)
in PBETA_RULE (GEN_ALL (ISPECL [ksname,mk_var("e",mk_type("fun",[``:string``,mk_type("fun",[type_of st1,``:bool``])])),aht] th5)) end

(* mk refined abstraction function and the is_abs_fun thm for it as well (to be used by mk_abs_cons_thm) *)
fun mk_ref_abs_fun af state astate ks_def ath_lem1 ath_lem2 hd_def idx dead bad k = 
    let val nabsv = Real.ceil(log2(Real.fromInt(k+1))) (* to check if new abstract state requires another abs var to be added *)
	val astate2 = if (List.length (strip_pair astate))=nabsv then astate 
		      else list_mk_pair ((mk_var("av"^(int_to_string(nabsv-1)),bool))::(strip_pair(astate)))
	val astate_k = n2b nabsv (k+1) (* monomial corresponding to new astract state; bad goes here *)
	val astate_r = n2b nabsv idx (* monomial for abstract state that got split into dead and bad; dead stays here *)
	val vm = getVarmap af
	val tb_k = t2tb vm astate_k
	val tb_r = t2tb vm astate_r
	(* refined abstraction function af' is (dead /\ sh_r) \/ (bad /\ sh_k) \/ (~sh_r /\ ~sh_k /\ af) *)
	val af' = BddOp(bdd.Or,BddOp(bdd.Or,BddOp(bdd.And,bad,tb_k),BddOp(bdd.And,dead,tb_r)),
			BddListConj vm [BddNot tb_k,BddNot tb_r,af]) 
	val hn = term_to_string2(fst(dest_comb(lhs(concl(SPEC_ALL hd_def)))))^"'"
	val _ = new_constant(hn,mk_type("fun",[mk_prod(type_of state,type_of astate),bool]))
	val hnc = mk_const(hn,mk_type("fun",[mk_prod(type_of state,type_of astate),bool]))
        val hd_def2 = hd(Defn.eqns_of(Hol_defn hn  `(^hnc)(^state,^(astate)) = ^(getTerm af')`))
	val ast_excl_thm1 = DECIDE (mk_imp(astate_k,mk_neg astate_r))
    	val ast_excl_thm2 = DECIDE (mk_imp(astate_r,mk_neg astate_k))
	val lst1 = List.tabulate(List.length (strip_pair state),fn n => mk_bool_var("v"^(int_to_string n))) 
	val lst2 = List.tabulate(List.length (strip_pair state),fn n => mk_bool_var("w"^(int_to_string n))) 
	val subst1 = ListPair.map (fn (v,v') => v |-> v') (strip_pair state,lst1)
	val subst2 = ListPair.map (fn (v,v') => v |-> v') (strip_pair state,lst2)
	val goal = mk_imp(mk_conj(subst subst1 (getTerm af'),subst subst2 (getTerm af')),snd(dest_imp(concl(SPEC_ALL ath_lem1))))
	val ath_lem1' = GEN_ALL (REWRITE_RULE [GSYM hd_def2] (prove(goal, (* prove new ath_lem1 using the old one *)
			     MAP_EVERY ASSUME_TAC [ast_excl_thm1,ast_excl_thm2]
			     THEN Cases_on `^astate_k` THEN Cases_on `^astate_r` 
			     THEN Q.ABBREV_TAC `ak = ^astate_k` THEN Q.ABBREV_TAC `ar = ^astate_r` 
			     THEN FULL_SIMP_TAC std_ss []
			     THEN PROVE_TAC [ath_lem1])))
	val st1 = list_mk_pair lst1
	val st2 = list_mk_pair lst2
	val afap = PGENL [st1,st2,astate] (IMP_TRANS (SPEC_ALL ath_lem1') (SPEC_ALL ath_lem2))
	val af' = BddEqMp (SYM (SPEC_ALL hd_def2)) af' 
	val aftot = mk_abs_fun_total_thm af' 
	val iaf = CONV_RULE (DEPTH_CONV PETA_CONV) 
	    (REWRITE_RULE [GSYM hd_def2] (REWRITE_RULE [CONJ aftot afap] (mk_conc_is_abs_fun_def st1 st2 astate af' ks_def)))
    in (af',ath_lem1',astate2,hd_def2,iaf) end

(* creates abstracted Tm and I and passes them to mk_wfKS and returns the results *)
(* h is the abs_fun as returned by mk_abs_fun *)
fun mk_abs_ks I1 T1 RTm state Ric af aksname (apl,ks_def,wfKS_ks) hd_def = 
    let val T1 = Binarymap.listItems RTm 
        val st = strip_pair state
        val state = pairSyntax.list_mk_pair st
        val st_ty = type_of state
        val s = List.map term_to_string2 st	
	val st' =  List.map mk_primed_bool_var s
	val state' = list_mk_pair st'
	val vm' = getVarmap af  
	val s2s' = List.map (fn(v,v') => (BddVar true vm' v,BddVar true vm' v')) (ListPair.zip(st,st'))
	val vmabs = List.filter (fn (t,_) => String.compare("av",String.substring(t,0,2))=EQUAL) (Binarymap.listItems vm')
        val (abst,abst') = List.partition (fn s => not (Char.compare(#"'",List.last(String.explode(term_to_string s)))=EQUAL)) 
	    (List.map mk_bool_var (fst(ListPair.unzip vmabs)))
	val astate = pairSyntax.list_mk_pair abst
	val astate' = pairSyntax.list_mk_pair abst'	
        val abstcnj = t2tb vm' (list_mk_conj abst)
        val abstcnj' = t2tb vm' (list_mk_conj abst')
        val as2as' =  List.map (fn(v,v') => (BddVar true vm' v,BddVar true vm' v')) (ListPair.zip(abst,abst'))
        val Itb = t2tb vm' I1 
        val Ih = BddExists st (BddOp(bdd.And,af,Itb))
        val Th = List.map (fn (actnm,act) => (actnm,BddExists st (BddExists st' 
				(BddOp(bdd.And,BddOp(bdd.And,BddExtendVarmap vm' act, 
						     af),BddReplace as2as' (BddReplace s2s' af)))))) T1
        val Iht = getTerm Ih
	val T1h = List.map (fn (nm,tb) => (nm,getTerm tb)) Th
	val aksname = if (Option.isSome aksname) then Option.valOf aksname else "aks"
	val (aapl,aks_def,wfKS_aks,aRTm) = mk_wfKS Iht T1h (SOME (list2map Th)) astate vm' Ric NONE (SOME af) (SOME aksname)	
	val aht = mk_pabs(mk_pair(state,astate),getTerm af)
        val aksth = mk_abs_eq_thm state state' astate astate' (List.length st) hd_def ks_def aks_def 
				  ``^(lhs (concl aks_def)) = ABS_KS ^(lhs (concl ks_def)) ^aht`` 
	val abs_aks = CONV_RULE (RHS_CONV (RAND_CONV PETA_CONV)) aksth 
    in (Iht,T1h,Ih,abs_aks,(aapl,aks_def,wfKS_aks,aRTm)) end

(* prove the second part of the IS_ABS_FUN assum (the first part is totality) *)
fun mk_abs_fun_ap_thm state astate hR_thms_ abst_def (apl,ks_def,wfKS_ks) hd_def = 
    let val ht = rhs(concl(SPEC_ALL hd_def))
	val ht1 = mk_pforall (state,ht)
	val lst1 = List.tabulate(List.length (strip_pair state),fn n => mk_bool_var("v"^(int_to_string n))) 
	val lst2 = List.tabulate(List.length (strip_pair state),fn n => mk_bool_var("w"^(int_to_string n))) 
	val st1 = list_mk_pair lst1
	val st2 = list_mk_pair lst2
	val t1 = snd(dest_pforall(rhs(concl(GEN_PALPHA_CONV st1 ht1))))
	val t2 = snd(dest_pforall(rhs(concl(GEN_PALPHA_CONV st2 ht1))))
	val (k',t1s) = dest_conj(snd(boolSyntax.dest_exists(rhs(concl((pred_setLib.SET_SPEC_CONV THENC SIMP_CONV std_ss []) t1)))))
	val t2s = snd(dest_conj(snd(boolSyntax.dest_exists(rhs(concl((pred_setLib.SET_SPEC_CONV THENC SIMP_CONV std_ss []) t2))))))
	val hR_thms = List.map snd (Binarymap.listItems hR_thms_)
	val hR_sz = List.map (fn th => (((List.length o fst o strip_forall o concl) th) div 2,
					(fst o dest_comb o lhs o concl o SPEC_ALL)th )) hR_thms
	val (_,_,hR_eqs) = List.foldl (fn ((sz,nm),(lst1,lst2,cj)) => 
					  (List.drop(lst1,sz),
					   List.drop(lst2,sz),
					   mk_conj(cj,mk_comb(nm,mk_pair(list_mk_pair(List.take(lst1,sz)),
									 list_mk_pair(List.take(lst2,sz))))))) 
				      (lst1,lst2,T) hR_sz
	val hR_eqs = list_mk_conj (List.tl (strip_conj hR_eqs))
	val k = List.last(snd(strip_comb k'))
	val boa_thm = BETA_RULE (ISPECL [mk_abs(``j:num``,t1s),mk_abs(``j:num``,t2s),k] BIGOR_OVER_AND)
	val abstlhsi = lhs(snd(strip_forall(rhs(concl(SPEC_ALL(GEN_ALPHA_CONV ``i:num`` (concl abst_def)))))))
	val abstlhsj = lhs(snd(strip_forall(rhs(concl(SPEC_ALL(GEN_ALPHA_CONV ``j:num`` (concl abst_def)))))))
	val abst_lem2 = prove(mk_forall(``i:num``,mk_imp(mk_conj(mk_leq(``i:num``,k),abstlhsi), (* FIXME: this is *slow* for k>5 *)
							 mk_forall(``j:num``,mk_imp(mk_conj(mk_leq(``j:num``,k),abstlhsj),
										    mk_eq(``i:num``,``j:num``))))),
			      REWRITE_TAC [abst_def] THEN RW_TAC std_ss [] THEN FULL_SIMP_TAC arith_ss [])
	val abst_lem3 = MATCH_MP abst_lem1 abst_lem2
	val abst_lem4 = prove(list_mk_forall
				  ([``i:num``,``j:num``,``P:bool``],
				   mk_eq(list_mk_conj[mk_leq(``i:num``,k),mk_leq(``j:num``,k),abstlhsi,abstlhsj,``P:bool``],
					 list_mk_conj [mk_leq(``i:num``,k),mk_leq(``j:num``,k),mk_eq(``i:num``,``j:num``),
						       abstlhsi,abstlhsj,``P:bool``])),
				  REPEAT STRIP_TAC THEN EQ_TAC THENL 
					 [
					  ASSUM_LIST (fn t => PROVE_TAC (abst_lem3::t)),
					  PROVE_TAC []
					  ])
	val sri = SIMP_RULE std_ss [IN_DEF] SCC_REL_IMP
	val eqr_hR_thms = List.map 
			      (fn (th,t) => prove
					    (mk_comb(inst [alpha |-> type_of (fst(dest_pair(snd(dest_comb(lhs(concl(SPEC_ALL th)))))))] 
							  ``R_EQR``,t),
					     SIMP_TAC std_ss [R_EQR_def,R_REFL_def,R_SYM_def,R_TRANS_def,th] 
						      THEN REPEAT CONJ_TAC 
						      THEN PBETA_TAC 
						      THEN metisLib.METIS_TAC []))
			      (ListPair.zip(hR_thms,List.map (fn t => List.hd (snd (strip_comb t))) 
							     (List.rev(List.tl(List.rev(strip_conj t1s))))))
	val ath_lem1 =  prove(mk_imp(mk_conj(t1,t2),hR_eqs),
			      CONV_TAC(LAND_CONV(FORK_CONV(pred_setLib.SET_SPEC_CONV,pred_setLib.SET_SPEC_CONV)))
				      THEN SIMP_TAC std_ss [boa_thm]
				      THEN SIMP_TAC std_ss [AC CONJ_COMM CONJ_ASSOC]
				      THEN REWRITE_TAC [abst_lem4]
				      THEN MAP_EVERY ASSUME_TAC eqr_hR_thms
				      THEN RW_TAC std_ss []
				      THEN IMP_RES_TAC sri
				      THEN FULL_SIMP_TAC std_ss [])
	val lm = GEN_ALL (REWRITE_RULE [GSYM hd_def] ath_lem1)
	val ksname = lhs(concl ks_def)
	val apl' = List.map (fn ap => mk_pabs(st2,subst (List.map (fn (v,w) => v |-> w) (ListPair.zip(lst1,lst2))) (pbody ap))) apl
	val ap_thms =  List.map (* FIXME: clean this up, too much duplication of work in creation of the msa's, Lth and gen_ap_thms*)
			   (fn th => SIMP_RULE std_ss [MU_SAT_def] (GSYM th)) 
			   (let val prop_type = mk_type("fun",[type_of state,bool])
				val Lth = ksTools.mk_Lth ksname (type_of state) prop_type ks_def
				val msa1 =  PBETA_RULE (PURE_REWRITE_RULE 
					      [Lth] (MATCH_MP (CONV_RULE FORALL_IMP_CONV (ISPECL [st1,ksname] MU_SAT_AP)) wfKS_ks))
				val msa2 =  PBETA_RULE (PURE_REWRITE_RULE 
					      [Lth] (MATCH_MP (CONV_RULE FORALL_IMP_CONV (ISPECL [st2,ksname] MU_SAT_AP)) wfKS_ks))
			    in (List.map (fn mf =>  muCheck.mk_gen_ap_thm ksname st1 msa1 mf) (List.map (fn ap => ``AP ^ap``) apl))
			       @ (List.map (fn mf =>  muCheck.mk_gen_ap_thm ksname st2 msa2 mf) (List.map (fn ap =>  ``AP ^ap``) apl'))
			    end)
	val ath_lem2 = prove(mk_forall(mk_var("e",mk_type("fun",[``:string``,mk_type("fun",[type_of state,``:bool``])])),
				       mk_imp(hR_eqs,``!p. p IN (^ksname).ap ==>
				     ((^st1) IN STATES (AP p) (^ksname) e = (^st2) IN STATES (AP p) (^ksname) e)``)),
				     NTAC 3 STRIP_TAC
				     THEN CONV_TAC (LAND_CONV (SIMP_CONV std_ss [ks_def,KS_accfupds,combinTheory.K_DEF]))
				     THEN  RW_TAC std_ss [IN_INSERT,NOT_IN_EMPTY]
				     THEN  FULL_SIMP_TAC std_ss (ap_thms@hR_thms))
    in (st1,st2,lm,ath_lem2,PGENL [st1,st2,astate]  (IMP_TRANS ath_lem1 (SPEC_ALL ath_lem2))) end

(* prove the three formula related assumptions to ABS_CONS_MODEL *)
fun mk_abs_cons_mf_thms mf (apl,ks_def,wfKS_ks) =
let val no_rv = prove (``!Q. ~SUBFORMULA (~RV Q) (NNF (^mf))``,
		      SIMP_TAC std_ss (MU_SUB_def::NNF_def::RVNEG_def::(tsimps "mu")))
    val no_dmd = prove (``(!a g. ~SUBFORMULA <<a>> g (NNF (^mf)))``,
		       Induct_on `g` THEN SIMP_TAC std_ss (MU_SUB_def::NNF_def::RVNEG_def::(tsimps "mu")))
    val p_in_ap = prove (``!p. SUBFORMULA (AP p) (^mf) ==> p IN (^(lhs(concl ks_def))).ap``,
		       SIMP_TAC std_ss (ks_def::KS_accfupds::combinTheory.K_DEF::MU_SUB_def::NNF_def::RVNEG_def::(tsimps "mu")) 
		       THEN RW_TAC std_ss [] 
		       THEN CONV_TAC (pred_setLib.IN_CONV stringLib.string_EQ_CONV))
in [no_rv,no_dmd,p_in_ap] end

(* create the concrete thm to discharge the IS_ABS_FUN assum to ABS_CONS_MODEL *)
fun mk_is_abs_fun_thm abs_fun state astate hR_thms_ abst_def (apl,ks_def,wfKS_ks) hd_def = 
    let val aftot = mk_abs_fun_total_thm abs_fun 
	val (st1,st2,ath_lem1,ath_lem2,afap) = mk_abs_fun_ap_thm state astate hR_thms_ abst_def (apl,ks_def,wfKS_ks) hd_def 
	val afap = REWRITE_RULE [GSYM hd_def] afap
    in (ath_lem1,ath_lem2,CONV_RULE (DEPTH_CONV PETA_CONV) 
	(REWRITE_RULE [GSYM hd_def] (REWRITE_RULE [CONJ aftot afap]  (mk_conc_is_abs_fun_def st1 st2 astate abs_fun ks_def)))) end

(* discharge, online, the assumptions to ABS_CONS_MODEL *)
(* note enveq thm requires that both env and aenv be empty: this is true for instance if mf was originally in CTL*/LTL/CTL etc. *)
(* FIXME: split this so that we can discharge the non-mf_assums once in one func, and discharge mf_assums again and again for each mf, 
   thus saving time, since iaf is at the moment expensive to compute but does not change with mf *)
fun mk_abs_cons_thm mf (apl,ks_def,wfKS_ks) env aenv hd_def iaf_ = 
    let val mf_assums = mk_abs_cons_mf_thms mf (apl,ks_def,wfKS_ks)
	val hnc = fst(dest_comb(lhs(concl(SPEC_ALL hd_def))))
	val enveq = prove(``(!Q s sh. (^hnc) (s,sh) ==> sh IN (^aenv) Q ==> s IN (^env) Q)``,
			  SIMP_TAC std_ss [EMPTY_ENV_def,NOT_IN_EMPTY]);
	val iaf = ISPEC env iaf_
	val acm1 = ISPECL [mf,hnc,lhs(concl(ks_def)),env,aenv] ABS_CONS_MODEL
 in List.foldl (fn (mpth,th) => MATCH_MP th mpth) acm1  ([wfKS_ks]@mf_assums@[iaf,enveq]) end

(* ASSERT: t must be a QBF *)
(* transforms input QBF to pure propositional formula using |- (?x. P x) = P T \/ P F and |- (!x. P x) = P F /\ P T *)
fun elim_quant t = 
if is_exists t then let val (v,t') = dest_exists t 
		    in mk_disj(elim_quant (subst [v |-> ``T``] t'),elim_quant (subst [v |-> ``F``] t')) end 
else if is_forall t then let val (v,t') = dest_forall t 
		    in mk_conj(elim_quant (subst [v |-> ``T``] t'),elim_quant (subst [v |-> ``F``] t')) end 
else if is_neg t then mk_neg (elim_quant(dest_neg t)) 
else if is_conj t then mk_conj(elim_quant(fst(dest_conj t)),elim_quant(snd(dest_conj t))) 
else if is_disj t then mk_disj(elim_quant(fst(dest_disj t)),elim_quant(snd(dest_disj t))) 
else if is_eq t then mk_eq(elim_quant(fst(dest_eq t)),elim_quant(snd(dest_eq t))) 
else if is_imp t then mk_imp(elim_quant(fst(dest_imp t)),elim_quant(snd(dest_imp t))) 
else t

fun mlval tm = if tm=T then true else if tm=F then false else raise Match

fun mk_ass vm red res = bdd.assignment (ListPair.map (fn (v,c) => (Binarymap.find(vm,term_to_string2 v),mlval c)) (red,res)) 

(* check whether abstract counterexample atr has concrete counterpart upto nth state of the abstract counterexample trace*)
fun check_ace' atr I1 T1 state Ric astate h n = 
    if (n=0) then SOME [] else
    let 
	val _ = DMSG (ST "check_ace' \n") (dbgceart)(*DBG*)
	val state' = mk_primed_state state
        val (st,st') = (strip_pair state,strip_pair state')
        val s = List.map term_to_string2 st	
	val ace_states = atr
        val ast = pairSyntax.strip_pair astate
        val cce_states = List.tabulate(n,fn i => pairSyntax.list_mk_pair(List.map (fn v => mk_bool_var(v^"_"^(Int.toString i))) s))
	val init_f = subst (mk_subst st (strip_pair(List.hd cce_states))) I1
	val R1 = (if Ric then list_mk_conj else list_mk_disj) (List.map snd T1) 
        val trans_f = if (n=1) then T (* special casing because list_mk_conj [] crashes *) 
		      else (list_mk_conj (List.map (fn(stn,stn') => subst ((mk_subst st (strip_pair stn))@(mk_subst st' (strip_pair stn')))
						R1) (List.tl(ListPair.zip(``T``::cce_states,cce_states)))))
        val hb = getBdd h
	val vm = getVarmap h
	val abs_f =  list_mk_conj(List.map (fn (astc,cst) => subst (mk_subst st (strip_pair cst)) 
								  (b2t vm (bdd.restrict hb (mk_ass vm ast (strip_pair astc)) )))
					    (ListPair.zip(ace_states,cce_states)))
        val f = list_mk_conj [init_f,trans_f,abs_f]
        val cnf = defCNF.DEF_CNF_CONV f
        val satth = SOME (satProve zchaff (snd(strip_exists(rhs(concl cnf))))) handle ex => NONE
        val ctr = if Option.isSome satth (* return concrete trace if one was found else NONE *)
		      then let val l = strip_conj(fst(dest_imp(concl (Option.valOf satth))))
			       val bm = List.foldl (fn (v,bm) => if (is_neg v) then Binarymap.insert(bm,dest_neg v,``F``)
								 else Binarymap.insert(bm,v,``T``)) (Binarymap.mkDict Term.compare) 
				   (snd(List.partition 
				    (fn v => 						 
				     let val vs = term_to_string (if is_neg v then dest_neg v else v)
				     in (String.size vs >= 8) andalso 
					 (String.compare(String.substring(vs,0,10),"%%genvar%%")=EQUAL) end) l))
			       val cce = List.map (fn stp => let val l = pairSyntax.strip_pair stp
							     in pairSyntax.list_mk_pair (List.map (fn v => Binarymap.find(bm,v)) l) end) 
				         cce_states 
			   in SOME cce end 
		  else NONE
	val _ = DMSG (ST "check_ace' done \n") (dbgceart)(*DBG*)
    in ctr end

(* call check_ace' for increasing n until non-SAT happens then return the greatest (i.e. previous) SAT-able path *)
fun check_ace'' atr I1 T1 state Ric astate h n = 
    let val ctr = check_ace' atr I1 T1 state Ric astate h n
    in if (Option.isSome ctr) then let val ctr' = check_ace'' atr I1 T1 state Ric astate h (n+1) 
				   in if (Option.isSome ctr') then ctr' else ctr end 
       else ctr end

 
(* check whether abstract counterexample atr has concrete counterpart *)
(* if yes return concrete counterpart else return concrete counterpart upto (not including) the state that fails satisfiability *)
(* to check if full counterexample was discovered we can compare the length of the returned counterexample with atr *)
(* atr is output from get_ce. FIXME thmfy ctr *)
fun check_ace atr I1 T1 state Ric astate h = 
    let val atrsz = List.length atr
        val ctr = check_ace' atr I1 T1 state Ric astate h atrsz (* check if there is a full concrete counterexample *)
        val ctr' = if (Option.isSome ctr) then ctr
		   else check_ace'' atr I1 T1 state Ric astate h 1 (* if not then find longest concrete prefix *)
    in ctr' end

fun contract_vm vl tb =  List.foldl (fn (v,tb) => BddFreevarsContractVarmap v tb) tb vl

(* h as returned by mk_abs_fun. ctr as returned by check_ace, atr as returned by find_trace1 
   as_1 is abstract state to be refined. as_2 is the state after as_1 in the ace. h^-1 is inverse of h. ast is symbolic abstract state
   compute bad = <"."> h^-1(as_2) /\ h^-1(as_1) 
    i.e. bad \subseteq as_1 and all states in bad and no other in h^-1(as_1) have a transition to h^-1(as_2)
   compute dead = h^-1(as_1)\bad i.e. all other states in h^-1(as_1)
   fially n is just the index of as_1    *)
(* FIXME: can we do without requiring the BDD of M.R? *)
fun ref_abs atr ctr state RTm astate h = 
    let val as1 = pairSyntax.strip_pair(List.nth(atr,(List.length ctr)-1))
	val as2 = pairSyntax.strip_pair(List.nth(atr,(List.length ctr)))
	val ast = strip_pair astate
	val vm = getVarmap h
        fun s2res vm st vt = ListPair.zip(List.map (fn v => BddVar true vm v) st,
					    List.map (fn v => BddCon (Term.compare(v,T)=EQUAL) vm) vt)
        val cS1 = BddRestrict (s2res vm ast as1) h (* h^-1(as_1) *)
	val cS2 = BddRestrict (s2res vm ast as2) h (* h^-1(as_2) *)
	val st = pairSyntax.strip_pair state
        val s = List.map term_to_string2 st
	val st' =  List.map mk_primed_bool_var s
        val s2s' = List.map (fn(v,v') => (BddVar true vm v,BddVar true vm v')) (ListPair.zip(st,st'))
	val bad = BddOp(bdd.And,cS1,BddAppex st' (bdd.And, BddExtendVarmap vm (Binarymap.find(RTm,".")),(BddReplace  s2s' cS2)))
	val dead = (BddOp(bdd.And,cS1,BddNot bad))
	val n = List.foldl (fn (v,n) => if Term.compare(v,T)=EQUAL then 2*n else 2*n+1) 0 as1
  in (n,dead,bad) end

fun absCheck_aux I1 T1 RTm Ric state (apl,ks_def,wfKS_ks) astate hd_def af ath_lem1 ath_lem2 iaf env aenv Ree k mf mu_init_cache_snd =
    let 
	val _ = DMSG (ST "absCheck_aux\n") (dbgceart)(*DBG*)
	val (aI1,aT1,aItb,abs_aks,(abpl,aks_def,wfKS_aks,aRTm)) = mk_abs_ks I1 T1 RTm state Ric af NONE (apl,ks_def,wfKS_ks) hd_def
	val vm'' = PrimitiveBddRules.getVarmap (Binarymap.find(aRTm,"."))
	val ((tb,tbth,ace),mu_init_cache) = muCheck.muCheck Ree aI1 aT1 astate vm'' Ric (ref NONE) ((SOME af), SOME aItb) 
	                                         (SOME (abpl,aks_def,wfKS_aks,aRTm),mu_init_cache_snd) mf
	val cth = if (not (Option.isSome ace)) (* final success theorem *)
		      then let val acm = mk_abs_cons_thm mf (apl,ks_def,wfKS_ks) env aenv hd_def iaf
			   in  SOME (MP acm (REWRITE_RULE [abs_aks] (Option.valOf tbth))) end
		  else NONE
	val cce = if (Option.isSome ace)  (* concrete counter example (or prefix if ace was spurious) *)
		  then check_ace (Option.valOf ace) I1 T1 state Ric astate af 
		  else NONE
    in if (Option.isSome cth) then ((tb,cth,NONE),snd(mu_init_cache)) (* success *)
       else if (List.length (Option.valOf cce)) = (List.length (Option.valOf ace)) then ((tb,NONE,cce),snd(mu_init_cache)) (* failure *)
	    else let val (idx,dead,bad) = ref_abs (Option.valOf ace) (Option.valOf cce) state RTm astate af (* refine *) 
		     val (af,ath_lem1,astate,hd_def,iaf)=mk_ref_abs_fun af state astate ks_def ath_lem1 ath_lem2 hd_def idx dead bad k
               in absCheck_aux I1 T1 RTm Ric state (apl,ks_def,wfKS_ks) astate 
		   hd_def af ath_lem1 ath_lem2 iaf env aenv Ree (k+1) mf NONE end
    end

(* property independent theorems and data that needs to be initialised only once per model *)
fun init_abs T1 state vm (apl,ks_def,wfKS_ks,RTm) = 
    let val (vcfcl,pfn_thms) = mk_FC T1 state apl
	val (astate,abst_def,hR_thms_,hd_def,af) = mk_abs_fun (vcfcl,pfn_thms) vm state NONE NONE handle ex => Raise ex
	val (ath_lem1,ath_lem2,iaf) = mk_is_abs_fun_thm af state astate hR_thms_ abst_def (apl,ks_def,wfKS_ks) hd_def
	val env = inst [alpha |-> type_of state] ``EMPTY_ENV``
	val aenv = inst [alpha |-> type_of astate] ``EMPTY_ENV``
	val Ree = Array.fromList []
	val (t,_,_) = dest_cond (rhs(concl(SPEC_ALL abst_def)))
	val k = (Arbnum.toInt(numSyntax.dest_numeral (snd(dest_eq t)))) (* k+1 is current number of abstract states *)
    in ((astate,abst_def,hR_thms_,hd_def,af),state,env,aenv,Ree,(ath_lem1,ath_lem2,iaf),k) end

(* given concrete model M and a formula f, returns M |= f where the model checking has been done on an abstracted version of M *) 
(* NOTE: our abstraction framework is only for universal properties; the second check is because if all AP are state vars then 
	 there is no abstraction anyway so avoid waste of time; this check will change once non-bool state vars are supported *)
(* this function just computes the init data (or picks it from the init_cache); the real action takes place in absCheck_aux *)
(* FIXME: can the horrible type annotation to init_cache be got rid of? *)
fun absCheck I1 T1 state Ric vm apl ksname 
    (init_cache:((term list * thm * thm * (string,term_bdd) dict) option * 
		 ((thm list * (thm * term_bdd option * term) * 
		   (thm * (thm * thm) * term list * (term_bdd * term_bdd) list) *
		   (thm * thm * thm * thm * term * term * term * term * term list * 
		    hol_type)) * term * thm list) option * 
		 ((term * thm * (int, thm) dict * thm * term_bdd) * term * term * term *  
		  (string * term_bdd) array * (thm * thm * thm) * int) option) option) 
    mf = 
    let 
	val (apl,ks_def,wfKS_ks,RTm) = if Option.isSome init_cache andalso Option.isSome (#1(Option.valOf init_cache))
					   then let val (apl',ks_def,wfKS_ks,RTm) = Option.valOf (#1(Option.valOf init_cache))
						in if List.null apl' then  mk_wfKS I1 T1 (SOME RTm) state vm Ric apl NONE ksname
						   else  (apl',ks_def,wfKS_ks,RTm) end
				       else mk_wfKS I1 T1 NONE state vm Ric apl NONE ksname
    in if is_existential mf orelse (List.foldl (fn (ap,t) => t andalso (is_var(pbody ap))) true apl) 
	   then let val mu_init_cache_snd =  if Option.isSome init_cache andalso Option.isSome (#2 (Option.valOf init_cache))
						 then  #2(Option.valOf init_cache) else NONE
		    val (res,mu_init_cache) = muCheck (Array.fromList []) I1 T1 state vm Ric (ref NONE) (NONE,NONE) 
	                                                                     (SOME (apl,ks_def,wfKS_ks,RTm),mu_init_cache_snd) mf 
		in (res,SOME (SOME (apl,ks_def,wfKS_ks,RTm),snd(mu_init_cache),NONE)) end  
       else let val ((astate,abst_def,hR_thms_,hd_def,af),state,env,aenv,Ree,(ath_lem1,ath_lem2,iaf),k) = 
	   if Option.isSome init_cache andalso Option.isSome (#3(Option.valOf init_cache)) 
	       then Option.valOf(#3(Option.valOf init_cache))
	   else init_abs T1 state vm (apl,ks_def,wfKS_ks,RTm) 
		val (ath_lem1,ath_lem2,iaf) = if (Term.compare(concl ath_lem1,T)=EQUAL) 
					      then mk_is_abs_fun_thm af state astate hR_thms_ abst_def (apl,ks_def,wfKS_ks) hd_def
					      else (ath_lem1,ath_lem2,iaf)
		val mu_init_cache_snd = if Option.isSome init_cache andalso Option.isSome (#2(Option.valOf init_cache)) 
					then #2(Option.valOf init_cache) else NONE
	    in let val (res,mu_init_cache_snd) = absCheck_aux I1 T1 RTm Ric state (apl,ks_def,wfKS_ks) 
		                             astate hd_def af ath_lem1 ath_lem2 iaf env aenv Ree k mf mu_init_cache_snd
	       in (res,	
		   (SOME(SOME (apl,ks_def,wfKS_ks,RTm),
			 mu_init_cache_snd, 
			 SOME ((astate,abst_def,hR_thms_,hd_def,af),state,env,aenv,Ree,(ath_lem1,ath_lem2,iaf),k)))) 
	       end
	    end
    end
	
end
end







