(*List.app load ["bossLib","stringTheory","stringLib","HolBddLib","pairTheory","pred_setLib","listLib","CTL","pairSyntax","pairRules","pairTools","muTheory","boolSyntax","Drule","Tactical","Conv","Rewrite","Tactic","boolTheory"]*)

structure muCheck =
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
open muSyntax
open muSyntaxTheory
open muTheory
open boolSyntax
open Drule
open Tactical
open Conv
open Rewrite
open Tactic
open boolTheory
open listSyntax 
open stringTheory
open stringBinTree
open boolSimps 
open pureSimps
open listSimps
open numLib
open muTools
open holCheckTools
open ksTheory
open HolSatLib
open defCNF
open cearTheory
open bddTools
open envTheory
open envTools
open cacheTools
open cacheTheory
open ksTools

val dbgmc = holCheckTools.dbgall
val dbginit = holCheckTools.dbgall

fun DMSG m v = if v then let val _ = print "muCheck: " val _ = holCheckTools.DMSG m v in () end else ()

val cntap = ref 0 val cntrv = ref 0 val cntcj = ref 0 val cntdj = ref 0 val cntng = ref 0 val cntdm = ref 0 val cntbx = ref 0
val cntmu = ref 0 val cntnu = ref 0 val cntfpitfn = ref 0 val cntfpitit = ref 0
val tmap = ref 0.0 val tmrv = ref 0.0 val tmcj = ref 0.0 val tmdj = ref 0.0 val tmng = ref 0.0 val tmdm = ref 0.0 val tmbx = ref 0.0
val tmmu = ref 0.0 val tmnu = ref 0.0
val tmbobb = ref 0.0 val tmboth = ref 0.0 val tmbobe = ref 0.0
val tmfpoh = ref 0.0 val tmfpit = ref 0.0 val tmfpitfn = ref 0.0 val tmfpitit = ref 0.0
val mtmr = ref (Timer.startRealTimer())

in 

fun mk_imf_thms mf seth tysimps = 
    let 
	val _ = DMSG (ST "mk_imf_thms\n") (dbgmc) (*DBG*)
        val gls = (find_terms (can (match_term ``mu Q..f``)) mf)@(find_terms (can (match_term ``nu Q..f``)) mf)
    in  List.foldl (fn (gl,bm) => Binarymap.insert(bm,gl, prove(mk_comb(``IMF``,gl),
		      SIMP_TAC std_ss ([IMF_def,MU_SUB_def,NNF_def,RVNEG_def]
				   @tysimps
				   @(List.map (fn (rv,eqs) => eqs) (flatten(List.map (fn (rv,bm)=>Binarymap.listItems bm) 
										     (Binarymap.listItems seth)))))))) 
		    (Binarymap.mkDict Term.compare) gls end

fun mk_gen_ap_thm ksname state msa mf = 
    let 
	val _ = DMSG (ST "(make_gen_ap)\n") (dbgmc)(*DBG*)
	val _ = DMSG (TM mf) (dbgmc)  val _ = DMSG (ST  "mf\n") (dbgmc) 
	val _ = DMSG (TH  msa) (dbgmc) val _ = DMSG (ST  "msa\n") (dbgmc)(*DBG*)
        val ap = snd(dest_comb mf)
	val _ = DMSG (TM  ap) (dbgmc) val _ = DMSG (ST  " ap\n") (dbgmc)(*DBG*)
        val apth = GSYM(PBETA_RULE (SPEC ap ((CONV_RULE SWAP_VARS_CONV) msa))) 
	val _ = DMSG (TH  apth) (dbgmc) val _ = DMSG (ST  "(apth) \n") (dbgmc)(*DBG*)
	val _ = DMSG (ST ("(make_gen_ap) done\n")) (dbgmc)(*DBG*)
    in apth end

fun mk_gen_modal_thm Tth modth mf = 
    let 
	val _ = DMSG (ST ("(make_gen_modal)\n")) (dbgmc)(*DBG*)
        val nm = hd(snd(strip_comb mf))
	val ks1 = AP_THM Tth nm
	val ks2 = PURE_REWRITE_RULE [find_CONV (mk_comb(snd(dest_eq(concl Tth)), nm))] ks1
    in PairRules.PBETA_RULE (PURE_REWRITE_RULE [ks2] (SPEC nm modth)) end

(* returns mappings for each rv v->(x->"v"="x") where x are all the rv's in the formula (binding occurances included) *)
(* except for the cases v=x because that gives a trivial thm that causes the rewriter to loop *)
fun mk_seths mf =
    let 
	val _ = DMSG (ST  "mk_seths\n") (dbgmc)(*DBG*)
	val rvs = Binaryset.addList(Binaryset.empty Term.compare,
				    ((List.map (fn tm => snd(dest_comb tm)) 
				      (find_terms (can (match_term ``(RV x):^(ty_antiq(type_of mf))``)) mf))
				    @(List.map (fn tm => List.hd(snd(strip_comb tm))) 
					       (find_terms (can (match_term ``(mu Q .. f):^(ty_antiq(type_of mf))``)) mf))
				    @(List.map (fn tm => List.hd(snd(strip_comb tm))) 
					       (find_terms (can (match_term ``(nu Q .. f):^(ty_antiq(type_of mf))``)) mf)))
				    )
        val seglpairs = List.map (fn l => (hd l,last l)) (cartprod [Binaryset.listItems rvs,Binaryset.listItems rvs])
        val segl2 = List.map (fn v => (v,list2map(List.map (fn (x,y) => (fromHOLstring y,mk_eq(x,y))) 
				(List.filter (fn (x,y) => Term.compare(x,v)=EQUAL) 
				 seglpairs)))) (Binaryset.listItems rvs)
	val tth = GEN_ALL(List.last(CONJUNCTS (SPEC_ALL EQ_CLAUSES)))
	val seths = list2map(List.map (fn (v,gll) => (fromHOLstring v,Binarymap.map (fn (y,gl) =>
					   PURE_REWRITE_RULE [tth] (stringLib.string_EQ_CONV gl)) gll)) segl2) 	
	val _ = DMSG (ST  "mk_seths done\n") (dbgmc)(*DBG*)
        in seths end

fun mk_gen_rv_thms mf ksname state rvl ie wfKS_ks =
   let  
       val _ = DMSG (ST ("(make_gen_rv)\n")) (dbgmc)(*DBG*)
       val msr = MATCH_MP (CONV_RULE FORALL_IMP_CONV  (ISPECL [state,ksname] MU_SAT_RV)) wfKS_ks
       val msreq = ISPEC state (MATCH_MP (ISPEC ksname MU_SAT_RV_ENV_EQ) wfKS_ks)
       val _ = DMSG (ST ("(make_gen_rv done)\n")) (dbgmc)(*DBG*)
   in (msr,mk_seths mf,msreq) end

fun mk_gen_thms T (apl,ks_def,wfKS_ks) state state' st vm = 
   let  
       val _ = DMSG (ST  "(mk_gen_thms)\n") (dbgmc)(*DBG*)
       val tmr = Timer.startRealTimer()(*PRF*)
       (* Note: this assumes varmap assignments are contiguous stating from zero TODO: get rid of this assumption *)
       val i2ap = Vector.fromList (List.map (fn ap => BddVar true vm ap) st)
       val apnm2ix =fst(Vector.foldl (fn(nm,(bm,ix)) => (Binarymap.insert(bm,term_to_string2(getTerm(nm)),ix),ix+1)) 
				      (Binarymap.mkDict String.compare,0) i2ap)
       (*val _ = DMSG (ST ("vector i2ap\n")) (dbgmc) 
         val _ = Vector.app (fn nm => DMSG (ST ("("^(term_to_string(getTerm nm))^")")) (dbgmc)) i2ap(*DBG*)
         val _ = DMSG (ST ("mapnm2ix\n")) (dbgmc) 
         val _ =Binarymap.app (fn(nm,ix)=> DMSG (ST ("("^nm^","^(int_to_string ix)^")"))) (dbgmc) apnm2ix(*DBG*)*)
       val state_type = type_of state
       val stpset_ty = mk_type("fun",[mk_prod(state_type,state_type),bool])
       val env_ty = list_mk_fun([``:string``,state_type],bool)
       val ksname = lhs(concl ks_def)
       val prop_type = mk_type("fun",[state_type,bool])
       val KSap = List.foldl (fn (e,ac) => ``^e INSERT ^ac``) (``{}:^(ty_antiq(mk_type("fun",[prop_type,bool])))``) apl
       val msthl = List.map (fn th => MATCH_MP (CONV_RULE FORALL_IMP_CONV (ISPECL [state,ksname] th)) wfKS_ks) 
	   (MU_SAT_AP::MU_SAT_DMD::MU_SAT_BOX::[MU_SAT_T,MU_SAT_F,MU_SAT_NEG,MU_SAT_CONJ,MU_SAT_DISJ])
       val Lth = mk_Lth ksname state_type prop_type ks_def
       val msa = PBETA_RULE (PURE_REWRITE_RULE [Lth] (List.nth(msthl,0)))
       val msp = List.map GSYM (List.drop(msthl,3))	
       val (Tth,dmdth) = mk_Tth ks_def ksname (List.nth(msthl,1)) (List.nth(msthl,2)) state' state_type prop_type  
       val githms = mk_gen_inv_thms ksname state wfKS_ks
       val _ = DMSG (ST (Time.toString(Timer.checkRealTimer tmr))) (dbgmc)(*PRF*)
       val _ = DMSG (ST (" (mk_gen_thms end)\n")) (dbgmc)(*DBG*)        
   in (msp,msa,Tth,dmdth,githms) end

(* note this assumes that an AP is a boolean term *)
(* if AP's are over non-booleans, then we do suitable preprocessing on the model to turn stuff into booleans
   otherwise you can't make BDD's out of them *)						
fun mk_ap_tb vm absf mf sth = 
    let 
	val _ = DMSG (ST  "(mk_ap_tb)\n") (dbgmc)(*DBG*)
        val _ = DMSG (TM  mf) (dbgmc) val _ = DMSG (ST  "(mf)\n") (dbgmc)(*DBG*)
        val _ = DMSG (TH  sth) (dbgmc) val _ = DMSG (ST  "(sth)\n") (dbgmc)(*DBG*)
	val ap = pbody (snd (dest_comb mf))
        val tb =  if (Option.isSome absf) then 
		      let val htb = Option.valOf absf 
			  val ht = getTerm htb 
			  val cstate = fst(dest_pair(List.hd (snd (strip_comb ht))))
		      in BddExists (strip_pair cstate) (BddOp(bdd.And,htb, t2tb vm ap)) end
		  else t2tb vm ap
	val _ = DMSG (TM (getTerm tb)) (dbgmc) val _ = DMSG (ST  "(tb)\n") (dbgmc)(*DBG*)
	val res = BddEqMp sth tb
	val _ = DMSG (ST  "(mk_ap_tb done)\n") (dbgmc)(*DBG*)
    in res  end 

fun mk_con_tb_tm vm tm = if (Term.compare(tm,``T:bool``)=EQUAL) then BddCon true vm else BddCon false vm

fun mk_con_tb b vm mf sth = 
    let 
	val _ = DMSG (ST  " mk_con_tb\n") (dbgmc)(*DBG*)
	(*val _ = DMSG (TH  sth) (dbgmc)(*DBG*)
	val _ = DMSG (ST  " sth\n") (dbgmc)(*DBG*)*)
	val res = BddEqMp sth (BddCon b vm) 
	val _ = DMSG (ST  " mk_con_tb done\n") (dbgmc)(*DBG*)
    in res end

fun mk_rv_tb ee (_,_,_,_,ix,_,_,_,_,_) mf sth  = 
    let 
	val _ = DMSG (ST  " mk_rv_tb\n") (dbgmc)(*DBG*)
	(*val _ = DMSG (TH  sth) (dbgmc)(*DBG*) 
	val _ = DMSG (ST  "rv tb sth\n") (dbgmc)(*DBG*) 
	val _ = DMSG (ST  (int_to_string ix)) (dbgmc)(*DBG*)
	val _ = DMSG (ST  " ix\n") (dbgmc)(*DBG*)  
	val _ = DMSG (ST  (int_to_string (Array.length ee))) (dbgmc)(*DBG*) 
	val _ = DMSG (ST  " ee length\n") (dbgmc)(*DBG*) 
	val _ = DMSG (TM  (getTerm (snd(Array.sub(ee,ix))))) (dbgmc)(*DBG*)
	val _ = DMSG (ST  "rv tb\n") (dbgmc)(*DBG*)*)
	val res = BddEqMp sth (snd(Array.sub(ee,ix))) 
	(*val _ = DMSG (TM  (getTerm res)) (dbgmc)(*DBG*)*)
	val _ = DMSG (ST  "mk_rv_tb done\n") (dbgmc)(*DBG*)
    in res end

fun mk_rv_spec_thm msr seth msreq ie ee (tb,gth,sth,env,ix,rsc,ithm,abthm,_,_) dp mf =  
    let 
	val _ = DMSG (ST  "mk_rv_spec_thm\n") (dbgmc)(*DBG*)
	(*val _ = DMSG (TM  ie) (dbgmc)	val _ = DMSG (ST  " ie \n") (dbgmc)(*DBG*)*)
	val bv = snd(dest_comb mf)
	(*val _ = DMSG (TM  bv) (dbgmc) val _ = DMSG (ST  " bv \n") (dbgmc)(*DBG*)*)
	val v = fromHOLstring(bv) 
	(*val _ = DMSG (TH  msr) (dbgmc) val _ = DMSG (ST  "msr\n") (dbgmc)(*DBG*)
	val _ = if (Option.isSome sth) then DMSG (TH  (Option.valOf sth)) (dbgmc) else DMSG (ST  " NONE") (dbgmc)  
	val _ = DMSG (ST  "\nsth\n") (dbgmc)(*DBG*)
	val _ = DMSG (TM  ie) (dbgmc) val _ = DMSG (ST  " ie\n") (dbgmc)(*DBG*)
        val _ = List.app (fn th => let val _ = DMSG (TH  th) (dbgmc) val _ = DMSG (ST  "seth\n") (dbgmc) in () end)(*DBG*)
			 ((List.map snd (Binarymap.listItems(Binarymap.find(seth,v))))@[ENV_UPDATE_def,BETA_THM])(*DBG*)*)
	val th =  if (Int.compare(ix,dp)=EQUAL andalso (Vector.sub(rsc,ix)>0)) (*i.e.current bound var top level fv filt by >0 test*)
		  then (* this has already been proved in FixExp *) 
		      Option.valOf sth
		  else (* otherwise not innermost bound var so must account for change in environment *)
		      let 
			  (*val _ = DMSG (ST  "else\n") (dbgmc) val _ = DMSG (TH  (ISPECL [ie,fromMLstring v] msr)) (dbgmc) 
                            val _ = DMSG (ST  " msr1\n") (dbgmc)(*DBG*)
			    val _ = List.app (fn th => let val _ = DMSG (TH  th) (dbgmc) 
                            val _ = DMSG (ST  " seths\n") (dbgmc) in () end)(*DBG*)
			      (List.map snd (Binarymap.listItems(Binarymap.find(seth,v))))(*DBG*)
			    val _ = DMSG (TH  (eval_env ie ie bv seth [])) (dbgmc)(*DBG*)
			    val _ = DMSG (ST  " env_eval thm\n") (dbgmc)(*DBG*)*)
		      in SYM (CONV_RULE (RHS_CONV (PURE_ONCE_REWRITE_CONV [eval_env ie ie bv seth []])) (ISPECL [ie,bv] msr)) end
	(*val _ = DMSG (TH  th) (dbgmc) val _ = DMSG (ST  "rv spec thm\n") (dbgmc)(*DBG*)*)
	val _ = DMSG (ST  "mk_rv_spec_thm done\n") (dbgmc)
    in th end

(* in case an mf is an RV, getting the spec thm is more than just SPEC'ing the gth with the ie *)
fun get_spec_thm ie spec_func gth mf = 
    let 
	val _ = DMSG (ST  " get_spec_thm\n") (dbgmc)(*DBG*)
	(*val _ = DMSG (TH  gth) (dbgmc) val _ = DMSG (ST  " gth\n") (dbgmc)(*DBG*)*)    
    in if is_RV mf (* RV case *)
       then spec_func mf (* this calls mk_rv_spec_thm *)
       else let 
               (*val _ = DMSG (ST  "not RV \n") (dbgmc) val _ = DMSG (ST _type (type_of ie)) (dbgmc) 
                 val _ = DMSG (ST  " ie type\n") (dbgmc)(*DBG*)	
                 val _ = (with_flag (show_types,true) DMSG (TH  gth) (dbgmc) val _ = DMSG (ST  " gth with type\n") (dbgmc)(*DBG*)*)
	    in SPEC ie gth end
    end

(* dummy theorem not used by FixExp *) 
(* we don't just put TRUTH here because a gen thm needs to be SPEC'able *)
fun mk_fp_gen_thm state mf = INST_TYPE [``:'a`` |-> type_of state] ENV_UPDATE_INV 

fun get_cache_entry mf (muAP cch) = !cch
|   get_cache_entry mf (muRV cch) = !cch
|   get_cache_entry mf (muAnd(cch,_)) = !cch 			
|   get_cache_entry mf (muOr(cch,_)) = !cch 			
|   get_cache_entry mf (muNot(cch,_)) = !cch 			
|   get_cache_entry mf (muTR cch) = !cch
|   get_cache_entry mf (muFL cch) = !cch
|   get_cache_entry mf (muDIAMOND(cch,_)) = !cch 			
|   get_cache_entry mf (muBOX(cch,_)) = !cch 			
|   get_cache_entry mf (fpmu(_,cch,_)) = !cch 			
|   get_cache_entry mf (fpnu(_,cch,_)) = !cch

fun mk_spec_inv_thm githm nodes ie0 ie1 mf seth = 
    let 
	val _ = DMSG (ST  " mk_spec_inv_thm\n") (dbgmc)(*DBG*)	
	val (opr,args) = HolKernel.strip_comb mf	    
	val _ = DMSG (TM  mf) (dbgmc) val _ = DMSG (ST  " mf\n") (dbgmc)(*DBG*)	
        val _ = DMSG (TM  ie0) (dbgmc) val _ = DMSG (ST  " ie0\n") (dbgmc)(*DBG*)	
	val _ = DMSG (TM  ie1) (dbgmc) val _ = DMSG (ST  " ie1\n") (dbgmc)(*DBG*)	
	val _ = DMSG (TH  githm) (dbgmc) val _ = DMSG (ST  " githm\n") (dbgmc)(*DBG*)	
	val res = 
	    case (fst (dest_const opr)) of
		"AP"      => ISPECL [ie0,ie1] githm
	      | "RV"      => let val Hv = List.hd args
				 val v = fromHOLstring Hv
			     val _ = DMSG (TM  ``^ie0 ^Hv = ^ie1 ^Hv``) (dbgmc) val _ = DMSG (ST  " spec_inv goal\n") (dbgmc)(*DBG*)
		             val ethm = prove(``^ie0 ^Hv = ^ie1 ^Hv``, 
					      SIMP_TAC std_ss 
					      ([ENV_UPDATE_def]@
					       (List.map snd (Binarymap.listItems(Binarymap.find(seth,v))))))
			     val _ = DMSG (TH  ethm) (dbgmc) val _ = DMSG (ST  " ethm\n") (dbgmc)(*DBG*)
			     in MATCH_MP (ISPECL [ie0,ie1] githm) ethm end
	      | "And"     => ISPECL [ie0,ie1] githm
	      | "Or"      => ISPECL [ie0,ie1] githm
	      | "Not"     => ISPECL [ie0,ie1] githm
	      | "TR"      => ISPECL [ie0,ie1] githm
	      | "FL"      => ISPECL [ie0,ie1] githm
	      | "DIAMOND" => ISPECL [ie0,ie1] githm
	      | "BOX"     => ISPECL [ie0,ie1] githm
	      | "mu"      => ISPECL [ie0,ie1] githm
	      | "nu"      => ISPECL [ie0,ie1] githm
	      | _         => Raise Match
	val _ = DMSG (TH  res) (dbgmc) val _ = DMSG (ST  " mk_spec_inv_thm res\n") (dbgmc)(*DBG*)
	val _ = DMSG (ST  " mk_spec_inv_thm done\n") (dbgmc)(*DBG*)	
    in res end

(* goal is a conjunction of equalities of the form ie0 Q = ie1 Q TODO:speed this up*)
fun mk_se_thm goal seth = 
    let 
	val _ = DMSG (ST  "mk_se_thm\n") (dbgmc)(*DBG*)
	val _ = DMSG (TM  goal) (dbgmc) val _ = DMSG (ST  " goal\n") (dbgmc)(*DBG*)
	val sel = (List.map snd (List.concat (List.map snd (Binarymap.listItems (Binarymap.map (Binarymap.listItems o snd) seth)))))
	val _ = List.app (fn th => let val _ = DMSG (TH  th) (dbgmc) val _ = DMSG (ST  " cache seth\n") (dbgmc) in () end) sel(*DBG*)
	val res = prove(goal,SIMP_TAC std_ss (ENV_UPDATE_def::sel))  
	val _ = DMSG (ST  "mk_se_thm done\n") (dbgmc)(*DBG*)	
    in res end

(* retrieve term_bdd from cache. if missing use callbacks to create it and update cache *) 
fun cache_get cch ie tb_func gth_func dp nodes mf seth state =
    let val (tb,gth,sth,env,ix,rsc,ithm,abthm,ado_subthm,ado_eqthm) = !cch
	val _ = DMSG (ST  "(cache_get)\n") (dbgmc)(*DBG*)	
	val _ = DMSG (TM  mf) (dbgmc)  val _ = DMSG (ST  " mf\n") (dbgmc)(*DBG*)
	val _ = DMSG (ST (Int.toString dp)) (dbgmc) val _ = DMSG (ST  " dp\n") (dbgmc)(*DBG*)
        val _ = DMSG (ST (Int.toString ix)) (dbgmc) val _ = DMSG (ST  " ix\n") (dbgmc)(*DBG*)
	val _ = if (dbgmc) then let val _ = print_rsc rsc "" in () end else () 
	val _ = DMSG (ST  (Int.toString(Vector.length rsc))) (dbgmc) 
	val _ = DMSG (ST  " rsc length\n") (dbgmc)(*DBG*)
        fun check_rv rsc dp = if (dp=(~1)) then true else if (Vector.sub(rsc,dp)=0) then check_rv rsc (dp-1) else false
	(*val _ = with_flag (show_types,true) DMSG (TM  ie) (dbgmc) val _ = DMSG (ST  " ie\n") (dbgmc)(*DBG*)
	val _ = with_flag (show_types,true) DMSG (TM  env) (dbgmc) val _ = DMSG (ST  " env\n") (dbgmc)(*DBG*)*)
    in if (Term.compare(env,ie)=EQUAL) 
       then 
	   if (Option.isSome tb) 
	   then Option.valOf tb
	   else 
	       if (Option.isSome sth) 
	       then let val tb = tb_func mf (Option.valOf sth)
			val _ = upd_cch_tb cch tb 
		    in tb end
	       else 
		   if (Option.isSome gth) 
		   then let 
			    val _ = DMSG (ST  "gth SOME\n") (dbgmc)(*DBG*)
			    (*val _ = with_flag(show_types,true) DMSG (TH  (Option.valOf gth)) (dbgmc) (*DBG*)
                              val _ = DMSG (ST  " gth\n") (dbgmc)(*DBG*)*)
			    val sth = get_spec_thm ie gth_func (Option.valOf gth) mf (* could be an RV *)
			    val tb = tb_func mf sth
			    val _ = upd_cch_tb cch tb val _ = upd_cch_sth cch sth
			in tb end			    
		   else let 
			    val _ = DMSG (TM  mf) (dbgmc) val _ = DMSG (ST  "gth NONE\n") (dbgmc)(*DBG*)
			    val gth = gth_func mf (* can't be an RV because we stuffed its gth with TRUTH *)
			    (*val _ = with_flag(show_types,true) DMSG (TH  gth) (dbgmc) val _ = DMSG (ST  " gth\n") (dbgmc) *)(*DBG*)
			    val sth = ISPEC ie gth
			    (*val _ = DMSG (TH  sth) (dbgmc) val _ = DMSG (ST  " sth22\n") (dbgmc)(*DBG*)*)
			    val tb = tb_func mf sth
			    val _ = upd_cch_tb cch tb val _ = upd_cch_sth cch sth val _ = upd_cch_gth cch gth 
			in tb end			  
       else 
	   if (Option.isSome tb andalso (check_rv rsc dp)) 
	   then (* above check prevents dirty read i.e. only if no subformula contains a currently bound RV *)
	       if (Option.isSome gth) 
	       then let 
			val _ = DMSG (ST  " cached\n") (dbgmc)(*DBG*)
			(*val _ = DMSG (TM (getTerm (Option.valOf tb))) (dbgmc)(*DBG*)
			val _ = DMSG (ST  " cached tb\n") (dbgmc)(*DBG*)
			val _ = if (dbgmc) then let val _ = print _rsc rsc "cached tb" in () end else () (*DBG*)*)
			val sth1 = get_spec_thm ie gth_func (Option.valOf gth) mf (* could be an RV *)
			val sth0 = Option.valOf sth
			(*val _ = DMSG (TH  sth0) (dbgmc) val _ = DMSG (ST  " sth0\n") (dbgmc)(*DBG*)*)
			val sithm = mk_spec_inv_thm ithm nodes env ie mf seth
			(*val _ = DMSG (TH (sithm)) (dbgmc) val _ = DMSG (ST  "sithm0\n") (dbgmc)(*DBG*)*)
			val sithm = if (is_imp(concl sithm))
				    then MATCH_MP sithm (mk_se_thm (fst(dest_imp(concl sithm))) seth)
				    else sithm
			(*val _ = DMSG (TH (sithm)) (dbgmc) val _ = DMSG (ST  "sithm1\n") (dbgmc)(*DBG*)*)
			val sithm = AP_THM sithm state
			(*val _ = DMSG (TH (sithm)) (dbgmc) val _ = DMSG (ST  "sithm2\n") (dbgmc)(*DBG*)*)
			val tb = BddEqMp sithm (Option.valOf tb)
			val _ = DMSG (ST  " tb cache read done\n") (dbgmc)
			val _ = upd_cch_tb cch tb val _ = upd_cch_sth cch sth1 val _ = upd_cch_env cch ie
		    in tb end			    
	       else failwith("Internal error: cache_get: Cache has term_bdd but no gen thm")
	   else (* otherwise we have to recompute this tb (no clean subformula  will be recomputed) *) 
	       if (Option.isSome gth) 
	       then let val _ = DMSG (ST  " recompute SOME gth\n") (dbgmc)(*DBG*)
			val sth = get_spec_thm ie gth_func (Option.valOf gth) mf (* could be an RV *)
			val tb = tb_func mf sth
			val _ = upd_cch_tb cch tb val _ = upd_cch_sth cch sth val _ = upd_cch_env cch ie
		    in tb end			    
	       else let val _ = DMSG (ST  " recompute NONE gth\n") (dbgmc)(*DBG*)
			val gth = gth_func mf 
			val sth = if (is_RV mf) then gth else ISPEC ie gth 
			(*val _ = with_flag(show_types,true) DMSG (TH  gth) (dbgmc) val _ = DMSG (ST  " gth\n") (dbgmc)(*DBG*) *)
			val tb = tb_func mf sth
			val _ = upd_cch_tb cch tb val _ = upd_cch_sth cch sth val _ = upd_cch_gth cch gth val _ = upd_cch_env cch ie 
		    in tb end			  
    end
		   
fun get_abthms mf f1 f2 cch = 
    let (*FIXME: don't do the extra work if f1 and f2 are the same *)
	val abthm = #8(!cch)    
	val abthm = Option.valOf abthm
	val abthnm = lhs(concl abthm)  
	val mf1 = List.hd(snd(strip_comb mf))
	val mf2 = List.last(snd(strip_comb mf))
	val cab1 = #8(get_cache_entry mf1 f1)
	val cab2 = #8(get_cache_entry mf2 f2) 
	val cab1 = Option.valOf cab1
	val cab1nm = lhs(concl cab1) 
	val cab2 = Option.valOf cab2
	val cab2nm = lhs(concl cab2)
    in (abthm,abthnm,mf1,mf2,cab1,cab1nm,cab2,cab2nm) end

fun muCheck_aux ((_,(msa,absf,ksname),_,_,_),(seth,state,ie)) mf vm dp (muAP cch) = 
    let 
	val _ = (cntap := (!cntap)+1)(*PRF*)
	val tm1 = Time.toReal(Timer.checkRealTimer (!mtmr))(*PRF*)
	val tb = cache_get cch ie (mk_ap_tb vm absf) (mk_gen_ap_thm ksname state msa) dp [] mf seth state
	val _ = (tmap := (!tmap)+((Time.toReal(Timer.checkRealTimer (!mtmr)))-tm1))(*PRF*)
    in tb end 
  | muCheck_aux ((_,_,(msr,_,msreq,ee),_,_),(seth,state,ie)) mf vm dp (muRV cch) =  
    let 
	val _ = (cntrv := (!cntrv)+1)(*PRF*) 
	val tm1 = Time.toReal(Timer.checkRealTimer (!mtmr))(*PRF*)
	val tb = cache_get cch ie (mk_rv_tb ee (!cch)) (mk_rv_spec_thm msr seth msreq ie ee (!cch) dp) dp [] mf seth state
	val _ = (tmrv := (!tmrv)+((Time.toReal(Timer.checkRealTimer (!mtmr)))-tm1))(*PRF*)
    in tb end
  | muCheck_aux (args as (msp,_,_,_,_),(seth,state,ie)) mf vm dp (muAnd(cch,(f1,f2))) = 
    let 
	val _ = (cntcj := (!cntcj)+1)(*PRF*)
	val (abthm,abthnm,mf1,mf2,cab1,cab1nm,cab2,cab2nm) = get_abthms mf f1 f2 cch
	val tb = cache_get cch ie (BinExp (args,(seth,state,ie)) bdd.And (snd(strip_comb(mf))) vm (f1,f2) dp abthm)
	    (fn mf => GEN ``e:^(ty_antiq(type_of ie))`` 
	     (ISPECL [``e:^(ty_antiq(type_of ie))``,cab1nm,cab2nm] 
	      (List.nth(msp,3)))) dp [f1,f2] mf seth state
    in  tb end
  | muCheck_aux (args as (msp,_,_,_,_),(seth,state,ie)) mf vm dp (muOr(cch,(f1,f2))) = 
    let 
	val _ = (cntdj := (!cntdj)+1)(*PRF*)
	val (abthm,abthnm,mf1,mf2,cab1,cab1nm,cab2,cab2nm) = get_abthms mf f1 f2 cch
	val tb = cache_get cch ie (BinExp (args,(seth,state,ie)) bdd.Or (snd(strip_comb(mf))) vm (f1,f2) dp abthm)
	    (fn mf => GEN ``e:^(ty_antiq(type_of ie))`` 
	     (ISPECL [``e:^(ty_antiq(type_of ie))``,cab1nm,cab2nm] 
	      (List.nth(msp,4)))) dp [f1,f2] mf seth state
    in tb end
  | muCheck_aux (args as (msp,_,_,_,_),(seth,state,ie)) mf vm dp (muNot(cch,f1)) = 
    let 
	val tm1 = Time.toReal(Timer.checkRealTimer (!mtmr))(*PRF*)
	val (abthm,abthnm,mf1,_,cabthm,cabthmnm,_,_) = get_abthms mf f1 f1 cch
	val tb = cache_get cch ie (NotExp (args,(seth,state,ie)) mf1 vm dp f1 abthm) 
	    (fn mf => (ISPEC cabthmnm ((CONV_RULE SWAP_VARS_CONV) (List.nth(msp,2))))) dp [f1] mf seth state
	val _ = (tmng := (!tmng)+((Time.toReal(Timer.checkRealTimer (!mtmr)))-tm1))(*PRF*)
	val _ = (cntng := (!cntng)+1)(*PRF*)
    in tb end
  | muCheck_aux ((msp,_,_,_,_),(seth,state,ie)) mf vm dp (muTR cch) = 
	cache_get cch ie (mk_con_tb true vm) (fn mf => (List.nth(msp,0))) dp [] mf seth state
  | muCheck_aux ((msp,_,_,_,_),(seth,state,ie)) mf vm dp (muFL cch) = 
	cache_get cch ie (mk_con_tb false vm) (fn mf => (List.nth(msp,1))) dp [] mf seth state
  | muCheck_aux (args as (_,_,_,(_,Tth,(dmdth,_),_,_),_),(seth,state,ie)) mf vm dp (muDIAMOND(cch,(act,f1))) = 
     let 
	 val _ = (cntdm := (!cntdm)+1)(*PRF*) 
	 val (abthm,abthnm,_,_,cabthm,cabthmnm,_,_) = get_abthms mf f1 f1 cch
	 val tb = cache_get cch ie (ModalExp (args,(seth,state,ie)) act false (List.last(snd(strip_comb mf))) vm f1 dp abthm) 
	     (mk_gen_modal_thm Tth dmdth) dp [f1] mf seth state
     in  tb end 
  | muCheck_aux (args as (_,_,_,(_,Tth,(_,boxth),_,_),_),(seth,state,ie)) mf vm dp (muBOX(cch,(act,f1))) = 
     let val _ = (cntbx := (!cntbx)+1)(*PRF*) 
	 val (abthm,abthnm,_,_,cabthm,cabthmnm,_,_) = get_abthms mf f1 f1 cch
	 val tb = cache_get cch ie (ModalExp (args,(seth,state,ie)) act true (List.last(snd(strip_comb mf))) vm f1 dp abthm) 
	     (mk_gen_modal_thm Tth boxth) dp [f1] mf seth state
     in tb end  
  | muCheck_aux (args,(seth,state,ie)) mf vm dp (fpmu(bvch,cch,f1)) = 
    let 
	val _ = (cntmu := (!cntmu)+1)(*PRF*) 
	val rvnm = List.hd(snd(strip_comb mf))
	val (abthm,abthnm,mf1,_,cabthm,cabthmnm,_,_) = get_abthms mf f1 f1 cch
	val tb = cache_get cch ie (FixExp (args,(seth,state,ie)) [rvnm,cabthmnm] (BddCon false vm) vm (bvch,cch,f1) (dp+1) abthm cabthm)
	    (mk_fp_gen_thm state) dp [f1] mf seth state
    in tb end
  | muCheck_aux (args,(seth,state,ie)) mf vm dp (fpnu(bvch,cch,f1)) = 
    let 
	val _ = (cntmu := (!cntmu)+1)(*PRF*)
	val rvnm = List.hd(snd(strip_comb mf))
	val (abthm,abthnm,mf1,_,cabthm,cabthmnm,_,_) = get_abthms mf f1 f1 cch
	val tb = cache_get cch ie (FixExp (args,(seth,state,ie)) [rvnm,cabthmnm] (BddCon true vm) vm (bvch,cch,f1) (dp+1) abthm cabthm) 
	    (mk_fp_gen_thm state) dp [f1] mf seth state
    in tb end

and NotExp (args,(seth,state,ie)) mf1 vm dp f1 abthm mf sth = 
    let 
	val _ = DMSG (ST  " NotExp\n") (dbgmc)(*DBG*)
	val tb = BddNot (muCheck_aux (args,(seth,state,ie)) mf1 vm dp f1)
	(*val _ = DMSG (TM (getTerm tb)) (dbgmc) val _ = DMSG (ST  " NotExp tb\n") (dbgmc) 
          val _ = DMSG (TH  sth) (dbgmc) val _ = DMSG (ST  " NotExp sth\n") (dbgmc)(*DBG*)*)
	val sth = PURE_REWRITE_RULE [SYM abthm] sth 
	(*val _ = DMSG (TH  sth) (dbgmc) val _ = DMSG (ST  " NotExp sth abbrev\n") (dbgmc)(*DBG*)*)
	val tb2 = BddEqMp sth tb
	val _ = DMSG (ST  " NotExp end\n") (dbgmc)(*DBG*)
    in tb2 end
 
and BinExp (args,(seth,state,ie)) opr [t1,t2] vm (f1,f2) dp abthm mf opthm =
    let 
	val _ = DMSG (ST ("BinExp\n")) (dbgmc)(*DBG*)
	(*val _ = DMSG (TM  t1) (dbgmc)	val _ = DMSG (ST ("b1\n")) (dbgmc)(*DBG*)*)
	val b1 = muCheck_aux (args,(seth,state,ie)) t1 vm dp f1 
	(*val _ = DMSG (TM  t2) (dbgmc)	val _ = DMSG (ST ("b2\n")) (dbgmc)(*DBG*)*)
        val b2 = muCheck_aux (args,(seth,state,ie)) t2 vm dp f2 
	val tm1 = Time.toReal(Timer.checkRealTimer (!mtmr))(*PRF*)
	(*val _ = DMSG (ST ("bop\n")) (dbgmc)(*DBG*)*)
        val bb = BddOp(opr,b1,b2)
        val _ = (tmbobb := (!tmbobb)+((Time.toReal(Timer.checkRealTimer (!mtmr)))-tm1))(*PRF*)
	val tm2 = Time.toReal(Timer.checkRealTimer (!mtmr))(*PRF*)
        val _ = (tmboth := (!tmboth)+((Time.toReal(Timer.checkRealTimer (!mtmr)))-tm2))(*PRF*)
        val tm3 = Time.toReal(Timer.checkRealTimer (!mtmr))(*PRF*)
	(*val _ = DMSG (TM  (getTerm bb)) (dbgmc) val _ = DMSG (ST  " BinExp bb\n") (dbgmc) 
          val _ = DMSG (TH  opthm) (dbgmc) val _ = DMSG (ST  " BinExp opthm\n") (dbgmc)(*DBG*)*)
	val opthm = PURE_REWRITE_RULE [SYM abthm] opthm
	(*val _ = DMSG (TH  opthm ) (dbgmc)val _ = DMSG (ST  " BinExp opthm abbrev\n") (dbgmc)(*DBG*) *)
	val tb =BddEqMp opthm bb
	val _ = DMSG (ST ("BinExp end\n")) (dbgmc) (*DBG*)
        val _ = (tmbobe := (!tmbobe)+((Time.toReal(Timer.checkRealTimer (!mtmr)))-tm3))(*PRF*)       
        val _ = if (opr=bdd.And) then (tmcj := (!tmcj)+((Time.toReal(Timer.checkRealTimer (!mtmr)))-tm1))(*PRF*)       
		else  (tmdj := (!tmdj)+((Time.toReal(Timer.checkRealTimer (!mtmr)))-tm1))(*PRF*)
    in tb end
  | BinExp _ _ _ _ _ _ _ _ _ = Raise Match (* impossible, just here to avoid warning *)

and ModalExp (args as (_,_,_,(RTm,_,_,sp,s2sp),_),(seth,state,ie))  actnm isbox t2 vm f1 dp abthm mf sth = 
    let 
	val _ = DMSG (ST ("ModalExp\n")) (dbgmc)(*DBG*)
	val tb1 = muCheck_aux (args,(seth,state,ie)) t2 vm dp f1
	val tm1 = Time.toReal(Timer.checkRealTimer (!mtmr))(*PRF*)
        val tb2 = if isbox then BddAppall sp (bdd.Imp, find(RTm,actnm),(BddReplace  s2sp tb1))
		  else BddAppex sp (bdd.And, find(RTm,actnm),(BddReplace  s2sp tb1))
	val sth = SPEC (hd(snd(strip_comb(getTerm(tb1))))) sth (* TODO: move this to muCheck_aux to be consistent with ~,/\,\/ etc*)
	(*val _ = DMSG (TH  sth) (dbgmc)	val _ = DMSG (ST  " ModalExp sth\n") (dbgmc)(*DBG*)*)
	val sth = PURE_REWRITE_RULE [SYM abthm] sth
	(*val _ = DMSG (TH  sth) (dbgmc)	val _ = DMSG (ST  " ModalExp sth abbrev\n") (dbgmc) 
          val _ = DMSG (TM  (getTerm tb2)) (dbgmc) val _ = DMSG (ST  " tb2\n") (dbgmc)(*DBG*)*)
	val ttb = BddEqMp (SYM sth) tb2  
        val _ = (tmdm := (!tmdm)+((Time.toReal(Timer.checkRealTimer (!mtmr)))-tm1))(*PRF*)
	val _ = DMSG (ST ("ModalExp end\n")) (dbgmc)(*DBG*)
    in ttb end

and FixExp ((p_,ap_,rv_,d_,
	     (wfKS_ks,finS,frv_thms,imf_thms,pextth,rvtt,mssth,fps,eus,Ss,ess,statel,ksname,prop_type,ee,qd,sqd,ce,qt,eeq)),
	    (seth,state,ie)) [t1,t2] initbdd vm (bvch,_,f1) dp abthm cabthm mf _ =
    let (*FIXME: clean up this monster *)
	val _ = DMSG (ST  " FixExp\n") (dbgmc)(*DBG*)
	val _ = DMSG (TM  t2) (dbgmc) val _ = DMSG (ST  " t2\n") (dbgmc)(*DBG*)
	val tmr5 = Timer.startRealTimer()(*PRF*)
        val tmrr1 = Time.toReal(Timer.checkRealTimer (!mtmr))(*PRF*)
	(* note that the binding occurance uses same cache node as the occurances of the bv in the formula *)	
	val (bvtb,bvgth,bvsth,bvenv,bvix,bvrsc,bvithm,bvabthm,ado_subthm,ado_eqthm) = !bvch
	val bv = (fromHOLstring(t1))
        val (ttm,initset,imf_t2g,init_thm,abbrev_thm,fp2thm,adogeneqthm,bigthm,chainth,initsubth) = 
	    if (bdd.equal (getBdd(initbdd)) (bdd.TRUE)) 
		then (true,Ss,list_mk_comb(``$nu:(^(ty_antiq(list_mk_fun([``:string``,type_of t2],type_of t2))))``,
					   [t1,List.last (snd(strip_comb mf))]),GFP_INIT,NU_FP_STATES,
		      STATES_FP_BIGINTER_2,STATES_DEF_SYM_NU,NU_BIGINTER,GEN_GFP_CHAIN,
		      REWRITE_RULE [SYM (List.last (CONJUNCTS (REWRITE_RULE [wfKS_def] wfKS_ks)))] 
		      (INST_TYPE [alpha|->type_of state] SUBSET_UNIV))  
            else (false,ess,list_mk_comb(``$mu:(^(ty_antiq(list_mk_fun([``:string``,type_of t2],type_of t2))))``,
					 [t1,List.last (snd(strip_comb mf))]),LFP_INIT,MU_FP_STATES,
		      STATES_FP_BIGUNION_2,STATES_DEF_SYM_MU,MU_BIGUNION,GEN_LFP_CHAIN,EMPTY_SUBSET)  
	val _ = DMSG (ST  (if ttm then "true" else "false")) (dbgmc) val _ = DMSG (ST  " ttm\n") (dbgmc)(*DBG*)
	val _ = DMSG (TM  ie) (dbgmc) val _ = DMSG (ST  " ie\n") (dbgmc)(*DBG*)
	(*  ado: max same_quant nesting depth is 2 and immediate outer bv (if any) has the same fp operator as this one, 
                 and the outer bv has not been just reset *)
	val ado = (sqd andalso (not (List.null qt)) andalso (ttm=List.hd qt)) 
		  andalso (not (Term.compare(numSyntax.zero_tm,List.last(snd(strip_comb(snd(dest_comb ie)))))=EQUAL)) 
	val _ = if ado then DMSG (ST  "ADO active\n") (dbgmc) else DMSG (ST  "no ADO\n") (dbgmc)(*DBG*)
	(* if ado then start from where we left off. ASSERT:ado==>Option.isSome bvtb *)
	val ((initset,initbdd),init_thm,abbrev_thm) = 
	    if (ado)  
		then let val bvt = getTerm(Option.valOf bvtb)
			 val _ = DMSG (TM  bvt) (dbgmc) val _ = DMSG (ST  " bvt\n") (dbgmc)(*DBG*)
			 val e = List.nth(snd(strip_comb bvt),2) (* bvt is a MU_SAT term, so e is prev outer env *)
			 val _ = DMSG (TM  e) (dbgmc) val _ = DMSG (ST  " e\n") (dbgmc)(*DBG*)
			 val X = get_env_val state t1 e
			 val _ = DMSG (TM  X) (dbgmc) val _ = DMSG (ST  " X\n") (dbgmc)(*DBG*)
			 val th = MP (ISPECL [ksname,fst(dest_env e),t1,state,X] GEN_MS_FP_INIT) wfKS_ks
		         val _ = DMSG (TH  th) (dbgmc) val _ = DMSG (ST  " initset MS_FP\n") (dbgmc)(*DBG*)
		     in ((X,BddEqMp th (Option.valOf bvtb)),GEN_FP_INIT,if (ttm) then GEN_NU_FP_STATES else GEN_MU_FP_STATES) end
	    else ((initset,initbdd),init_thm,abbrev_thm)
	val _ = DMSG (TM  initset) (dbgmc) val _ = DMSG (ST  " initset\n") (dbgmc) (*DBG*)
        val _ = DMSG (TM  (getTerm(initbdd))) (dbgmc) val _ = DMSG (ST  " initbdd\n") (dbgmc) (*DBG*)
	val _ = DMSG (TM  imf_t2g) (dbgmc) val _ = DMSG (ST  " imf_t2g\n") (dbgmc)(*DBG*)
	(* if ado then we need the old outer env for proving the env legal assumption to the endth *)
	val imf_t2 = Binarymap.find(imf_thms,imf_t2g)
	(*val _ = DMSG (TH  imf_t2) (dbgmc) val _ = DMSG (ST  " imf_t2\n") (dbgmc)(*DBG*)
	val _ = if not ado then let val _ = DMSG (TH  abbrev_thm) (dbgmc) val _ = DMSG (ST  " abbrev_thm\n") (dbgmc) in () end (*DBG*)
		else let val _ = DMSG (TH  abbrev_thm) (dbgmc) val _ = DMSG (ST  " ADO abbrev_thm\n") (dbgmc) in () end(*DBG*)*)
        (* make a term representing the modified environment *)
        val ie1 = list_mk_comb(eus,[ie,t1,initset])
        fun mk_fp n = mk_comb(list_mk_comb(fps,[t2,t1,ksname,ie1]),n)
        val ie2 = list_mk_comb(eus,[ie,t1,mk_fp numSyntax.zero_tm])
        (* create a new RV theorem for this bound var and add it to the spec thms, and add the bv's initbdd to the env *)
        val new_rv_thm = SYM (MP (ISPECL [t2,ksname,ie,t1,state,initset,numSyntax.zero_tm] MS_FP_INIT) wfKS_ks)
	(*val _ = DMSG (TH  new_rv_thm) (dbgmc) val _ = DMSG (ST  " new_rv_thm\n") (dbgmc)(*DBG*)*)
        val _ = upd_cch_sth bvch new_rv_thm
        val ix = (Array.length ee) - qd  (* index of current bv in ee and rv_thms arrays *)
	val _ = 
	    if (ado) 
		then Array.update(ee,ix,(bv,BddEqMp (SYM(MP (ISPECL [t2,ksname,ie,t1,initset,state] init_thm) wfKS_ks)) initbdd))
	    else Array.update(ee,ix,(bv,BddEqMp (SYM(MP (ISPECL [t2,ksname,ie,t1,state] init_thm) wfKS_ks)) initbdd))
	val ado_subthm' = if sqd then SOME (lift_ado_sub_thm ado ado_subthm t2 ksname ie1 eeq imf_thms abthm
	    wfKS_ks ie t1 initset seth imf_t2 ess Ss eus adogeneqthm initsubth numSyntax.zero_tm) else NONE
        val _ = (tmfpoh := (!tmfpoh)+((Time.toReal(Timer.checkRealTimer (!mtmr)))-tmrr1))(*PRF*)
        val _ = if (not ttm) then (tmmu := (!tmmu)+((Time.toReal(Timer.checkRealTimer (!mtmr)))-tmrr1))(*PRF*)
		else (tmnu := (!tmnu)+((Time.toReal(Timer.checkRealTimer (!mtmr)))-tmrr1))(*PRF*)
        val _ = DMSG (ST (Time.toString(Timer.checkRealTimer tmr5))) (dbgmc) val _ = DMSG (ST (" (FixExp OVERHEAD)\n")) (dbgmc)(*PRF*)
        fun iter ie2 n = (* ee also changes with each iter, but statefully, so no need to pass it in *) 
          let val _ = DMSG (ST  ("(iter)\n")) (dbgmc)(*DBG*)
	      val _ = DMSG (TM  t2) (dbgmc) val _ = DMSG (ST  "::") (dbgmc) val _ = DMSG (TM  n) (dbgmc)(*DBG*)
	      val _ = DMSG (TM  ie2) (dbgmc) val _ = DMSG (ST  " ie2\n") (dbgmc)(*DBG*)
	      val tmr = Timer.startRealTimer()(*PRF*)
              val tmr2 = Timer.startRealTimer()(*PRF*)
	      val eeqthm  = if sqd then mk_ado_pre_sub_thm ado ado_subthm t2 ksname ie1 eeq imf_thms abthm wfKS_ks ie t1 
		  initset seth imf_t2 ess eus chainth adogeneqthm initsubth
		  (if  (Term.compare(n,numSyntax.zero_tm)=EQUAL) then n else rand n)  else TRUTH
	      val _ = DMSG (TH  eeqthm) (dbgmc) val _ = DMSG (ST  " eeqthm\n") (dbgmc)(*DBG*)
	      val itr = (muCheck_aux ((p_,ap_,rv_,d_,(wfKS_ks,finS,frv_thms,imf_thms,pextth,rvtt,mssth,fps,eus,Ss,ess,statel,
							   ksname,prop_type,ee,qd-1,sqd,ce,ttm::qt,(eeqthm,abthm)::eeq)),
					   (seth,state,ie2)) (List.last (snd(strip_comb mf)))  vm dp f1)
	      val itrtm = getTerm itr
	      val _ = DMSG (TM  itrtm) (dbgmc) val _ = DMSG (ST  " (itr)\n") (dbgmc)(*DBG*)
	      val _ = DMSG (ST  "::") (dbgmc) val _ = DMSG (TM  n) (dbgmc)(*DBG*)
	      val itrthm = (ISPECL [t2,ksname,ie,t1,state,initset,n] MS_FP)
              val _ = DMSG (TH  itrthm) (dbgmc) val _ = DMSG (ST  " itr thm\n") (dbgmc)(*DBG*)
              val itr = BddEqMp itrthm itr
	      (* if counterexamples/witnesses are turned on, and we are in the outermost fixed point iteration *)
	      val _ = if (Option.isSome (!ce)) andalso ix=0 then ce := SOME (itr::(Option.valOf (!ce))) else ()
	      val _ = if (Option.isSome (!ce)) andalso ix=0 then (*DBG*)
	      let val _=DMSG (ST "CE len")(dbgmc) val _=DMSG(ST((int_to_string(List.length(Option.valOf (!ce))))^"\n"))(dbgmc)(*DBG*)
		  val _ = DMSG (BD (getBdd itr))(dbgmc)
			  in () end else ()(*DBG*)
	      val _ = DMSG (TM  (getTerm itr)) (dbgmc) val _ = DMSG (ST  " (itr 2)\n") (dbgmc)(*DBG*)
              val _ = DMSG (ST (Time.toString(Timer.checkRealTimer tmr2))) (dbgmc) val _ = DMSG (ST (" (call)\n")) (dbgmc)(*PRF*)
              val tmrr1 = Time.toReal(Timer.checkRealTimer (!mtmr))(*PRF*)
              val prevbdd = snd(Array.sub(ee,ix))
	      val _ = DMSG (BD (getBdd prevbdd)) (dbgmc)
	      val _ = DMSG (TM (getTerm prevbdd)) (dbgmc) val _ = DMSG (ST  " prevbdd\n") (dbgmc)(*DBG*)
          in let 
              val eqq = (bdd.equal (getBdd prevbdd) (getBdd itr)) 
	      val tttb = 
		  if eqq
		  then let 
			   val _ = DMSG (ST  " (iter fin calcs)\n") (dbgmc)(*DBG*)
			   val _ = (cntfpitfn:=(!cntfpitfn)+1)(*PRF*)
			   val tmrr3 = Time.toReal(Timer.checkRealTimer (!mtmr))(*PRF*)
			   val orac_th = REWRITE_RULE [pextth] (GENL statel (BddThmOracle (BddOp(bdd.Biimp,prevbdd,itr))))
			   val _ = DMSG (TH  orac_th) (dbgmc) val _ = DMSG (ST  "oracle thm\n") (dbgmc)(*DBG*)
			   val endth =  
			       if ado 
				   then let 
				            (*val _ = DMSG (TH  cabthm) (dbgmc) val _ = DMSG (ST  " ADO cabthm\n") (dbgmc)(*DBG*)
					    val _ = DMSG (TH  abthm) (dbgmc) val _ = DMSG (ST  " ADO abthm\n") (dbgmc)(*DBG*)*)
					    val imf_t2 = PURE_ONCE_REWRITE_RULE [abthm] imf_t2
					    (*val _ = DMSG (TH  imf_t2) (dbgmc) val _ = DMSG (ST  " ADO imf_t2\n") (dbgmc)(*DBG*)
					    val _ = DMSG(TH ado_subthm') (dbgmc) val _ = DMSG (ST  " ADO subthm'\n") (dbgmc)(*DBG*)
					    val _=DMSG(TH(Option.valOf ado_eqthm))(dbgmc) val _=DMSG(ST "ADO eqthm\n")(dbgmc)(*DBG*)*)
					    val ado_imfth = Binarymap.find(imf_thms,t2)
					    val adoeqthm2 = MATCH_MP SUBSET_TRANS 
						(LIST_CONJ [MATCH_MP EQ_IMP_SUBSET (Option.valOf ado_eqthm),
							    (SPEC (fst (dest_env ie)) 
							     (MATCH_MP fp2thm 
							      (LIST_CONJ [imf_t2,ado_imfth,
									  wfKS_ks,PURE_ONCE_REWRITE_RULE[adogeneqthm](fst(hd eeq))])))])
					    val _ = DMSG (TH  adoeqthm2) (dbgmc)  val _ = DMSG (ST  " ADO adoeqthm2\n") (dbgmc)(*DBG*)
					    val sabbrev_thm = ISPECL [t2,ksname,ie,n,t1,initset] abbrev_thm 
					    val _ = DMSG (TH sabbrev_thm) (dbgmc) val _= DMSG (ST " ADO sabbrev_thm\n") (dbgmc)(*DBG*)
					in PURE_ONCE_REWRITE_RULE [SYM abthm] 
					    (MP (MP sabbrev_thm (LIST_CONJ [wfKS_ks,imf_t2,finS,Option.valOf ado_subthm'])) adoeqthm2)
					end
			       else MP (PURE_REWRITE_RULE [SYM abthm] (ISPECL [t2,ksname,ie,n,t1] abbrev_thm))
						    (LIST_CONJ [wfKS_ks,imf_t2])
			   val _ = DMSG (TH  endth) (dbgmc) val _ = DMSG (ST  " endth\n") (dbgmc)(*DBG*)
			   val t2b = (SYM (PURE_ONCE_REWRITE_RULE [mssth] 
					   (AP_THM (MATCH_MP endth orac_th) state))) (* FIXME: AP_THM very slow on big tuples *)
			   val _ = DMSG (TH  t2b) (dbgmc)  val _ = DMSG (ST  " t2b\n") (dbgmc)(*DBG*)
			   (* make ado eqthm and sub_thm for next round *)
			   val _ = if sqd then 
			       let val t2b' = (CONV_RULE (RHS_CONV (RATOR_CONV (PURE_ONCE_REWRITE_CONV [abthm]))) 
				       (PEXT (PairRules.PGEN state (BETA_RULE (REWRITE_RULE [IN_DEF,MU_SAT_def] t2b)))))
				   val _ = DMSG (TH  t2b') (dbgmc)  val _ = DMSG (ST  " t2b'\n") (dbgmc)(*DBG*)
				   val ado_eqthm' =  CONV_RULE(RHS_CONV(REWRITE_CONV[MP(ISPECL[t2,ksname,ie,t1] bigthm) wfKS_ks])) t2b'
				   (*val _ = DMSG (TH  ado_eqthm') (dbgmc)  val _ = DMSG (ST  " ado_eqthm'\n") (dbgmc)(*DBG*)*)
				   val _ = upd_cch_eqth bvch ado_eqthm' 
				   (* make ado subthm *)
				   val ado_subthm = mk_ado_sub_thm ado (Option.valOf ado_subthm') t2 ksname ie1 eeq 
				       imf_thms abthm wfKS_ks ie t1 initset (rator (getTerm prevbdd)) seth imf_t2 ess eus chainth n  
				   val _ = upd_cch_subth bvch ado_subthm 
			       in () end else ()
			   val _ = (tmfpitfn := (!tmfpitfn)+((Time.toReal(Timer.checkRealTimer (!mtmr)))-tmrr3))(*PRF*)
			   val _ = (tmfpit := (!tmfpit)+((Time.toReal(Timer.checkRealTimer (!mtmr)))-tmrr1))(*PRF*) 	
			   (*val _ = DMSG (ST  bv) (dbgmc)(*DBG*)*)
			   val _ = DMSG (ST  " (iter fin done)\n") (dbgmc)(*DBG*)
		       in BddEqMp t2b prevbdd end
		  else let 
			   val _ = (cntfpitit:=(!cntfpitit)+1)(*PRF*)
			   val tmrr3 = Time.toReal(Timer.checkRealTimer (!mtmr))(*PRF*)
			   val ie3 = list_mk_comb(eus,[ie,t1,mk_fp(mk_comb(``SUC``,n))])
			   val _ = DMSG (TM  ie3) (dbgmc) val _ = DMSG (ST  " ie3\n") (dbgmc)(*DBG*)
			   val _ = Array.update(ee,ix,(bv,itr))
			   val rv_thm = SYM (SPECL [t2,ie,initset,t1,n] rvtt)
			   val _ = DMSG (TH  rv_thm) (dbgmc)  val _ = DMSG (ST  "fixexp rv_thm\n") (dbgmc)(*DBG*)
			   val _ = upd_cch_sth bvch rv_thm 
			   val _ = (tmfpitit := (!tmfpitit)+((Time.toReal(Timer.checkRealTimer (!mtmr)))-tmrr3))(*PRF*)
			   val _ = (tmfpit := (!tmfpit)+((Time.toReal(Timer.checkRealTimer (!mtmr)))-tmrr1))(*PRF*)
			   val _ = if (not ttm) then (tmmu := (!tmmu)+((Time.toReal(Timer.checkRealTimer (!mtmr)))-tmrr1))(*PRF*)
				   else (tmnu := (!tmnu)+((Time.toReal(Timer.checkRealTimer (!mtmr)))-tmrr1))(*PRF*)                  
			   val _ = DMSG (ST (Time.toString(Timer.checkRealTimer tmr))) (dbgmc)(*PRF*)
			   val _ = DMSG (ST (" (iter end)\n")) (dbgmc)(*DBG*)
		       in iter ie3 ``SUC ^n`` end              
             in tttb end
	  end        
    val fpres = iter ie2 numSyntax.zero_tm 
    val tmrr2 = Time.toReal(Timer.checkRealTimer (!mtmr))(*PRF*)
    val _ = (tmfpoh := (!tmfpoh)+((Time.toReal(Timer.checkRealTimer (!mtmr)))-tmrr2))(*PRF*)
    in fpres end
  | FixExp  _ _ _ _ _ _ _ _ _ _= Raise Match (* impossible, just here to avoid warning *)

(* init the model *)
fun init_model I1 T1 state vm Ric =
    let val (apl,ks_def,wfKS_ks,RTm) = mk_wfKS I1 T1 NONE state vm Ric NONE NONE NONE
    in (apl,ks_def,wfKS_ks,RTm) end

(* init model dependent data structures and theorems *)
fun init_thms (apl,ks_def,wfKS_ks) T1 state vm Ric absf = 
    let 
	val tmr = Timer.startRealTimer()
	val ksname = lhs(concl ks_def)
	val prop_ty = List.hd(snd(dest_type(type_of ksname)))
	val state' = mk_primed_state state
	val (st,st') = (strip_pair##strip_pair) (state,state')
        val s2s' = List.map (fn(v,v') => (BddVar true vm v,BddVar true vm v')) (ListPair.zip(st,st'))
	val (msp,msa,Tth,(dmdth,boxth),githms) = mk_gen_thms T1 (apl,ks_def,wfKS_ks) state state' st vm
        val st_ty = type_of state
	val f_ty = ``:^(prop_ty) mu``
	val env_ty = list_mk_fun([string_ty,st_ty],bool)
        val eus = ``ENV_UPDATE:^(ty_antiq(list_mk_fun([env_ty,string_ty,prop_ty],env_ty)))``
        val fps = ``FP:^(ty_antiq(list_mk_fun([f_ty,string_ty,type_of ksname,env_ty,``:num``,st_ty],bool)))``
	val Ss = mk_comb(``KS_S:^(ty_antiq(list_mk_fun([type_of ksname,st_ty],bool)))``,ksname)
	val ess = ``{}:^(ty_antiq(list_mk_fun([st_ty],bool)))``
        val mssth = GSYM (SIMP_RULE std_ss [IN_DEF] MU_SAT_def)
        val rvtt = GENL [``f:^(ty_antiq(f_ty))``,``e:^(ty_antiq(env_ty))``,
			 ``X:^(ty_antiq(prop_ty))``,``Q:string``,``n:num``] (ISPEC state (GENL [``s:^(ty_antiq(st_ty))``] 
			  (SPEC_ALL (MATCH_MP  (SIMP_RULE std_ss [MS_FP] (GEN_ALL (SIMP_RULE std_ss [ENV_UPDATE]  
				         (ISPECL [``f:(^(ty_antiq(f_ty)))``,``Q:string``,``ks:^(ty_antiq(type_of ksname))``,
						  ``e[[[Q<--X]]]:(^(ty_antiq(env_ty)))``] SAT_RV_ENV_SUBST)))) wfKS_ks))))
        val pextth = GSYM (CONV_RULE (STRIP_QUANT_CONV (RHS_CONV holCheckTools.ELIM_TUPLED_QUANT_CONV)) 
		    (REWRITE_RULE [(GEN_PALPHA_CONV state (rhs(concl(SPEC_ALL(INST_TYPE [alpha|->st_ty] FUN_EQ_THM)))))] 
			       (INST_TYPE [alpha |-> st_ty] FUN_EQ_THM)))
        val finS = prove(``FINITE (^ksname).S``,PROVE_TAC [wfKS_def,wfKS_ks,BOOLVEC_UNIV_FINITE_CONV (List.length st)])
        val _ = DMSG (ST (Time.toString(Timer.checkRealTimer tmr))) (dbgmc)(*PRF*) 
	val _ = DMSG (ST (" (overhead)\n")) (dbgmc)(*PRF*)
    in ((msp,(msa,absf,ksname), (Tth,(dmdth,boxth),st',s2s'),(finS,pextth,rvtt,mssth,fps,eus,Ss,ess,st,prop_ty)),state,githms)
    end

(* init data structures and theorems that depend on the property and environment *)
fun init_prop mf ee ksname state wfKS_ks vm githms msp prop_ty =
    let val mf = inst [alpha |-> prop_ty] mf (* it is possible that mf 's type var has not been instantiated *)
	val sqd = ((sameq_depth mf)=2) (* whether or not ado will be enabled at all *)
	val rvl = Array.foldr (fn((rv,tb),l)=> (rv,getTerm tb)::l) [] ee  
        val st_ty = type_of state
	val f_ty = ``:^(prop_ty) mu``
	val env_ty = list_mk_fun([string_ty,st_ty],bool)
	val ie =  if (List.null rvl) then (``EMPTY_ENV:^(ty_antiq(env_ty))``) else mk_env rvl state
	val (msr,seth,msreq) = mk_gen_rv_thms mf ksname state rvl ie wfKS_ks 
	val sel = (List.map snd (List.concat (List.map snd (Binarymap.listItems (Binarymap.map (Binarymap.listItems o snd) seth)))))
        val _ = prove (``IMF ^mf``,REWRITE_TAC ([IMF_def,MU_SUB_def,NNF_def,RVNEG_def]@(tsimps "mu")@sel))	
	    handle ex => failwith ("Bound variable occurs negatively:"^(term_to_string mf))
        val qd = qdepth mf
        val ee2 = Array.array((Array.length ee)+qd,("dummy",BddCon true vm))
	val _ = Array.copy {si=0,len=NONE,src=ee,dst=ee2,di=0}
	val tmr2 = Timer.startRealTimer()(*PRF*)
	val (mfml,imf_thms,frv_thms) = mk_cache ee ie mf mf qd githms state seth msp
	val _ = Binarymap.app (fn (k,v) => let val _ = DMSG (TM  k) (dbgmc) val _ = DMSG (ST  " key\n") (dbgmc) (*DBG*)
					       val _ = DMSG (TH  v) (dbgmc) val _ = DMSG (ST  " v\n") (dbgmc) (*DBG*)
                                             in () end) frv_thms val _ = DMSG (ST  " frv_thms\n") (dbgmc)(*DBG*)
	val imf_thms = mk_ado_imf_thms mf seth (tsimps "mu") frv_thms imf_thms
	val _ = Binarymap.app (fn (k,v) => let val _ = DMSG (TM  k) (dbgmc) val _ = DMSG (ST  " key\n") (dbgmc) (*DBG*)
					       val _ = DMSG (TH  v) (dbgmc) val _ = DMSG (ST  " v\n") (dbgmc) (*DBG*)
                                             in () end) imf_thms val _ = DMSG (ST  " imf_thms\n") (dbgmc)(*DBG*)
        val _ = DMSG (ST (Time.toString(Timer.checkRealTimer tmr2))) (dbgmc) (*PRF*)	
        val _ = DMSG (ST ("mk_cache done\n")) (dbgmc)(*DBG*)
in (ie,(msr,seth,msreq,ee2),mfml,imf_thms,frv_thms,qd,sqd) end

(* init data structures and theorems used by model checker *)
fun init I1 T1 state vm Ric ce mf ee absf (model_data,init_data) =
    let val (apl,ks_def,wfKS_ks,RTm) = if Option.isSome model_data then Option.valOf model_data 
				       else init_model I1 T1 state vm Ric 
	val _ = if Option.isSome init_data then DMSG (ST "isSome") (dbginit) else DMSG (ST "no init data") (dbginit)
	val ((msp,(msa,absf,ksname),(Tth,(dmdth,boxth),st',s2s'),
	      (finS,pextth,rvtt,mssth,fps,eus,Ss,ess,st,prop_ty)),state,githms) =
	if Option.isSome init_data then Option.valOf init_data else init_thms (apl,ks_def,wfKS_ks) T1 state vm Ric absf
	val (ie,(msr,seth,msreq,ee2),mfml,imf_thms,frv_thms,qd,sqd) = init_prop mf ee ksname state wfKS_ks vm githms msp prop_ty 
	val ce = if not (Option.isSome (!ce)) andalso is_existential mf 
		 then ref (SOME []) else ce (*turn on witness trace if existential mf*)
    in ((SOME (apl,ks_def,wfKS_ks,RTm),SOME ((msp,(msa,absf,ksname),(Tth,(dmdth,boxth),st',s2s'),
	      (finS,pextth,rvtt,mssth,fps,eus,Ss,ess,st,prop_ty)),state,githms)),
	(msp,
	 (msa,absf,ksname),
	 (msr,seth,msreq,ee2),
	 (RTm,Tth,(dmdth,boxth),st',s2s'),
	 (wfKS_ks,finS,frv_thms,imf_thms,pextth,rvtt,mssth,fps,eus,Ss,ess,st,ksname,prop_ty,ee2,qd,sqd,ce,[],[])),
	(ks_def,mf,seth,ie,mfml,frv_thms,ce))
    end

(* reset call counts and computation times *)(*PRF*)
fun reset_profile() = (*PRF*)
    let val _ =  cntap := 0 val _ = cntrv := 0 val _ = cntcj := 0 val _ = cntdj := 0 val _ = cntng := 0 val _ = cntdm := 0(*PRF*) 
	val _ =  cntbx := 0 val _ =  cntmu := 0 val _ =  cntnu := 0 val _ =  cntfpitfn := 0 val _ =  cntfpitit := 0(*PRF*)
        val _ =  tmap := 0.0 val _ = tmrv := 0.0 val _ = tmcj := 0.0 val _ = tmdj := 0.0 val _ = tmng := 0.0 val _ = tmdm := 0.0(*PRF*)
	val _ =  tmbx := 0.0 val _ =  tmmu := 0.0 val _ =  tmnu := 0.0(*PRF*)
        val _ =  tmbobb := 0.0 val _ =  tmboth := 0.0 val _ =  tmbobe := 0.0(*PRF*)
        val _ =  tmfpoh := 0.0 val _ =  tmfpit := 0.0 val _ =  tmfpitfn := 0.0 val _ =  tmfpitit := 0.0(*PRF*)
        val _ =  mtmr := (Timer.startRealTimer())(*PRF*)
in () end (*PRF*)

(* print  call counts and computation times for last run *)(*PRF*)
fun print _profile() = (*PRF*)
    let val _ = DMSG (ST ("cnt ap :")) (dbgmc) val _ = DMSG (ST (int_to_string(!cntap))) (dbgmc) 
	                                        val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("cnt rv :")) (dbgmc) val _ = DMSG (ST (int_to_string(!cntrv))) (dbgmc) 
						val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("cnt cj :")) (dbgmc) val _ = DMSG (ST (int_to_string(!cntcj))) (dbgmc) 
						val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("cnt dj :")) (dbgmc) val _ = DMSG (ST (int_to_string(!cntdj))) (dbgmc) 
						val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("cnt ng :")) (dbgmc) val _ = DMSG (ST (int_to_string(!cntng))) (dbgmc) 
						val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("cnt dm :")) (dbgmc) val _ = DMSG (ST (int_to_string(!cntdm))) (dbgmc) 
						val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("cnt bx :")) (dbgmc) val _ = DMSG (ST (int_to_string(!cntbx))) (dbgmc) 
						val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("cnt mu :")) (dbgmc) val _ = DMSG (ST (int_to_string(!cntmu))) (dbgmc) 
						val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("cnt nu :")) (dbgmc) val _ = DMSG (ST (int_to_string(!cntnu))) (dbgmc) 
						val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("cnt fp it fn :")) (dbgmc) val _ = DMSG (ST (int_to_string(!cntfpitfn))) (dbgmc) 
						      val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("cnt fp it it :")) (dbgmc) val _ = DMSG (ST (int_to_string(!cntfpitit))) (dbgmc) 
						      val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("tm ap :")) (dbgmc) val _ = DMSG (ST (Real.toString(!tmap))) (dbgmc) 
					       val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("tm rv :")) (dbgmc) val _ = DMSG (ST (Real.toString(!tmrv))) (dbgmc) 
					       val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("tm cj :")) (dbgmc) val _ = DMSG (ST (Real.toString(!tmcj))) (dbgmc) 
					       val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("tm dj :")) (dbgmc) val _ = DMSG (ST (Real.toString(!tmdj))) (dbgmc) 
					       val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("tm ng :")) (dbgmc) val _ = DMSG (ST (Real.toString(!tmng))) (dbgmc) 
					       val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("tm dm :")) (dbgmc) val _ = DMSG (ST (Real.toString(!tmdm))) (dbgmc) 
					       val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("tm bx :")) (dbgmc) val _ = DMSG (ST (Real.toString(!tmbx))) (dbgmc) 
					       val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("tm mu :")) (dbgmc) val _ = DMSG (ST (Real.toString(!tmmu))) (dbgmc) 
					       val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("tm nu :")) (dbgmc) val _ = DMSG (ST (Real.toString(!tmnu))) (dbgmc) 
					       val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("tm bo bb :")) (dbgmc) val _ = DMSG (ST (Real.toString(!tmbobb))) (dbgmc) 
						  val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("tm bo th :")) (dbgmc) val _ = DMSG (ST (Real.toString(!tmboth))) (dbgmc) 
						  val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("tm bo be :")) (dbgmc) val _ = DMSG (ST (Real.toString(!tmbobe))) (dbgmc) 
						  val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("tm fp oh :")) (dbgmc) val _ = DMSG (ST (Real.toString(!tmfpoh))) (dbgmc) 
						  val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("tm fp it :")) (dbgmc) val _ = DMSG (ST (Real.toString(!tmfpit))) (dbgmc) 
						  val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("tm fp it fn :")) (dbgmc) val _ = DMSG (ST (Real.toString(!tmfpitfn))) (dbgmc) 
						     val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
        val _ = DMSG (ST ("tm fp it it :")) (dbgmc) val _ = DMSG (ST (Real.toString(!tmfpitit))) (dbgmc) 
						     val _ = DMSG (ST ("\n")) (dbgmc)(*PRF*)
    in () end(*PRF*)

(* make final adjustments to result of model checking run 
   such as unwinding any contractions and other syntactic rearrangements of the formula *)
fun finish tb frv_thms = 
    let 
	val _ = DMSG (ST  "finish\n") (dbgmc)(*DBG*)
	val unfrv = BddApConv (ONCE_REWRITE_CONV [Binarymap.find(frv_thms,List.hd(snd(strip_comb(getTerm tb))))]) tb
	val _ = DMSG (ST  "finish done\n") (dbgmc)(*DBG*)
    in unfrv end

(* given the list of top-level approximations, find a path through them and return it as a trace *)
(* FIXME: a more readable trace would only print  out those AP's that are talked about in the corresponding property *) 
(*  FIXME: trace should start from the initial states *)  
fun makeTrace state vm mu_init_data ce = 
    let 
	val vmc = List.foldl (fn (v,bm) => Binarymap.insert(bm,v,Binarymap.find(vm,v))) (Binarymap.mkDict String.compare) 
			     (List.map term_to_string2 (strip_pair state)) 
	val cel = Option.valOf (!ce)
	val _ = DMSG (ST "ce length")(dbgmc) val _ = DMSG (NM (List.length cel))(dbgmc)
    in if (List.length cel = 1) then [] (* the fp comp terminated immediately, so trace is empty i.e. set of initial states is the ce *)
       else let 	        
	       val trbl = List.map getBdd (List.tl cel) (* list of outermost fp computation's approximations *) 
	       val (_,_,_,RTm) = Option.valOf (fst mu_init_data)  
	       val Rb = getBdd(Binarymap.find(RTm,".")) 
	       val _ = DMSG (ST  "makeTrace::trbl length ") (dbgmc)(*DBG*) 
	       val _ = DMSG (ST  ((int_to_string(List.length trbl))^"\n")) (dbgmc)(*DBG*) 
	       val _ = List.app (fn b => let val _ = DMSG (BD b)  (dbgmc) val _ = DMSG (ST  "\n") (dbgmc) in () end) trbl(*DBG*)
	       fun has_to b1 b2 = (* those states in b1 that have a transition to b2 *)
		 let val im = bddTools.mk_next state Rb vm b1 (* image of b1 under R *)
		     val pi = bddTools.mk_prev state Rb vm (bdd.AND(im,b2)) (*preimage of image cut down to b2 gets all source states *)
		   in bdd.AND(pi,b1) end (* cut down source states to the ones in b1 *)
	       fun mk_tr (apx::trl) prev = (* trace out a path of transitions over trbl *)
		   if bdd.equal bdd.FALSE (has_to prev apx)  (* no outgoing trans from current ce so return this *)
		   then []
		   else let val s1 = bddTools.mk_pt (bdd.AND(apx,bddTools.mk_next state Rb vm prev)) vmc (*next state on the trace *)
			in if List.null trl then [s1] 
			   else s1::(mk_tr trl s1) 
			end 
		 | mk_tr [] prev = Raise Match (* this should not happen here to avoid compiler warning *)
	       val tr = if (List.length trbl)=1 then [bddTools.mk_pt (List.hd trbl) vmc] 
			else let val s1 = bddTools.mk_pt (List.hd trbl) vmc in s1::(mk_tr (List.tl trbl) s1) end 
	       val trace = List.map (pt_bdd2state state vmc) tr
	       val _ = DMSG (ST  "makeTrace done") (dbgmc)(*DBG*)
	   in trace end
    end 

(* try and prove that M |= f i.e. initial states are contained in the term-bdd returned by muCheck *)
fun checkResult tb mf ks_def (I1,Itb) state ie vm =
    let 
	val _ = DMSG (ST  "checkResult") (dbgmc)(*DBG*)
	val ksname = lhs(concl ks_def)
	val Itb = if Option.isSome Itb then Option.valOf Itb else t2tb vm I1 
	val _ = DMSG (TM  (getTerm Itb)) (dbgmc) val _ = DMSG (ST  " Itb\n") (dbgmc)(*DBG*)
	val sIth = CONV_RULE (RHS_CONV (ONCE_REWRITE_CONV [GSYM SPECIFICATION])) 
	    (PBETA_RULE (AP_THM (SYM (PBETA_RULE (REWRITE_CONV [KS_accfupds,combinTheory.K_DEF,ks_def] ``(^ksname).S0``))) state))
	val _ = DMSG (TH  sIth) (dbgmc) val _ = DMSG (ST  " sIth\n") (dbgmc)(*DBG*)
	val Itb2 = BddEqMp sIth Itb
	val _ = DMSG (TM  (getTerm Itb2)) (dbgmc) val _ = DMSG (ST  " Itb2\n") (dbgmc)(*DBG*)
	val tb1 = BddForall (strip_pair state) (BddOp(bdd.Imp,Itb2,tb))
	val _ = DMSG (TM  (getTerm tb1)) (dbgmc) val _ = DMSG (ST  " tb1\n") (dbgmc)(*DBG*)
	val mms = CONV_RULE (RHS_CONV ELIM_TUPLED_QUANT_CONV) (CONV_RULE (RHS_CONV (GEN_PALPHA_CONV state)) 
							       (ISPECL [mf,lhs(concl ks_def),ie] MU_MODEL_SAT_def))
	val _ = DMSG (TH  mms) (dbgmc) val _ = DMSG (ST  " mms\n") (dbgmc)(*DBG*)
	val tb2 =  BddEqMp (SYM mms) tb1
	val _ = DMSG (TM  (getTerm tb2)) (dbgmc) val _ = DMSG (ST  " tb2\n") (dbgmc)(*DBG*)
	val tbth = SOME (BddThmOracle tb2) handle ex => NONE (* exception means failure *)
	val _ = DMSG (ST  "checkResult done") (dbgmc)(*DBG*)
    in tbth end

(* T1 is map from name of action -> corresponding term (of the action considered as a transition relation)
   ee is 'environment' i.e. vector of (RV, corresponding termbdd) pairs (termbdd is of set of states assigned to this RV)
   I is thm def of init state needed to compute the varsets for BddRules.BddExistsAnd, and termbdd replacement op
   mf is the mu formula to be checked
   absf is an optional abstraction function 
   OUT: termbdd of set of states satisfying mf, success theorem, ce/witness trace, cache of stuff usable for another property  *)
fun muCheck ee I1 T1 state vm Ric ce (absf,Itb) init_cache mf = 
    let val _ = reset_profile()(*PRF*)
	val (init_cache,init_stuff,(ks_def,mf,seth,ie,mfml,frv_thms,ce')) = init I1 T1 state vm Ric ce mf ee absf init_cache
	val tb = muCheck_aux (init_stuff,(seth,state,ie)) mf vm ((Array.length ee)-1) mfml
        val res_tb = finish tb frv_thms
	val res_thm = if Option.isSome (!ce) then NONE else checkResult res_tb mf ks_def (I1,Itb) state ie vm 
	val trace = if Option.isSome (!ce) then NONE 
		    else if is_universal mf 
		    then if Option.isSome res_thm then NONE 
			 else SOME (get_ce ee I1 T1 state vm Ric (absf,Itb) init_cache mf) (* compute counterexample *)
		    else if Option.isSome res_thm andalso is_traceable mf then SOME (makeTrace state vm init_cache ce')(* return witness *)
		    else NONE 
   in ((res_tb,res_thm,trace),init_cache) end (* init_cache can then be passed in as init_data next time *)

(* find counterexample... FIXME: only tested for AG properties so far, probably needs fixing to work for other A properties *)
(* FIXME thmfy the returned list ... what good would that be though? *)
(* FIXME will this work if ce is a loop i.e. if some initial state is reachable from a non-initial one? *)
and get_ce Ree I1 T1 state vm Ric (absf,Itb) mu_init_data mf = 
    let 
	val _ = DMSG (ST  "get_ce \n") (dbgmc)(*DBG*)
	in if is_traceable mf then 
	       let val ce = ref (SOME [])
		   (* model check the negation of f and save all top-level approximations in the ref ce*)
		   val _ = muCheck Ree I1 T1 state vm Ric ce (absf,Itb) mu_init_data (NNF(mu_neg mf))
		   val _ = DMSG (ST  "get_ce::fce done\n") (dbgmc)(*DBG*)
		   (* some "universal" props have no ce i.e. any prop with no fixpoint computation. in that case return empty trace *)
		   (* since the set of initial states is itself a counterexample                                                    *)
		   (* FIXME: handle this more intelligently, by returning a pt from S0 *)
		   val trace = if List.null (Option.valOf (!ce)) then [] else makeTrace state vm mu_init_data ce
		   val _ = DMSG (ST  "get_ce done\n") (dbgmc)(*DBG*)
	       in trace end
	   else [] 
    end

(* get trace and convert to trace of action names*)
fun findTraceNames RTm Ree I1 T1 state vm Ric mf (absf,Itb) mu_init_data =
    let val tr = get_ce Ree I1 T1 state vm Ric (absf,Itb) mu_init_data mf
	val (_,_,_,RTm) = Option.valOf (fst mu_init_data)
        val (actns,dotactn) = List.partition (fn (nm,_) => not (String.compare(nm,".")=EQUAL)) (Binarymap.listItems RTm)
        val (acts,acttbl) = ListPair.unzip (actns@dotactn) (* thus giving "." action last priority when pattern matching *) 
	val (s,sp) = (strip_pair ## strip_pair) (state,mk_primed_state state)
        val (stb,sptb) = ListPair.unzip(ListPair.map (fn (s,sp) => (BddVar true vm s,BddVar true vm sp)) (s,sp)) 
        fun findact (v,vp) = 
	    let val (vl,vpl) = (strip_pair ## strip_pair) (v,vp)
		val (vtb,vptb) = ListPair.unzip(ListPair.map (mk_con_tb_tm vm ## mk_con_tb_tm vm) (vl,vpl))
                val assl = ListPair.zip(stb@sptb,vtb@vptb)
                val (acts,restbs) = ListPair.unzip(ListPair.map (I ## (BddRestrict assl)) (acts,acttbl))
                val actl = List.filter (fn (nm,tb) => bdd.equal bdd.TRUE (getBdd tb)) (ListPair.zip(acts,restbs))
                val (nm,_) = ListPair.unzip actl
	    in List.hd nm end  
        val tr2 = List.map findact (threadlist tr)
    in tr2 end

end
end




