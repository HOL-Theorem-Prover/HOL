(*List.app load ["bossLib","stringTheory","stringLib","HolBddLib","pairTheory","pred_setLib","listLib","CTL","pairSyntax","pairRules","pairTools","muTheory","boolSyntax","Drule","Tactical","Conv","Rewrite","Tactic","boolTheory"]*)

structure muCheck =
struct

local

open Globals HolKernel Parse

open bossLib pairTheory pred_setTheory pred_setLib stringLib
     listTheory simpLib pairSyntax pairLib PrimitiveBddRules
     DerivedBddRules Binarymap PairRules pairTools boolSyntax Drule
     Tactical Conv Rewrite Tactic boolTheory listSyntax stringTheory
     boolSimps pureSimps listSimps numLib HolSatLib

open setLemmasTheory muSyntax muSyntaxTheory muTheory stringBinTree
     muTools commonTools ksTheory cearTheory bddTools envTheory envTools
     cacheTools cacheTheory ksTools lazyTools lzPairRules lzConv

val dpfx = "mc_"

in

fun mk_gen_ap_thm ksname state msa mf =
    let
	val _ = dbgTools.DEN dpfx "mga" (*DBG*)
	val _ = dbgTools.DTM (dpfx^"mga_mf")  mf (*DBG*)
	val _ = dbgTools.DTH (dpfx^ "mga_msa")  msa (*DBG*)
        val ap = rand mf
	val _ = dbgTools.DTM (dpfx^"mga_ap") ap (*DBG*)
        val apth = GSYM(lzPBETA_RULE (SPEC ap ((CONV_RULE lzSWAP_VARS_CONV) msa)))
	val _ = dbgTools.DTH (dpfx^"mga_apth")  apth (*DBG*)
	val _ = dbgTools.DEX dpfx "mga" (*DBG*)
    in apth end

fun mk_gen_modal_thm Tth modth mf =
    let
	val _ = dbgTools.DEN dpfx "mgm" (*DBG*)
	(*val _ = dbgTools.DTH (dpfx^ Tth) (*DBG*)
	val _ = dbgTools.DTH (dpfx^ modth) (*DBG*)
	val _ = dbgTools.DTM (dpfx^ mf) *)
        val nm = hd(snd(strip_comb mf))
	(*val ks1 = AP_THM Tth nm
	val ks2 = PURE_REWRITE_RULE [find_CONV (mk_comb(snd(dest_eq(concl Tth)), nm))] ks1*)
	val res = lzPBETA_RULE (PURE_REWRITE_RULE [Tth] (SPEC nm modth))
	(*val _ = dbgTools.DTH (dpfx^ res) (*DBG*)*)
	val _ = dbgTools.DEX dpfx "mgm" (*DBG*)
    in res end

(* returns mappings for each rv v->(x->"v"="x") where x are all the rv's in the formula (binding occurances included) *)
(* except for the cases v=x because that gives a trivial thm that causes the rewriter to loop *)
fun mk_seths mf =
    let
	val _ = dbgTools.DEN dpfx "mse" (*DBG*)
	val rvtm = ``(RV x):^(ty_antiq(type_of mf))``
	val mutm = ``(mu Q .. f):^(ty_antiq(type_of mf))``
	val nutm = ``(nu Q .. f):^(ty_antiq(type_of mf))``
	val rvs = Binaryset.addList(Binaryset.empty Term.compare,
				    ((List.map (fn tm => rand tm) (find_terms (can (match_term rvtm)) mf)) @
				     (List.map (fn tm => List.hd(snd(strip_comb tm)))
					       (find_terms (can (match_term mutm)) mf)) @
				     (List.map (fn tm => List.hd(snd(strip_comb tm)))
					       (find_terms (can (match_term nutm)) mf))))
        val seglpairs = List.map (fn l => (hd l,last l)) (cartprod [Binaryset.listItems rvs,Binaryset.listItems rvs])
        val segl2 = List.map (fn v => (v,list2map(List.map (fn (x,y) => (fromHOLstring y,mk_eq(x,y)))
				(List.filter (fn (x,y) => Term.compare(x,v)=EQUAL)
				 seglpairs)))) (Binaryset.listItems rvs)
	val seths = list2map(List.map (fn (v,gll) =>
				       (fromHOLstring v,
					Binarymap.map (fn (y,gl) => (* FIXME: this lz has not been verified *)
						       let val jf = (fn _ =>
									(PURE_REWRITE_RULE
								[GEN_ALL(List.last(CONJUNCTS (SPEC_ALL EQ_CLAUSES)))]
										 (stringLib.string_EQ_CONV gl)))
						       in mk_lthm (fn _ =>  (if Term.compare(lhs gl,rhs gl)=EQUAL
									    then mk_eq(gl,T) else mk_neg(gl),jf)) jf end)
						      gll)) segl2)
	val sel = (List.map snd (List.concat (List.map snd (Binarymap.listItems
								(Binarymap.map (Binarymap.listItems o snd) seths)))))
	val _ = dbgTools.DEX dpfx "mse" (*DBG*)
        in (seths,sel) end

(* for when we have not got sel precomputed  *)
fun prove_imf f =
    let val p_ty = muSyntax.get_prop_type f
	val sel = snd (mk_seths f)
	val imfth = mk_imf_thm (inst [alpha |-> p_ty] muSyntax.mu_imf_tm) f (mk_tysimps sel p_ty) p_ty
    in imfth end

fun mk_gen_rv_thms mf ksname state rvl ie wfKS_ks =
   let
       val _ = dbgTools.DEN dpfx "mgr" (*DBG*)
       val _ = dbgTools.DTH (dpfx^"mgr_wfKS_ks") wfKS_ks (*DBG*)
       val _ = dbgTools.DTH (dpfx^"mgr_spec_MU_SAT_RV")  (ISPECL [state,ksname] MU_SAT_RV) (*DBG*)
       val _ = dbgTools.DTH (dpfx^"mgr_msr_ante")  (CONV_RULE lzFORALL_IMP_CONV(ISPECL [state,ksname] MU_SAT_RV))(*DBG*)
       val msr = MP (CONV_RULE lzFORALL_IMP_CONV (ISPECL [state,ksname] MU_SAT_RV)) wfKS_ks
       val msreq = ISPEC state (MP (ISPEC ksname MU_SAT_RV_ENV_EQ) wfKS_ks)
       val _ = dbgTools.DEX dpfx "mgr" (*DBG*)
   in (msr,mk_seths mf,msreq) end

fun mk_gen_thms T (apl,ks_def,wfKS_ks) state state' st vm =
   let
       val _ = dbgTools.DEN dpfx "mgt" (*DBG*)
       (* Note: this assumes varmap assignments are contiguous stating from zero TODO: get rid of this assumption *)
       val i2ap = Vector.fromList (List.map (fn ap => BddVar true vm ap) st)
       val apnm2ix =fst(Vector.foldl (fn(nm,(bm,ix)) => (Binarymap.insert(bm,term_to_string2(getTerm(nm)),ix),ix+1))
				      (Binarymap.mkDict String.compare,0) i2ap)
       (*val _ = dbgTools.DST (dpfx^ ("vector i2ap\n"))
         val _ = Vector.app (fn nm => dbgTools.DST (dpfx^ ("("^(term_to_string(getTerm nm))^")")) ) i2ap(*DBG*)
         val _ = dbgTools.DST (dpfx^ ("mapnm2ix\n"))
         val _ =Binarymap.app (fn(nm,ix)=> dbgTools.DST (dpfx^ ("("^nm^","^(int_to_string ix)^")")))  apnm2ix(*DBG*)*)
       val ksname = lhs(concl ks_def)
       val (prop_type,state_type) = get_types ksname
       val env_ty = stringLib.string_ty --> state_type --> bool
       val stpset_ty = (mk_prod(state_type,state_type)) --> bool
       val KSap = List.foldl (fn (e,ac) => list_mk_comb (inst [alpha|->prop_type] pred_setSyntax.insert_tm,[e,ac]))
			     (inst [alpha|->prop_type] pred_setSyntax.empty_tm) apl
       val msthl = List.map (fn th => MATCH_MP (CONV_RULE lzFORALL_IMP_CONV (ISPECL [state,ksname] th)) wfKS_ks)
	   (MU_SAT_AP::MU_SAT_DMD::MU_SAT_BOX::[MU_SAT_T,MU_SAT_F,MU_SAT_NEG,MU_SAT_CONJ,MU_SAT_DISJ])
       val Lth = mk_Lth ks_def
       val _ =  dbgTools.DTH (dpfx^"mgt_ Lth") Lth (*DBG*)
       (*val _ = List.app (fn th => dbgTools.DTH (dpfx^ th) ) msthl val _ =  dbgTools.DST (dpfx^ "msthl\n") *)
       (*val msa = PBETA_RULE (PURE_REWRITE_RULE [Lth] (List.nth(msthl,0)))*)
       val pvar = mk_var("p",prop_type)
       val jf = (fn _ =>  (PURE_REWRITE_RULE [Lth] (List.nth(msthl,0))))
       val msa = lzPBETA_RULE
		     (mk_lthm (fn _ => (``!e p. MU_SAT (AP p) ^ksname e ^state =
					^(list_mk_comb(rhs(concl Lth),[state,pvar]))``,jf)) jf)
       (*val _ =  dbgTools.DTH (dpfx^ msa)   val _ =  dbgTools.DST (dpfx^ "msa\n") *)
       val msp = List.map GSYM (List.drop(msthl,3))
       val (Tth,dmdth) = mk_Tth ks_def ksname (List.nth(msthl,1)) (List.nth(msthl,2)) state' state_type prop_type
       val githms = mk_gen_inv_thms ksname state wfKS_ks
       val _ = dbgTools.DEX dpfx "mgt" (*DBG*)
   in (msp,msa,Tth,dmdth,githms) end

(* note this assumes that an AP is a boolean term *)
(* if AP's are over non-booleans, then we do suitable preprocessing on the model to turn stuff into booleans
   otherwise you can't make BDD's out of them *)
fun mk_ap_tb vm absf mf sth =
    let
	val _ = dbgTools.DEN dpfx "mat" (*DBG*)
        (*val _ = dbgTools.DTM (dpfx^  mf)  val _ = dbgTools.DST (dpfx^  "(mf)\n") (*DBG*)
        val _ = dbgTools.DTH (dpfx^  sth)  val _ = dbgTools.DST (dpfx^  "(sth)\n") (*DBG*)*)
	val ap = pbody (snd (dest_comb mf))
        val tb =  if (Option.isSome absf) then (* FIXME: can we remove the reference to absf? *)
		      let val htb = Option.valOf absf
			  val ht = getTerm htb
			  val cstate = fst(dest_pair(List.hd (snd (strip_comb ht))))
		      in BddExists (strip_pair cstate) (BddOp(bdd.And,htb, t2tb vm ap)) end
		  else t2tb vm ap
	(*val _ = dbgTools.DTM (dpfx^ (getTerm tb))  val _ = dbgTools.DST (dpfx^  "(tb)\n") (*DBG*)*)
	val res = BddEqMp sth tb
	val _ = dbgTools.DEX dpfx "mat" (*DBG*)
    in res  end

fun mk_con_tb_tm vm tm = if (Term.compare(tm,T)=EQUAL) then BddCon true vm else BddCon false vm

fun mk_con_tb b vm mf sth =
    let
	val _ = dbgTools.DEN dpfx "mct" (*DBG*)
	(*val _ = dbgTools.DTH (dpfx^  sth) (*DBG*)
	val _ = dbgTools.DST (dpfx^  " sth\n") (*DBG*)*)
	val res = BddEqMp sth (BddCon b vm)
	val _ = dbgTools.DEX dpfx "mct" (*DBG*)
    in res end

fun mk_rv_tb ee (_,_,_,_,ix,_,_,_,_,_) mf sth  =
    let
	val _ = dbgTools.DEN dpfx "mrt" (*DBG*)
	(*val _ = dbgTools.DTH (dpfx^  sth) (*DBG*)
	val _ = dbgTools.DST (dpfx^  "rv tb sth\n") (*DBG*)
	val _ = dbgTools.DST (dpfx^  (int_to_string ix)) (*DBG*)
	val _ = dbgTools.DST (dpfx^  " ix\n") (*DBG*)
	val _ = dbgTools.DST (dpfx^  (int_to_string (Array.length ee))) (*DBG*)
	val _ = dbgTools.DST (dpfx^  " ee length\n") (*DBG*)
	val _ = dbgTools.DTM (dpfx^  (getTerm (snd(Array.sub(ee,ix))))) (*DBG*)
	val _ = dbgTools.DST (dpfx^  "rv tb\n") (*DBG*)*)
	val res = BddEqMp sth (snd(Array.sub(ee,ix)))
	(*val _ = dbgTools.DTM (dpfx^  (getTerm res)) (*DBG*)*)
	val _ = dbgTools.DEX dpfx "mrt" (*DBG*)
    in res end

fun mk_rv_spec_thm msr seth sel msreq ie ee state (tb,gth,sth,env,ix,rsc,ithm,abthm,_,_) dp mf =
    let
	val _ = dbgTools.DEN dpfx "mrst" (*DBG*)
	(*val _ = dbgTools.DTM (dpfx^  ie) 	val _ = dbgTools.DST (dpfx^  " ie \n") (*DBG*)*)
	val bv = rand mf
	(*val _ = dbgTools.DTM (dpfx^  bv)  val _ = dbgTools.DST (dpfx^  " bv \n") (*DBG*)*)
	val v = fromHOLstring(bv)
	(*val _ = dbgTools.DTH (dpfx^  msr)  val _ = dbgTools.DST (dpfx^  "msr\n") (*DBG*)
	val _ = if (Option.isSome sth) then dbgTools.DTH (dpfx^  (Option.valOf sth))  else dbgTools.DST (dpfx^  " NONE")
	val _ = dbgTools.DST (dpfx^  "\nsth\n") (*DBG*)
	val _ = dbgTools.DTM (dpfx^  ie)  val _ = dbgTools.DST (dpfx^  " ie\n") (*DBG*)
        val _ = List.app (fn th => let val _ = dbgTools.DTH (dpfx^  th)
				       val _ = dbgTools.DST (dpfx^  "seth\n")  in () end)(*DBG*)
			 ((List.map snd (Binarymap.listItems(Binarymap.find(seth,v))))@[ENV_UPDATE_def,BETA_THM])(*DBG*)*)
	val th =  if (Int.compare(ix,dp)=EQUAL
		      andalso (Vector.sub(rsc,ix)>0)) (*i.e.current bnd var top level fv filt by >0 test*)
		  then (* this has already been proved in FixExp *)
		      Option.valOf sth
		  else (* otherwise not innermost bound var so must account for change in environment *)
		      let
			  (*val _ = dbgTools.DST (dpfx^  "else\n")
			   val _ = dbgTools.DTH (dpfx^  (ISPECL [ie,fromMLstring v] msr))
                            val _ = dbgTools.DST (dpfx^  " msr1\n") (*DBG*)
			    val _ = List.app (fn th => let val _ = dbgTools.DTH (dpfx^  th)
                            val _ = dbgTools.DST (dpfx^  " seths\n")  in () end)(*DBG*)
			      (List.map snd (Binarymap.listItems(Binarymap.find(seth,v))))(*DBG*)
			    val _ = dbgTools.DTH (dpfx^  (eval_env ie ie bv seth [])) (*DBG*)
			    val _ = dbgTools.DST (dpfx^  " env_eval thm\n") (*DBG*)*)
		      in SYM (CONV_RULE(RHS_CONV(PURE_ONCE_REWRITE_CONV [eval_env ie ie bv state seth sel []]))
				       (ISPECL [ie,bv] msr)) end
	(*val _ = dbgTools.DTH (dpfx^  th)  val _ = dbgTools.DST (dpfx^  "rv spec thm\n") (*DBG*)*)
	val _ = dbgTools.DEX dpfx "mrst" (*DBG*)
    in th end

(* in case an mf is an RV, getting the spec thm is more than just SPEC'ing the gth with the ie *)
fun get_spec_thm ie spec_func gth mf =
    let
	val _ = dbgTools.DEN dpfx "gst" (*DBG*)
	(*val _ = dbgTools.DTH (dpfx^  gth)  val _ = dbgTools.DST (dpfx^  " gth\n") (*DBG*)*)
	val res = if is_RV mf (* RV case *)
		  then spec_func mf (* this calls mk_rv_spec_thm *)
		  else let
		      (*val _ = dbgTools.DST (dpfx^  "not RV \n")  val _ = dbgTools.DST (dpfx^ _type (type_of ie))
         	       val _ = dbgTools.DST (dpfx^  " ie type\n") (*DBG*)
		       val _ =  dbgTools.DTH (dpfx^  gth)  val _ = dbgTools.DST (dpfx^  " gth with type\n") (*DBG*)*)
		      in SPEC ie gth end
	val _ = dbgTools.DEX dpfx "gst" (*DBG*)
    in res end

(* dummy theorem, not used by FixExp *)
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
	val _ = dbgTools.DEN dpfx "msit" (*DBG*)
	val (opr,args) = strip_comb mf
	(*val _ = dbgTools.DTM (dpfx^  mf)  val _ = dbgTools.DST (dpfx^  " mf\n") (*DBG*)
        val _ = dbgTools.DTM (dpfx^  ie0)  val _ = dbgTools.DST (dpfx^  " ie0\n") (*DBG*)
	val _ = dbgTools.DTM (dpfx^  ie1)  val _ = dbgTools.DST (dpfx^  " ie1\n") (*DBG*)
	val _ = dbgTools.DTH (dpfx^  githm)  val _ = dbgTools.DST (dpfx^  " githm\n") (*DBG*)	*)
	val res =
	    case (fst (dest_const opr)) of
		"AP"      => ISPECL [ie0,ie1] githm
	      | "RV"      => let val Hv = List.hd args
				 val v = fromHOLstring Hv
			     (*val _ = dbgTools.DTM (dpfx^" spec_inv goal\n"  ``^ie0 ^Hv = ^ie1 ^Hv``)   (*DBG*)*)
				 val sel =  (List.map snd (Binarymap.listItems(Binarymap.find(seth,v))))
				 val goal = mk_eq(mk_comb(ie0,Hv),mk_comb(ie1,Hv)) (*``^ie0 ^Hv = ^ie1 ^Hv`` *)
				 val jf = (fn _ =>  (prove(goal,SIMP_TAC std_ss ([ENV_UPDATE_def]@sel))) )
				 val ethm = mk_lthm (fn _ => (goal,jf)) jf
			     (*val _ = dbgTools.DTH (dpfx^  ethm)  val _ = dbgTools.DST (dpfx^  " ethm\n") (*DBG*)*)
			     in (*MATCH_*)MP (ISPECL [ie0,ie1] githm) ethm end
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
	(*val _ = dbgTools.DTH (dpfx^  res)  val _ = dbgTools.DST (dpfx^  " mk_spec_inv_thm res\n") (*DBG*)*)
	val _ = dbgTools.DEX dpfx "msit" (*DBG*)
    in res end

(* goal is a conjunction of equalities of the form ie0 Q = ie1 Q TODO:speed this up*)
fun mk_se_thm goal sel =
    let
	val _ = dbgTools.DEN dpfx "mst" (*DBG*)
	(*val _ = dbgTools.DTM (dpfx^  goal)  val _ = dbgTools.DST (dpfx^  " goal\n") (*DBG*)*)
	(*val _ =List.app (fn th => dbgTools.DTH (dpfx^" cache seth\n"  th)) sel(*DBG*)*)
	val jf = (fn _ =>  (prove(goal,SIMP_TAC std_ss (ENV_UPDATE_def::sel))))
	val res = mk_lthm (fn _ => (goal,jf)) jf
	val _ = dbgTools.DEX dpfx "mst" (*DBG*)
    in res end

(* retrieve term_bdd from cache. if missing use callbacks to create it and update cache *)
fun cache_get cch ie tb_func gth_func dp nodes mf seth sel state =
    let val (tb,gth,sth,env,ix,rsc,ithm,abthm,ado_subthm,ado_eqthm) = !cch
	val _ = dbgTools.DEN dpfx "cg" (*DBG*)
	(*val _ = dbgTools.DTM (dpfx^  mf)   val _ = dbgTools.DST (dpfx^  " mf\n") (*DBG*)
	val _ = dbgTools.DST (dpfx^ (Int.toString dp))  val _ = dbgTools.DST (dpfx^  " dp\n") (*DBG*)
        val _ = dbgTools.DST (dpfx^ (Int.toString ix))  val _ = dbgTools.DST (dpfx^  " ix\n") (*DBG*)
	val _ = if  then let val _ = print_rsc rsc "" in () end else () (*DBG*)
	val _ = dbgTools.DST (dpfx^  (Int.toString(Vector.length rsc)))  (*DBG*)
	val _ = dbgTools.DST (dpfx^  " rsc length\n") (*DBG*)*)
        fun check_rv rsc dp = if (dp=(~1)) then true else if (Vector.sub(rsc,dp)=0) then check_rv rsc (dp-1) else false
	(*val _ = with_flag (show_types,true) dbgTools.DTM (dpfx^  ie)  val _ = dbgTools.DST (dpfx^  " ie\n") (*DBG*)
	val _ = with_flag (show_types,true) dbgTools.DTM (dpfx^  env)  val _ = dbgTools.DST (dpfx^  " env\n") (*DBG*)*)
     val res = if (Term.compare(env,ie)=EQUAL)
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
			    val _ = dbgTools.DST (dpfx^"cg_ gth SOME\n") (*DBG*)
			    (*val _ = with_flag(show_types,true) dbgTools.DTH (dpfx^  (Option.valOf gth))  (*DBG*)
                              val _ = dbgTools.DST (dpfx^  " gth\n") (*DBG*)*)
			    val sth = get_spec_thm ie gth_func (Option.valOf gth) mf (* could be an RV *)
			    val tb = tb_func mf sth
			    val _ = upd_cch_tb cch tb val _ = upd_cch_sth cch sth
			in tb end
		   else let
			    val _ = dbgTools.DST (dpfx^"cg_ gth NONE\n") (*DBG*)
			    (*val _ = dbgTools.DTM (dpfx^  mf) (*DBG*)*)
			    val gth = gth_func mf (* can't be an RV because we stuffed its gth with TRUTH *)
			    (*val _ =  dbgTools.DTH (dpfx^  gth)  val _ = dbgTools.DST (dpfx^  " gth\n")  *)(*DBG*)
			    val sth = ISPEC ie gth
			    (*val _ = dbgTools.DTH (dpfx^  sth)  val _ = dbgTools.DST (dpfx^  " sth22\n") (*DBG*)*)
			    val tb = tb_func mf sth
			    val _ = upd_cch_tb cch tb val _ = upd_cch_sth cch sth val _ = upd_cch_gth cch gth
			in tb end
       else
	   if (Option.isSome tb andalso (check_rv rsc dp))
	   then (* above check prevents dirty read i.e. only if no subformula contains a currently bound RV *)
	       if (Option.isSome gth)
	       then let
			val _ = dbgTools.DST (dpfx^"cg_ cached\n") (*DBG*)
			(*val _ = dbgTools.DTM (dpfx^ (getTerm (Option.valOf tb))) (*DBG*)
			val _ = dbgTools.DST (dpfx^  " cached tb\n") (*DBG*)
			val _ = if  then let val _ = print _rsc rsc "cached tb" in () end else () (*DBG*)*)
			val sth1 = get_spec_thm ie gth_func (Option.valOf gth) mf (* could be an RV *)
			val sth0 = Option.valOf sth
			(*val _ = dbgTools.DTH (dpfx^  sth0)  val _ = dbgTools.DST (dpfx^  " sth0\n") (*DBG*)*)
			val sithm = mk_spec_inv_thm ithm nodes env ie mf seth
			(*val _ = dbgTools.DTH (dpfx^ (sithm))  val _ = dbgTools.DST (dpfx^  "sithm0\n") (*DBG*)*)
			val sithm = if (is_imp(concl sithm))
				    then (*MATCH_*)MP sithm (mk_se_thm (fst(dest_imp(concl sithm))) sel)
				    else sithm
			(*val _ = dbgTools.DTH (dpfx^ (sithm))  val _ = dbgTools.DST (dpfx^  "sithm1\n") (*DBG*)*)
			val sithm = AP_THM sithm state
			(*val _ = dbgTools.DTH (dpfx^ (sithm))  val _ = dbgTools.DST (dpfx^  "sithm2\n") (*DBG*)*)
			val tb = BddEqMp sithm (Option.valOf tb)
			val _ = dbgTools.DST (dpfx^"cg_ tb cache read done\n")
			val _ = upd_cch_tb cch tb val _ = upd_cch_sth cch sth1 val _ = upd_cch_env cch ie
		    in tb end
	       else failwith("Internal error: cache_get: Cache has term_bdd but no gen thm")
	   else (* otherwise we have to recompute this tb (however note that no clean subformula  will be recomputed) *)
	       if (Option.isSome gth)
	       then let val _ = dbgTools.DST (dpfx^"cg_ recompute SOME gth\n") (*DBG*)
			val sth = get_spec_thm ie gth_func (Option.valOf gth) mf (* could be an RV *)
			val tb = tb_func mf sth
			val _ = upd_cch_tb cch tb val _ = upd_cch_sth cch sth val _ = upd_cch_env cch ie
		    in tb end
	       else let val _ = dbgTools.DST (dpfx^"cg_ recompute NONE gth\n") (*DBG*)
			val gth = gth_func mf
			val sth = if (is_RV mf) then gth else ISPEC ie gth
			(*val _ = with_flag(show_types,true) dbgTools.DTH (dpfx^  gth)
			 val _ = dbgTools.DST (dpfx^  " gth\n") (*DBG*) *)
			val tb = tb_func mf sth
			val _ = upd_cch_tb cch tb val _ = upd_cch_sth cch sth
			val _ = upd_cch_gth cch gth val _ = upd_cch_env cch ie
		    in tb end
     val _ = dbgTools.DEX dpfx "cg" (*DBG*)
    in res end

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

fun muCheck_aux ((_,(msa,absf,ksname),_,_,_),(seth,sel,state,ie)) mf vm dp (muAP cch) =
    let val _ = profTools.bgt (dpfx^"mc_ap")(*PRF*)
	val tb = cache_get cch ie (mk_ap_tb vm absf) (mk_gen_ap_thm ksname state msa) dp [] mf seth sel state
	val _ = profTools.ent (dpfx^"mc_ap")(*PRF*)
    in tb end
  | muCheck_aux ((_,_,(msr,_,msreq,ee),_,_),(seth,sel,state,ie)) mf vm dp (muRV cch) =
    let val _ = profTools.bgt (dpfx^"mc_rv")(*PRF*)
	val tb = cache_get cch ie (mk_rv_tb ee (!cch)) (mk_rv_spec_thm msr seth sel msreq ie ee state (!cch) dp) dp []
			   mf seth sel state
	val _ = profTools.ent (dpfx^"mc_rv")(*PRF*)
    in tb end
  | muCheck_aux (args as (msp,_,_,_,_),(seth,sel,state,ie)) mf vm dp (muAnd(cch,(f1,f2))) =
    let
	val (abthm,abthnm,mf1,mf2,cab1,cab1nm,cab2,cab2nm) = get_abthms mf f1 f2 cch
	val tb = cache_get cch ie (BinExp (args,(seth,sel,state,ie)) bdd.And (snd(strip_comb(mf))) vm (f1,f2) dp abthm)
	    (fn mf => GEN ``e:^(ty_antiq(type_of ie))``
	     (ISPECL [``e:^(ty_antiq(type_of ie))``,cab1nm,cab2nm]
	      (List.nth(msp,3)))) dp [f1,f2] mf seth sel state
    in  tb end
  | muCheck_aux (args as (msp,_,_,_,_),(seth,sel,state,ie)) mf vm dp (muOr(cch,(f1,f2))) =
    let
	val (abthm,abthnm,mf1,mf2,cab1,cab1nm,cab2,cab2nm) = get_abthms mf f1 f2 cch
	val tb = cache_get cch ie (BinExp (args,(seth,sel,state,ie)) bdd.Or (snd(strip_comb(mf))) vm (f1,f2) dp abthm)
	    (fn mf => GEN ``e:^(ty_antiq(type_of ie))``
	     (ISPECL [``e:^(ty_antiq(type_of ie))``,cab1nm,cab2nm]
	      (List.nth(msp,4)))) dp [f1,f2] mf seth sel state
    in tb end
  | muCheck_aux (args as (msp,_,_,_,_),(seth,sel,state,ie)) mf vm dp (muNot(cch,f1)) =
    let
	val (abthm,abthnm,mf1,_,cabthm,cabthmnm,_,_) = get_abthms mf f1 f1 cch
	val tb = cache_get cch ie (NotExp (args,(seth,sel,state,ie)) mf1 vm dp f1 abthm)
	    (fn mf => (ISPEC cabthmnm ((CONV_RULE SWAP_VARS_CONV) (List.nth(msp,2))))) dp [f1] mf seth sel state
    in tb end
  | muCheck_aux ((msp,_,_,_,_),(seth,sel,state,ie)) mf vm dp (muTR cch) =
	cache_get cch ie (mk_con_tb true vm) (fn mf => (List.nth(msp,0))) dp [] mf seth sel state
  | muCheck_aux ((msp,_,_,_,_),(seth,sel,state,ie)) mf vm dp (muFL cch) =
	cache_get cch ie (mk_con_tb false vm) (fn mf => (List.nth(msp,1))) dp [] mf seth sel state
  | muCheck_aux (args as (_,_,_,(_,Tth,(dmdth,_),_,_),_),(seth,sel,state,ie)) mf vm dp (muDIAMOND(cch,(act,f1))) =
     let
	 val (abthm,abthnm,_,_,cabthm,cabthmnm,_,_) = get_abthms mf f1 f1 cch
	 val tb = cache_get cch ie (ModalExp (args,(seth,sel,state,ie)) act false (List.last(snd(strip_comb mf)))
					     vm f1 dp abthm)
	     (mk_gen_modal_thm Tth dmdth) dp [f1] mf seth sel state
     in  tb end
  | muCheck_aux (args as (_,_,_,(_,Tth,(_,boxth),_,_),_),(seth,sel,state,ie)) mf vm dp (muBOX(cch,(act,f1))) =
     let
	 val (abthm,abthnm,_,_,cabthm,cabthmnm,_,_) = get_abthms mf f1 f1 cch
	 val tb = cache_get cch ie (ModalExp (args,(seth,sel,state,ie)) act true (List.last(snd(strip_comb mf)))
					     vm f1 dp abthm)
	     (mk_gen_modal_thm Tth boxth) dp [f1] mf seth sel state
     in tb end
  | muCheck_aux (args,(seth,sel,state,ie)) mf vm dp (fpmu(bvch,cch,f1)) =
    let
	val rvnm = List.hd(snd(strip_comb mf))
	val (abthm,abthnm,mf1,_,cabthm,cabthmnm,_,_) = get_abthms mf f1 f1 cch
	val tb = cache_get cch ie (FixExp (args,(seth,sel,state,ie)) [rvnm,cabthmnm] (BddCon false vm) vm
					  (bvch,cch,f1) (dp+1) abthm cabthm) (mk_fp_gen_thm state) dp [f1]
			   mf seth sel state
    in tb end
  | muCheck_aux (args,(seth,sel,state,ie)) mf vm dp (fpnu(bvch,cch,f1)) =
    let
	val rvnm = List.hd(snd(strip_comb mf))
	val (abthm,abthnm,mf1,_,cabthm,cabthmnm,_,_) = get_abthms mf f1 f1 cch
	val tb = cache_get cch ie (FixExp (args,(seth,sel,state,ie)) [rvnm,cabthmnm] (BddCon true vm) vm
					  (bvch,cch,f1) (dp+1) abthm cabthm) (mk_fp_gen_thm state) dp [f1]
			   mf seth sel state
    in tb end

and NotExp (args,(seth,sel,state,ie)) mf1 vm dp f1 abthm mf sth =
    let
	val _ = dbgTools.DEN dpfx "ne" (*DBG*)
	val tb = BddNot (muCheck_aux (args,(seth,sel,state,ie)) mf1 vm dp f1)
	val _ = profTools.bgt (dpfx^"mc_neg")(*PRF*)
	(*val _ = dbgTools.DTM (dpfx^ (getTerm tb))  val _ = dbgTools.DST (dpfx^  " NotExp tb\n")
          val _ = dbgTools.DTH (dpfx^  sth)  val _ = dbgTools.DST (dpfx^  " NotExp sth\n") (*DBG*)*)
	val sth = PURE_REWRITE_RULE [SYM abthm] sth
	(*val _ = dbgTools.DTH (dpfx^  sth)  val _ = dbgTools.DST (dpfx^  " NotExp sth abbrev\n") (*DBG*)*)
	val tb2 = BddEqMp sth tb
	val _ = profTools.ent (dpfx^"mc_neg")(*PRF*)
	val _ = dbgTools.DEX dpfx "ne" (*DBG*)
    in tb2 end

and BinExp (args,(seth,sel,state,ie)) opr [t1,t2] vm (f1,f2) dp abthm mf opthm =
    let
	val _ = dbgTools.DEN dpfx "be" (*DBG*)
	(*val _ = dbgTools.DTM (dpfx^  t1) 	val _ = dbgTools.DST (dpfx^ ("b1\n")) (*DBG*)*)
	val b1 = muCheck_aux (args,(seth,sel,state,ie)) t1 vm dp f1
	(*val _ = dbgTools.DTM (dpfx^  t2) 	val _ = dbgTools.DST (dpfx^ ("b2\n")) (*DBG*)*)
        val b2 = muCheck_aux (args,(seth,sel,state,ie)) t2 vm dp f2
	(*val _ = dbgTools.DST (dpfx^ ("bop\n")) (*DBG*)*)
	val _ = profTools.bgt (dpfx^"mc_bin")(*PRF*)
        val bb = BddOp(opr,b1,b2)
	(*val _ = dbgTools.DTM (dpfx^  (getTerm bb))  val _ = dbgTools.DST (dpfx^  " BinExp bb\n")
          val _ = dbgTools.DTH (dpfx^  opthm)  val _ = dbgTools.DST (dpfx^  " BinExp opthm\n") (*DBG*)*)
	val opthm = PURE_REWRITE_RULE [SYM abthm] opthm
	(*val _ = dbgTools.DTH (dpfx^  opthm ) val _ = dbgTools.DST (dpfx^  " BinExp opthm abbrev\n") (*DBG*) *)
	val tb =BddEqMp opthm bb
	val _ = profTools.ent (dpfx^"mc_bin")(*PRF*)
	val _ = dbgTools.DEX dpfx "be" (*DBG*)
    in tb end
  | BinExp _ _ _ _ _ _ _ _ _ = Raise Match (* impossible, just here to avoid warning *)

and ModalExp (args as (_,_,_,(RTm,_,_,sp,s2sp),_),(seth,sel,state,ie))  actnm isbox t2 vm f1 dp abthm mf sth =
    let
	val _ = dbgTools.DEN dpfx "me" (*DBG*)
	val tb1 = muCheck_aux (args,(seth,sel,state,ie)) t2 vm dp f1
	val _ = profTools.bgt (dpfx^"mc_mod")(*PRF*)
        val tb2 = if isbox then BddAppall sp (bdd.Imp, find(RTm,actnm),(BddReplace  s2sp tb1))
		  else BddAppex sp (bdd.And, find(RTm,actnm),(BddReplace  s2sp tb1))
	val sth = SPEC (hd(snd(strip_comb(getTerm(tb1))))) sth (* TODO: move this to muCheck_aux as with ~,/\,\/ etc*)
	(*val _ = dbgTools.DTH (dpfx^  sth) 	val _ = dbgTools.DST (dpfx^  " ModalExp sth\n") (*DBG*)*)
	val sth = PURE_REWRITE_RULE [SYM abthm] sth
	(*val _ = dbgTools.DTH (dpfx^  sth) 	val _ = dbgTools.DST (dpfx^  " ModalExp sth abbrev\n")
          val _ = dbgTools.DTM (dpfx^  (getTerm tb2))  val _ = dbgTools.DST (dpfx^  " tb2\n") (*DBG*)*)
	val ttb = BddEqMp (SYM sth) tb2
	val _ = profTools.ent (dpfx^"mc_mod")(*PRF*)
	val _ = dbgTools.DEX dpfx "me" (*DBG*)
    in ttb end

and FixExp ((p_,ap_,rv_,d_,
	   (wfKS_ks,finS,frv_thms,imf_thms,pextth,rvtt,mssth,fps,eus,Ss,ess,statel,ksname,prop_type,ee,qd,sqd,ce,qt,eeq)),
	   (seth,sel,state,ie)) [t1,t2] initbdd vm (bvch,_,f1) dp abthm cabthm mf _ =
    let (*FIXME: clean up this monster *)
	val _ = dbgTools.DEN dpfx "fe" (*DBG*)
	val _ = profTools.bgt (dpfx^"fe")(*PRF*)
	(*val _ = dbgTools.DTM (dpfx^  t2)  val _ = dbgTools.DST (dpfx^  " t2\n") (*DBG*)*)
	(* note that the binding occurance uses same cache node as the occurances of the bv in the formula *)
	val (bvtb,bvgth,bvsth,bvenv,bvix,bvrsc,bvithm,bvabthm,ado_subthm,ado_eqthm) = !bvch
	val bv = (fromHOLstring(t1))
	val p_ty = get_prop_type t2
        val (ttm,initset,imf_t2g,init_thm,abbrev_thm,fp2thm,adogeneqthm,bigthm,chainth,initsubth) =
	    if (bdd.equal (getBdd(initbdd)) (bdd.TRUE))
		then (true,Ss,list_mk_comb(get_mu_ty_nu_tm p_ty,[t1,List.last (snd(strip_comb mf))]),
		      GFP_INIT,NU_FP_STATES,STATES_FP_BIGINTER_2,STATES_DEF_SYM_NU,NU_BIGINTER,GEN_GFP_CHAIN,
		      let val jf = (fn _ => (REWRITE_RULE [SYM (List.last (CONJUNCTS (REWRITE_RULE [wfKS_def] wfKS_ks)))]
							 (INST_TYPE [alpha|->type_of state] SUBSET_UNIV)))
		      in mk_lthm (fn _ => (``!s. s SUBSET ^Ss``,jf)) jf end)
            else (false,ess,list_mk_comb(get_mu_ty_mu_tm p_ty,[t1,List.last (snd(strip_comb mf))]),LFP_INIT,MU_FP_STATES,
		      STATES_FP_BIGUNION_2,STATES_DEF_SYM_MU,MU_BIGUNION,GEN_LFP_CHAIN,EMPTY_SUBSET)
	(*val _ = dbgTools.DST (dpfx^  (if ttm then "true" else "false"))  val _ = dbgTools.DST (dpfx^  " ttm\n") (*DBG*)
	val _ = dbgTools.DTM (dpfx^  ie)  val _ = dbgTools.DST (dpfx^  " ie\n") (*DBG*)*)
	(*  ado: max same_quant nesting depth is 2 and immediate outer bv (if any) has the same fp operator as this one,
                 and the outer bv has not been just reset *)
	val ado = (sqd andalso (not (List.null qt)) andalso (ttm=List.hd qt))
		  andalso (not (Term.compare(numSyntax.zero_tm,List.last(snd(strip_comb(snd(dest_comb ie)))))=EQUAL))
	val _ = if ado then dbgTools.DST (dpfx^  "ADO active\n")  else dbgTools.DST (dpfx^  "no ADO\n") (*DBG*)
	(* if ado then start from where we left off. ASSERT:ado==>Option.isSome bvtb *)
	val ((initset,initbdd),init_thm,abbrev_thm) =
	    if (ado)
		then let val bvt = getTerm(Option.valOf bvtb)
			 (*val _ = dbgTools.DTM (dpfx^  bvt)  val _ = dbgTools.DST (dpfx^  " bvt\n") (*DBG*)*)
			 val e = List.nth(snd(strip_comb bvt),2) (* bvt is a MU_SAT term, so e is prev outer env *)
			 (*val _ = dbgTools.DTM (dpfx^  e)  val _ = dbgTools.DST (dpfx^  " e\n") (*DBG*)*)
			 val X = get_env_val state t1 e
			 (*val _ = dbgTools.DTM (dpfx^  X)  val _ = dbgTools.DST (dpfx^  " X\n") (*DBG*)*)
			 val th = MP (ISPECL [ksname,fst(dest_env e),t1,state,X] GEN_MS_FP_INIT) wfKS_ks
		         (*val _ = dbgTools.DTH (dpfx^  th)  val _ = dbgTools.DST (dpfx^  " initset MS_FP\n") (*DBG*)*)
		     in ((X,BddEqMp th (Option.valOf bvtb)),GEN_FP_INIT,
			 if (ttm) then GEN_NU_FP_STATES else GEN_MU_FP_STATES) end
	    else ((initset,initbdd),init_thm,abbrev_thm)
	(*val _ = dbgTools.DTM (dpfx^  initset)  val _ = dbgTools.DST (dpfx^  " initset\n")  (*DBG*)
        val _ = dbgTools.DTM (dpfx^  (getTerm(initbdd)))  val _ = dbgTools.DST (dpfx^  " initbdd\n")  (*DBG*)
	val _ = dbgTools.DTM (dpfx^  imf_t2g)  val _ = dbgTools.DST (dpfx^  " imf_t2g\n") (*DBG*)*)
	(* if ado then we need the old outer env for proving the env legal assumption to the endth *)
	val imf_t2 = Binarymap.find(imf_thms,imf_t2g)
	(*val _ = dbgTools.DTH (dpfx^  imf_t2)  val _ = dbgTools.DST (dpfx^  " imf_t2\n") (*DBG*)
	val _ = if not ado then dbgTools.DTH (dpfx^" abbrev_thm\n"  abbrev_thm)   (*DBG*)
		else dbgTools.DTH (dpfx^" ADO abbrev_thm\n"  abbrev_thm)   (*DBG*)*)
        (* make a term representing the modified environment *)
        val ie1 = list_mk_comb(eus,[ie,t1,initset])
        fun mk_fp n = mk_comb(list_mk_comb(fps,[t2,t1,ksname,ie1]),n)
        val ie2 = list_mk_comb(eus,[ie,t1,mk_fp numSyntax.zero_tm])
        (* create a new RV theorem for this bound var and add it to the spec thms, and add the bv's initbdd to the env *)
        val new_rv_thm = SYM (MP (ISPECL [t2,ksname,ie,t1,state,initset,numSyntax.zero_tm] MS_FP_INIT) wfKS_ks)
	(*val _ = dbgTools.DTH (dpfx^  new_rv_thm)  val _ = dbgTools.DST (dpfx^  " new_rv_thm\n") (*DBG*)*)
        val _ = upd_cch_sth bvch new_rv_thm
        val ix = (Array.length ee) - qd  (* index of current bv in ee and rv_thms arrays *)
	val _ =
	    if (ado)
		then Array.update(ee,ix,(bv,BddEqMp (SYM(MP (ISPECL [t2,ksname,ie,t1,initset,state] init_thm) wfKS_ks))
						    initbdd))
	    else Array.update(ee,ix,(bv,BddEqMp (SYM(MP (ISPECL [t2,ksname,ie,t1,state] init_thm) wfKS_ks)) initbdd))
	val ado_subthm' = if sqd then SOME (lift_ado_sub_thm ado ado_subthm t2 ksname ie1 eeq imf_thms abthm
	    wfKS_ks ie t1 initset seth imf_t2 ess Ss eus adogeneqthm initsubth numSyntax.zero_tm) else NONE
	val _ = profTools.ent (dpfx^"fe")(*PRF*)
        fun iter ie2 n = (* ee also changes with each iter, but statefully, so no need to pass it in *)
          let val _ = dbgTools.DST (dpfx^  ("(iter)\n")) (*DBG*)
	      (*val _ = dbgTools.DTM (dpfx^  t1)  val _ = dbgTools.DST (dpfx^  "::")
	       val _ = dbgTools.DTM (dpfx^  n) (*DBG*)
	       val _ = dbgTools.DTM (dpfx^  ie2)  val _ = dbgTools.DST (dpfx^  " ie2\n") (*DBG*)*)
	      val _ = profTools.bgt (dpfx^"fe")(*PRF*)
	      val eeqthm  = if sqd then mk_ado_pre_sub_thm ado ado_subthm t2 ksname ie1 eeq imf_thms abthm wfKS_ks ie t1
		  initset seth imf_t2 ess eus chainth adogeneqthm initsubth
		  (if  (Term.compare(n,numSyntax.zero_tm)=EQUAL) then n else rand n)  else TRUTH
	      val _ = profTools.ent (dpfx^"fe")(*PRF*)
	      (*val _ = dbgTools.DTH (dpfx^  eeqthm)  val _ = dbgTools.DST (dpfx^  " eeqthm\n") (*DBG*)*)
	      val itr = (muCheck_aux ((p_,ap_,rv_,d_,(wfKS_ks,finS,frv_thms,imf_thms,pextth,rvtt,mssth,fps,
						      eus,Ss,ess,statel,ksname,prop_type,ee,qd-1,sqd,ce,
						      ttm::qt,(eeqthm,abthm)::eeq)),
					   (seth,sel,state,ie2)) (List.last (snd(strip_comb mf)))  vm dp f1)
	      val _ = profTools.bgt (dpfx^"fe")(*PRF*)
	      val itrtm = getTerm itr
	      val _ = dbgTools.DTM (dpfx^"fe_itrtm") itrtm (*DBG*)
	      val _ = dbgTools.DTM (dpfx^"fe_n") n (*DBG*)
	      val itrthm = (ISPECL [t2,ksname,ie,t1,state,initset,n] MS_FP)
              val _ = dbgTools.DTH (dpfx^"fe_itrthm")  itrthm (*DBG*)
              val itr = BddEqMp itrthm itr
	      (* if counterexamples/witnesses are turned on, and we are in the outermost fixed point iteration *)
	      val _ = if (Option.isSome (!ce)) andalso ix=0 then ce := SOME (itr::(Option.valOf (!ce))) else ()
	      (*val _ = if (Option.isSome (!ce)) andalso ix=0 then (*DBG*)
	      let val _=dbgTools.DST (dpfx^ "CE len")
		  val _=DMSG(ST((int_to_string(List.length(Option.valOf (!ce))))^"\n"))(*DBG*)
		  val _ = DMSG (BD (getBdd itr))
			  in () end else ()(*DBG*)*)
	      (*val _ = dbgTools.DTM (dpfx^  (getTerm itr))  val _ = dbgTools.DST (dpfx^  " (itr 2)\n") (*DBG*)*)
              val prevbdd = snd(Array.sub(ee,ix))
	      (*val _ = DMSG (BD (getBdd prevbdd)) (*DBG*)
	      val _ = dbgTools.DTM (dpfx^ (getTerm prevbdd))  val _ = dbgTools.DST (dpfx^  " prevbdd\n") (*DBG*)*)
	      val _ = profTools.ent (dpfx^"fe")(*PRF*)
              val res =  let
              val eqq = (bdd.equal (getBdd prevbdd) (getBdd itr))
	      val tttb =
		  if eqq
		  then let
			   val _ = dbgTools.DST (dpfx^"fe_ iter fin calcs") (*DBG*)
			   val _ = profTools.bgt (dpfx^"fe")(*PRF*)
			   val orac_th = REWRITE_RULE [pextth] (GENL statel (BddThmOracle (BddOp(bdd.Biimp,prevbdd,itr))))
			   (*val _ = dbgTools.DTH (dpfx^  orac_th)  val _ = dbgTools.DST (dpfx^  "oracle thm\n") (*DBG*)*)
			   val endth =
			       if ado
				   then let (*FIXME: ADO stuff not lazified yet *)
				            (*val _ = dbgTools.DTH (dpfx^ cabthm)
					     val _ = dbgTools.DST (dpfx^  " ADO cabthm\n") (*DBG*)
					    val _ = dbgTools.DTH (dpfx^ abthm)
					    val _ = dbgTools.DST (dpfx^  " ADO abthm\n") (*DBG*)*)
					    val imf_t2 = PURE_ONCE_REWRITE_RULE [abthm] imf_t2
					    (*val _ = dbgTools.DTH (dpfx^ imf_t2)
					     val _ = dbgTools.DST (dpfx^  " ADO imf_t2\n") (*DBG*)
					    val _ =DMSG(TH (valOf ado_subthm'))
					    val _ =dbgTools.DST (dpfx^" ADO subthm'") (*DBG*)
					    val _=DMSG(TH(valOf ado_eqthm)) val _=DMSG(ST "ADO eqthm\n")(*DBG*)*)
					    val ado_imfth = Binarymap.find(imf_thms,t2)
					    (*val _ = dbgTools.DTH (dpfx^" ADO ado_imfth\n") ado_imfth)   (*DBG*)
					    val _ = dbgTools.DTM (dpfx^ ie) val _ = dbgTools.DST (dpfx^" ADO ie\n")(*DBG*)
					    val _ = dbgTools.DTH (dpfx^" ADO fst hd eeq\n" (fst(hd eeq)))   (*DBG*)*)
					    val adoeqthm2 = MATCH_MP SUBSET_TRANS
						(LIST_CONJ[MATCH_MP EQ_IMP_SUBSET (Option.valOf ado_eqthm),
							   (SPEC (fst (dest_env ie))
							    (MATCH_MP fp2thm
							     (LIST_CONJ [imf_t2,ado_imfth,
									 wfKS_ks,
									 PURE_ONCE_REWRITE_RULE[adogeneqthm](fst(hd eeq))]
						)))])
					    (*val _ = dbgTools.DTH (dpfx^" ADO adoeqthm2\n"  adoeqthm2)  (*DBG*)*)
					    val sabbrev_thm = ISPECL [t2,ksname,ie,n,t1,initset] abbrev_thm
					    (*val _ =dbgTools.DTH (dpfx^" ADO sabbrev_thm\n" sabbrev_thm) (*DBG*)*)
					in PURE_ONCE_REWRITE_RULE [SYM abthm]
					    (MP (MP sabbrev_thm (LIST_CONJ [wfKS_ks,imf_t2,finS,
									    Option.valOf ado_subthm'])) adoeqthm2)
					end
			       else MP (PURE_REWRITE_RULE [SYM abthm] (ISPECL [t2,ksname,ie,n,t1] abbrev_thm))
						    (LIST_CONJ [wfKS_ks,imf_t2])
			   (*val _ = dbgTools.DTH (dpfx^  endth)  val _ = dbgTools.DST (dpfx^  " endth\n") (*DBG*)
			   val _ = dbgTools.DTH (dpfx^  mssth)  val _ = dbgTools.DST (dpfx^  " mssth\n") (*DBG*)*)
			   val t2b = (SYM (PURE_ONCE_REWRITE_RULE [mssth] (AP_THM (MP endth orac_th) state)))
			   (*val _ = dbgTools.DTH (dpfx^  t2b)   val _ = dbgTools.DST (dpfx^  " t2b\n") (*DBG*)*)
			   (* make ado eqthm and sub_thm for next round *)
			   val _ = if sqd then
			       let val t2b' = (CONV_RULE (RHS_CONV (RATOR_CONV (PURE_ONCE_REWRITE_CONV [abthm])))
				       (PEXT (PairRules.PGEN state (BETA_RULE (REWRITE_RULE [IN_DEF,MU_SAT_def] t2b)))))
				   (*val _ = dbgTools.DTH (dpfx^t2b')   val _ = dbgTools.DST (dpfx^  " t2b'\n") (*DBG*)*)
				   val ado_eqthm' = CONV_RULE(RHS_CONV(REWRITE_CONV[MP(ISPECL[t2,ksname,ie,t1] bigthm)
										      wfKS_ks])) t2b'
				   (*val _ = dbgTools.DTH (dpfx^ado_eqthm')
				     val _ = dbgTools.DST (dpfx^" ado_eqthm'\n") (*DBG*)*)
				   val _ = upd_cch_eqth bvch ado_eqthm'
				   (* make ado subthm *)
				   val ado_subthm = mk_ado_sub_thm ado (Option.valOf ado_subthm') t2 ksname ie1 eeq
				       imf_thms abthm wfKS_ks ie t1 initset (rator (getTerm prevbdd)) seth
				       imf_t2 ess eus chainth n
				   val _ = upd_cch_subth bvch ado_subthm
			       in () end else ()
			   (*val _ = dbgTools.DST (dpfx^  bv) (*DBG*)*)
			   val _ = profTools.ent (dpfx^"fe")(*PRF*)
			   val _ = dbgTools.DST (dpfx^"fe_ iter fin done") (*DBG*)
		       in BddEqMp t2b prevbdd end
		  else let val _ = profTools.bgt (dpfx^"fe")(*PRF*)
			   val ie3 = list_mk_comb(eus,[ie,t1,mk_fp(mk_comb(``SUC``,n))])
			   val _ = dbgTools.DTM (dpfx^"fe_ie3") ie3 (*DBG*)
			   val _ = Array.update(ee,ix,(bv,itr))
			   val _ = dbgTools.CBTML (dpfx^"fe_rv_thm_tml") [t2,ie,initset,t1,n]
			   val _ = dbgTools.CBTH (dpfx^"fe_rvtt") rvtt
			   val rv_thm = SYM (SPECL [t2,ie,initset,t1,n] rvtt)
			   val _ = dbgTools.DTH (dpfx^"fe_rv_thm")  rv_thm (*DBG*)
			   val _ = upd_cch_sth bvch rv_thm
			   val _ = profTools.ent (dpfx^"fe")(*PRF*)
			   val _ = dbgTools.DST (dpfx^"fe_ iter end") (*DBG*)
		       in iter ie3 ``SUC ^n`` end
             in tttb end
	  in res end
    val fpres = iter ie2 numSyntax.zero_tm
    val _ = dbgTools.DEX dpfx "fe" (*DBG*)
    in fpres end
  | FixExp  _ _ _ _ _ _ _ _ _ _= Raise Match (* impossible, just here to avoid warning *)

(* init the model *)
fun init_model I1 T1 state vm Ric =
    let val (apl,ks_def,wfKS_ks,RTm,ITdf) = mk_wfKS I1 T1 NONE state vm Ric NONE NONE NONE
    in (apl,ks_def,wfKS_ks,RTm,ITdf) end

(* init model dependent data structures and theorems *)
fun init_thms (apl,ks_def,wfKS_ks) T1 state vm Ric absf = (*FIXME: this becomes very slow for alu 2x2*)
    let
	val _ = dbgTools.DEN dpfx "it" (*DBG*)
	val ksname = lhs(concl ks_def)
	val (prop_ty,st_ty) = get_types ksname
	val st_set_ty = st_ty --> bool
	val state' = mk_primed_state state
	val (st,st') = (strip_pair##strip_pair) (state,state')
        val s2s' = List.map (fn(v,v') => (BddVar true vm v,BddVar true vm v')) (ListPair.zip(st,st'))
	val f_ty = ``:^(prop_ty) mu``
	val env_ty = string_ty --> st_ty --> bool
	val ks_ty = type_of ksname
        val eus = ``ENV_UPDATE:^(ty_antiq(env_ty --> string_ty --> st_set_ty --> env_ty))``
        val fps = ``FP:^(ty_antiq(f_ty --> string_ty --> ks_ty  --> env_ty --> ``:num`` --> st_ty --> bool))``
	val Ss = mk_comb(``KS_S:^(ty_antiq(ks_ty --> st_ty --> bool))``,ksname)
	val ess = ``{}:^(ty_antiq(st_set_ty))``
	val (msp,msa,Tth,(dmdth,boxth),githms) = mk_gen_thms T1 (apl,ks_def,wfKS_ks) state state' st vm
        val mssth = GSYM (SIMP_RULE std_ss [IN_DEF] MU_SAT_def)
	val jf = (fn _ => (GENL [``f:^(ty_antiq(f_ty))``,``e:^(ty_antiq(env_ty))``,
			 ``X:^(ty_antiq(st_set_ty))``,``Q:string``,``n:num``]
				(ISPEC state (GENL [``s:^(ty_antiq(st_ty))``]
			  (SPEC_ALL (MATCH_MP  (SIMP_RULE std_ss [MS_FP] (GEN_ALL (SIMP_RULE std_ss [ENV_UPDATE]
				(ISPECL [``f:(^(ty_antiq(f_ty)))``,``Q:string``,``ks:^(ty_antiq(type_of ksname))``,
					 ``e[[[Q<--X]]]:(^(ty_antiq(env_ty)))``] SAT_RV_ENV_SUBST)))) wfKS_ks))))))
	val rvtt = mk_lthm (fn _ =>
	    (list_mk_forall([``f:^(ty_antiq(f_ty))``,``e:^(ty_antiq(env_ty))``,``X:^(ty_antiq(st_set_ty))``,
			       ``Q:string``,``n:num``],
				  mk_eq(``MU_SAT (RV Q) ^ksname e[[[Q<--FP f Q ^ksname e[[[Q<--X]]] (SUC n)]]] ^state``,
					``FP f Q ^ksname  e[[[Q<--X]]] (SUC n) ^state``)),jf)) jf
	val _ = dbgTools.DTH (dpfx^"it_rvtt") rvtt  (*DBG*)
        val pextth = GSYM (CONV_RULE (STRIP_QUANT_CONV (RHS_CONV commonTools.lzELIM_TUPLED_QUANT_CONV))
				     (ONCE_REWRITE_RULE [(lzGEN_PALPHA_CONV state  (rhs(concl(SPEC_ALL(INST_TYPE
									[alpha|->st_ty,beta |->bool] FUN_EQ_THM)))))]
				       (INST_TYPE [alpha |-> st_ty, beta |-> bool] FUN_EQ_THM)))
	val _ = dbgTools.DTH (dpfx^"it_pextth") pextth (*DBG*)
	val fS = mk_comb (inst [alpha |-> type_of state] pred_setSyntax.finite_tm,mk_ks_dot_S ksname)
	val jf = fn _ => (prove(fS(*``FINITE (^ksname).S``*),PROVE_TAC [wfKS_def,wfKS_ks,
									BOOLVEC_UNIV_FINITE_CONV (List.length st)]))
        val finS = mk_lthm (fn _ => (fS(*``FINITE (^ksname).S``*),jf)) jf
	val _ = dbgTools.DEX dpfx "it" (*DBG*)
    in ((msp,(msa,absf,ksname), (Tth,(dmdth,boxth),st',s2s'),(finS,pextth,rvtt,mssth,fps,eus,Ss,ess,st,prop_ty)),
	state,githms)
    end

(* init data structures and theorems that depend on the property and environment *)
fun init_prop (nf,mf) ee ksname state wfKS_ks vm githms msp prop_ty =
    let val _ = dbgTools.DEN dpfx "ip" (*DBG*)
	val mf = inst [alpha |-> prop_ty] mf (* it is possible that mf 's type var has not been instantiated *)
	val sqd = ((sameq_depth mf)=2) (* whether or not ado will be enabled at all *)
	val rvl = Array.foldr (fn((rv,tb),l)=> (rv,getTerm tb)::l) [] ee
        val st_ty = type_of state
	val f_ty = ``:^(prop_ty) mu``
	val env_ty = list_mk_fun([string_ty,st_ty],bool)
	val ie =  if (List.null rvl) then (``EMPTY_ENV:^(ty_antiq(env_ty))``) else mk_env rvl state
	val _ = profTools.bgt (dpfx^"init_prop_rv")(*PRF*)
	val (msr,(seth,sel),msreq) = mk_gen_rv_thms mf ksname state rvl ie wfKS_ks
	val _ = profTools.ent (dpfx^"init_prop_rv")(*PRF*)
	val _ = profTools.bgt (dpfx^"init_prop_imf")(*PRF*)
        (*val _ = prove (``IMF ^mf``, REWRITE_TAC ([IMF_def,MU_SUB_def,NNF_def,RVNEG_def]@(tsimps "mu") @ sel)) *)
	val _ = if is_valid mf then () else failwith ("Bound variable occurs negatively:"^(term_to_string mf))
	val _ = profTools.ent (dpfx^"init_prop_imf")(*PRF*)
        val qd = qdepth mf
        val ee2 = Array.array((Array.length ee)+qd,("dummy",BddCon true vm))
	val _ = Array.copy {src=ee,dst=ee2,di=0}
	(*val tmr2 = Timer.startRealTimer()(*PRF*)*)
	val (mfml,imf_thms,frv_thms) = mk_cache ee ie (nf,mf) mf qd githms state (seth,sel) msp
	(*val _ = Binarymap.app (fn (k,v) => let val _ = dbgTools.DTM (dpfx^  k)  (*DBG*)
						 val _ = dbgTools.DST (dpfx^  " key\n")  (*DBG*)
						 val _ = dbgTools.DTH (dpfx^  v) (*DBG*)
						 val _ = dbgTools.DST (dpfx^  " v\n")  (*DBG*)
                                             in () end) frv_thms val _ = dbgTools.DST (dpfx^  " frv_thms\n") (*DBG*)*)
	val _ = profTools.bgt (dpfx^"init_prop_adoimf")(*PRF*)
	val imf_thms = mk_ado_imf_thms mf seth (tsimps ``:'a mu``) frv_thms imf_thms
	val _ = profTools.ent (dpfx^"init_prop_adoimf")(*PRF*)
	(*val _ = Binarymap.app (fn (k,v) => let val _ = dbgTools.DTM (dpfx^k) (*DBG*)
						 val _ = dbgTools.DST (dpfx^  " key\n")  (*DBG*)
						 val _ = dbgTools.DTH (dpfx^  v)  (*DBG*)
						 val _ = dbgTools.DST (dpfx^  " v\n")  (*DBG*)
                                             in () end) imf_thms val _ = dbgTools.DST (dpfx^  " imf_thms\n") (*DBG*)*)
        (*val _ = dbgTools.DST (dpfx^ (Time.toString(Timer.checkRealTimer tmr2)))  (*PRF*)	*)
	val _ = dbgTools.DEX dpfx "ip" (*DBG*)
    in (ie,(msr,seth,sel,msreq,ee2),mfml,imf_thms,frv_thms,qd,sqd,mf) end

(* init data structures and theorems used by model checker *)
fun init I1 T1 state vm Ric ce (nf,mf) ee absf {ks=model_data,th=init_data} =
    let val _ = dbgTools.DEN dpfx "init" (*DBG*)
	val _ = profTools.bgt (dpfx^"init")(*PRF*)
	val _ = profTools.bgt (dpfx^"init_mod")(*PRF*)
	val (apl,ks_def,wfKS_ks,RTm,ITdf) = if Option.isSome model_data then Option.valOf model_data
				       else init_model I1 T1 state vm Ric
	val _ = profTools.ent (dpfx^"init_mod")(*PRF*)
	val _ = if Option.isSome init_data then dbgTools.DST (dpfx^"init_ isSome") (*DBG*)
		else dbgTools.DST (dpfx^"init_ no init data")(*DBG*)
	val _ = profTools.bgt (dpfx^"init_thm")(*PRF*)
	val ((msp,(msa,absf,ksname),(Tth,(dmdth,boxth),st',s2s'),
	      (finS,pextth,rvtt,mssth,fps,eus,Ss,ess,st,prop_ty)),state,githms) =
	if Option.isSome init_data then Option.valOf init_data else init_thms (apl,ks_def,wfKS_ks) T1 state vm Ric absf
	val _ = profTools.ent (dpfx^"init_thm")(*PRF*)
	val _ = profTools.bgt (dpfx^"init_prop")(*PRF*)
	val (ie,(msr,seth,sel,msreq,ee2),mfml,imf_thms,frv_thms,qd,sqd,mf) =
	    init_prop (nf,mf) ee ksname state wfKS_ks vm githms msp prop_ty
	val _ = profTools.ent (dpfx^"init_prop")(*PRF*)
	val ce = if not (Option.isSome (!ce)) andalso is_existential mf
		 then ref (SOME []) else ce (*turn on witness trace if existential mf*)
	val _ = profTools.ent (dpfx^"init")(*PRF*)
	val _ = dbgTools.DEX dpfx "init" (*DBG*)
    in ({ks=SOME (apl,ks_def,wfKS_ks,RTm,ITdf),th=SOME((msp,(msa,absf,ksname),(Tth,(dmdth,boxth),st',s2s'),
	      (finS,pextth,rvtt,mssth,fps,eus,Ss,ess,st,prop_ty)),state,githms)},
	(msp,
	 (msa,absf,ksname),
	 (msr,seth,msreq,ee2),
	 (RTm,Tth,(dmdth,boxth),st',s2s'),
	 (wfKS_ks,finS,frv_thms,imf_thms,pextth,rvtt,mssth,fps,eus,Ss,ess,st,ksname,prop_ty,ee2,qd,sqd,ce,[],[])),
	(ks_def,mf,seth,sel,ie,mfml,frv_thms,ce))
    end

(* make final adjustments to result of model checking run
   such as unwinding any contractions and other syntactic rearrangements of the formula *)
fun finish tb frv_thms =
    let
	val _ = dbgTools.DEN dpfx "fin" (*DBG*)
	val unfrv = BddApConv (ONCE_REWRITE_CONV [frv_find frv_thms (List.hd(snd(strip_comb(getTerm tb))))]) tb
	val _ = dbgTools.DEX dpfx "fin" (*DBG*)
    in unfrv end

(* given the list of top-level approximations, find a path through them and return it as a trace *)
(* see 31 July 2005 notes on how this works *)
(* FIXME: a more readable trace would only print  out those AP's that are talked about in the corresponding property *)
(* FIXME: need to extend this to work with properties other than EF f (i.e. EG f)
   problem with EG is that right now it will giv the shortest path it can find, whereas I feel that
   for EG the longest path is what is needed *)
(* FIXME: in amba_ahb, the ctl_grant2 property will fail if the outer EF is replaced by AG
          that is fine. however, the ce computation fails because the last outermost approximation does not contain
          any initial state. This is not possible in theory, so points to some problem with the ce machinery*)
fun makeTrace mf state vm mu_init_data ce Itb =
    let val _ = dbgTools.DEN dpfx "mt" (*DBG*)
	val _ = dbgTools.DTM (dpfx^"mt_state") state (*DBG*)
	val vmc = List.foldl (fn (v,bm) => Binarymap.insert(bm,v,Binarymap.find(vm,v))) (Binarymap.mkDict String.compare)
			     (List.map term_to_string2 (strip_pair state))
	val _ = List.app (fn (k,v) => dbgTools.DST (dpfx^"mt_vmc:"^(k^","^(int_to_string v)))) (Binarymap.listItems vmc)
	val cel = Option.valOf (!ce)
	val Ib = getBdd Itb
	val _ = dbgTools.DBD (dpfx^"mt_Ib") Ib(*DBG*)
	val _ = List.app (dbgTools.DBD (dpfx^"mt_cel") o getBdd) cel(*DBG*)
	val _ = dbgTools.DNM (dpfx^"mt_cel_sz") (List.length cel)(*DBG*)
	val gfp = is_nu (NNF mf)
	val res =
	    if (List.length cel <= 1)
	    then (*no outermost fp (|cel|=0) or the outermost fp comp terminated immediately (|cel|=1),
		  so tr is empty: any initial state is the ce *)
		[pt_bdd2state state vmc (bddTools.mk_pt Ib vmc)]
	    else let
		    val trbl = List.map getBdd (List.tl cel) (* list of outermost fp computation's approximations *)
		    val _ = dbgTools.DNM (dpfx^"mt_trbl_sz") (List.length trbl)(*DBG*)
		    val _ = List.app (dbgTools.DBD (dpfx^"mt_trbl")) trbl(*DBG*)
		    val Rb = getBdd(Binarymap.find(#4(Option.valOf (#ks(mu_init_data))),".")) (*#4 is RTm*)
		    fun has_to b1 b2 = (* those states in b1 that have a transition to b2 *)
			let val im = bddTools.mk_next state Rb vm b1 (* image of b1 under R. *)
			    (*preimg of img cut to b2 is all source states *)
			    val pi = bddTools.mk_prev state Rb vm (bdd.AND(im,b2)) (*  FIXME: is im superfluous here? *)
			in bdd.AND(pi,b1) end (* cut down source states to the ones in b1 *)
		    fun mk_tr (apx::trl) prev = (* trace out a path of transitions over trbl *)
			if not (isSome prev)
			then let val prev = if gfp
					    then SOME (bddTools.mk_pt Ib vmc)
					    else if not (bdd.equal bdd.FALSE (bdd.AND(apx,Ib)))
					         then SOME (bddTools.mk_pt (bdd.AND(apx,Ib)) vmc)
					         else NONE
			     in if isSome prev
				then (valOf prev)::mk_tr (apx::trl) prev
				else mk_tr trl prev
			     end
			else if (List.length trl)=1
		             then if gfp then []
				         else (bddTools.mk_pt (hd trl) vmc)::[]
			     else let val napx =
					  if gfp then bdd.DIFF(hd trl,apx)
					  else bdd.DIFF(hd trl,List.nth(trl,1))
				  in (*next state on the trace*)
				      let val s1 = mk_pt (bdd.AND(napx,bddTools.mk_next state Rb vm (valOf prev))) vmc
				      in s1::(mk_tr trl (SOME s1)) end
				  end
		      | mk_tr [] prev = Raise Match (* this should not happen. Put here to avoid compiler warning *)
		    val tr = if (List.length trbl)=1
			     then let val s1 = bddTools.mk_pt Ib vmc in [s1](*::(mk_tr trbl s1)*) end
			     (*bddTools.mk_pt (List.hd trbl) vmc] *)
			     else mk_tr trbl NONE
				 (*let val s1 = bddTools.mk_pt (bdd.AND(List.hd trbl,Ib)) vmc
				   in s1::(mk_tr (List.tl trbl) s1) end *)
		    val _ = List.app (dbgTools.DBD (dpfx^"mt_tr")) tr(*DBG*)
		    val trace = List.map (pt_bdd2state state vmc) tr
		    val _ = List.app (dbgTools.DTM (dpfx^"mt_trace")) trace(*DBG*)
		in trace end
	val _ = dbgTools.DEX dpfx "mt" (*DBG*)
    in res end


					(*  (* no outgoing trans from current ce so return this *)
					  if bdd.equal bdd.FALSE (has_to prev napx)
					  then []
					  else*)

(* try and prove that M |= f i.e. initial states are contained in the term-bdd returned by muCheck *)
fun checkResult tb mf ks_def (I1,Itb,ITdf) state ie vm =
    let
	val _ = dbgTools.DEN dpfx "cr" (*DBG*)
	val ksname = lhs(concl ks_def)
	val _ = dbgTools.DTB (dpfx^"cr_tb")  tb (*DBG*)
	val _ = dbgTools.DBD (dpfx^"cr_tb_bdd")  (getBdd tb) (*DBG*)
	(*val _ = dbgTools.DTM (dpfx^  (getTerm tb))  val _ = dbgTools.DST (dpfx^  " tb\n") (*DBG*)
	val _ = List.app (fn t => let val _ = dbgTools.DTM (dpfx^ t) val _ =  dbgTools.DST (dpfx^" tb assum\n") in () end)
	    (HOLset.listItems (getAssums tb))(*DBG*)*)
	val Itb = if Option.isSome Itb then Option.valOf Itb else BddEqMp (SYM (fst (valOf ITdf))) (t2tb vm I1)
	val _ = dbgTools.DTB (dpfx^"cr_Itb")  Itb (*DBG*)
	val _ = dbgTools.DBD (dpfx^"cr_Itb_bdd")  (getBdd Itb)
	val sIth = CONV_RULE (RHS_CONV (ONCE_REWRITE_CONV [GSYM SPECIFICATION]))
			     (lzPBETA_RULE (AP_THM (SYM (lzPBETA_RULE
					 (let val jf = (fn _ => (SIMP_CONV std_ss [KS_accfupds,combinTheory.K_DEF,ks_def]
									   (mk_ks_dot_S0 ksname)))
					  in mk_lthm (fn _ =>  (mk_eq((mk_ks_dot_S0 ksname),
								      getS0 (rhs(concl ks_def))),jf)) jf
					  end)))
				  state))
	val _ = dbgTools.DTH (dpfx^"cr_sIth")  sIth (*DBG*)
	val Itb2 = BddEqMp sIth Itb
	val _ = dbgTools.DTB (dpfx^"cr_Itb2")  Itb2 (*DBG*)
	val Itb3 = (BddOp(bdd.Imp,Itb2,tb))
	val _ = dbgTools.DTB (dpfx^"cr_Itb3")  Itb3 (*DBG*)
	val _ = dbgTools.DBD (dpfx^"cr_Itb3_bdd")  (getBdd Itb3)
	(*val _ = dbgTools.DTM (dpfx^  (getTerm Itb3))  val _ = dbgTools.DST (dpfx^  " Itb3\n") (*DBG*)
	  val _ = List.app (fn t=> let val _= dbgTools.DTM (dpfx^t) val _ = dbgTools.DST (dpfx^" Itb3 assum\n") in () end)
	    (HOLset.listItems (getAssums Itb3))(*DBG*)*)
	val tb1 = BddForall (strip_pair state) Itb3
	(*val _ = dbgTools.DTM (dpfx^  (getTerm tb1))  val _ = dbgTools.DST (dpfx^  " tb1\n") (*DBG*)*)
	val mms = CONV_RULE (RHS_CONV lzELIM_TUPLED_QUANT_CONV) (CONV_RULE (RHS_CONV (lzGEN_PALPHA_CONV state))
							       (ISPECL [mf,ksname,ie] MU_MODEL_SAT_def))
	val _ = dbgTools.DTH (dpfx^"cr_mms") mms (*DBG*)
	val tb2 =  BddEqMp (SYM mms) tb1
	val _ = dbgTools.DTB (dpfx^"cr_tb2") tb2 (*DBG*)
	val _ = dbgTools.DBD (dpfx^"cr_tb2_bdd")  (getBdd tb2)
	val tbth = SOME (BddThmOracle tb2) handle ex => NONE (* exception means failure *)
	val _ = dbgTools.DEX dpfx "cr" (*DBG*)
    in (tbth,SOME Itb) end

(* T1 is map from name of action -> corresponding term (of the action considered as a transition relation)
   ee is 'environment' i.e. vector of (RV, corresponding termbdd) pairs (termbdd is of set of states assigned to this RV)
   I is thm def of init state needed to compute the varsets for BddRules.BddExistsAnd, and termbdd replacement op
   mf is the mu formula to be checked
   absf is an optional abstraction function
   OUT: termbdd of set of states satisfying mf, success theorem, ce/witness trace, cache of reusable stuff *)
fun muCheck ee I1 T1 state vm Ric ce (absf,Itb) ic (nf,mf) =
    let val _ = dbgTools.DEN dpfx "mc" (*DBG*)
	val _ = profTools.bgt (dpfx^"mc")(*PRF*)
	val (ic,init_stuff,(ks_def,mf,seth,sel,ie,mfml,frv_thms,ce')) = init I1 T1 state vm Ric ce (nf,mf) ee absf ic
	val tb = muCheck_aux (init_stuff,(seth,sel,state,ie)) mf vm ((Array.length ee)-1) mfml
        val res_tb = finish tb frv_thms
	val (res_thm,Itb) = if Option.isSome (!ce)
			    then (NONE,Itb) (* in ce gen mode, so result is unimportant *)
			    else checkResult res_tb mf ks_def (I1,Itb,#5(valOf(#ks(ic)))) state ie vm
	val _ = profTools.ent (dpfx^"mc")(*PRF*)
	val trace = get_trace ce ce' res_thm ic ee I1 T1 state vm Ric (absf,Itb) ic (nf,mf)
	val _ = dbgTools.DEX dpfx "mc" (*DBG*)
   in ((res_tb,res_thm,trace),ic) end (* ic can then be passed in as ic next time *)

(* find counterexample/create witness... *)
(* FIXME: only tested for AG/EF properties so far, probably needs fixing to work for other properties *)
(* FIXME thmfy the returned list ... right now a buggy HolCheck can announce false counterexamples *)
(* FIXME will this work if ce is a loop i.e. if some initial state is reachable from a non-initial one? *)
and get_trace ce ce' res_thm ic Ree I1 T1 state vm Ric (absf,Itb) mu_init_data (nf,mf) =
    let
	val _ = dbgTools.DEN dpfx "gc" (*DBG*)
	val trace = if Option.isSome (!ce)
		    then NONE (* already in ce mode, called from previous get_trace, which will now use the ref ce *)
		    else
			if is_universal mf
			then
			    if Option.isSome res_thm then NONE
			    else if is_traceable (NNF mf)
			    then let val ce = ref (SOME []) (* compute counterexample *)
				     (* model check the neg of f and save all top-level approximations in the ref ce*)
				     val _ = muCheck Ree I1 T1 state vm Ric ce (absf,Itb) mu_init_data
						     (nf^"trace",(NNF(mu_neg mf)))
				     val trace =  makeTrace mf state vm mu_init_data ce (valOf Itb)
				 in SOME trace end
			    else NONE (* universal but ce not computable*)
			else
			    if Option.isSome res_thm andalso is_traceable (NNF mf)
			    then SOME(makeTrace mf state vm ic ce' (valOf Itb))(*return witness*)
			    else NONE (* existential but false or untraceable, so no witness *)
	val _ = dbgTools.DEX dpfx "gc" (*DBG*)
    in trace end


(* FIXME: uncomment once trace gen is fixed.
(* get trace and convert to trace of action names*)
fun findTraceNames RTm Ree I1 T1 state vm Ric mf (absf,Itb) mu_init_data =
    let val tr = get_ce Ree I1 T1 state vm Ric (absf,Itb) mu_init_data mf
	val RTm = #4(Option.valOf (#ks(mu_init_data)))
        val (actns,dotactn) = List.partition (fn (nm,_) => not (String.compare(nm,".")=EQUAL)) (Binarymap.listItems RTm)
        val (acts,acttbl) = ListPair.unzip (actns@dotactn) (* thus giving "." action last priority when pattern matching*)
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
*)

end
end




