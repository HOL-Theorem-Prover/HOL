
structure cacheTools =
struct

local

open Globals HolKernel Parse

open bossLib pairTheory pred_setTheory pred_setLib stringLib
     listTheory simpLib pairSyntax pairLib PrimitiveBddRules
     DerivedBddRules Binarymap PairRules pairTools boolSyntax Drule
     Tactical Conv Rewrite Tactic boolTheory listSyntax stringTheory
     boolSimps pureSimps listSimps numLib

open setLemmasTheory muSyntax muSyntaxTheory muTheory reachTheory
     stringBinTree bddTools envTheory envTools muTools cacheTheory
     commonTools lazyTools

val dpfx = "ct_"

structure Polyhash =
struct
   fun peek (ref dict,cmp) k = Binarymap.peek(dict,k)
   fun peekInsert (r as ref dict, cmp) (k,v) =
       case Binarymap.peek(dict,k) of
         NONE => (r := Binarymap.insert(dict,k,v); NONE)
       | x => x
   fun insert (r as ref dict, cmp) (k,v) =
       r := Binarymap.insert(dict,k,v)
   fun listItems (ref dict, cmp) = Binarymap.listItems dict
   fun map f (ref dict, cmp) = let
     fun foldthis (k,v,acc) = Binarymap.insert (acc, k, f (k,v))
   in
     (ref (Binarymap.foldl foldthis (Binarymap.mkDict cmp) dict), cmp)
   end
   fun find (ref dict, cmp) k = Binarymap.find(dict, k)

   fun mkDict cmp = (ref (Binarymap.mkDict cmp), cmp)
end

in

(* given f e and e', proves |- !Q. if ~(SUBFORMULA (~RV Q) (NNF f) then e Q = e' Q else e Q SUBSET e' Q where
   e is the env for the previous iteration and e' is the env for the current iteration
   seth are the string equality theorems required for evaluating the envs *)
fun ITER_ENV_LEGAL_CONV t2 t1 e e' seth state ksname ttm imf_thms imf_t2 frv_thms wfKS_ks abthm cabthm eeq =
    let
	val _ = dbgTools.DEN dpfx "ielc" (*DBG*)
        (* FIXME: need to have unwound version of t2 for passing to NNF_RVNEG_CONV but this could have efficiency issues *)
	val gl = ``!Q'. if (SUBFORMULA (~(RV Q')) (NNF ^t2)) then (^e) Q' = (^e') Q' else (^e) Q' SUBSET (^e') Q'``;
	(*val _ = dbgTools.DTM (dpfx^  t2)  val _ = dbgTools.DST (dpfx^  " ielc t2\n") (*DBG*)*)
        val th1 = PURE_ONCE_REWRITE_RULE [cabthm] (NNF_RVNEG_CONV t2)
	(*val _ = dbgTools.DTH (dpfx^   th1)  val _ = dbgTools.DST (dpfx^  " ielc th1\n") (*DBG*)
	val _ = dbgTools.DTM (dpfx^  gl)  val _ = dbgTools.DST (dpfx^  " ielc goal\n") (*DBG*)
	val _ = dbgTools.DTM (dpfx^  e )  val _ = dbgTools.DST (dpfx^  " ielc env\n") (*DBG*)
	val _ = dbgTools.DTM (dpfx^  e')  val _ = dbgTools.DST (dpfx^  " ielc env'\n") (*DBG*)*)
	val gl1 = (REWRITE_CONV [ENV_CASES,th1] THENC REPEATC (SIMP_CONV (bool_ss ++ boolSimps.COND_elim_ss) [SUBSET_REFL])) gl;
	(*val _ = dbgTools.DTM (dpfx^  (rhs(concl gl1)))  val _ = dbgTools.DST (dpfx^  " ielc second goal \n") (*DBG*)*)
	val res =  if (Term.compare(rhs(concl gl1),T)=EQUAL) then ONCE_REWRITE_RULE [EQ_CLAUSES] gl1
		   else let val env_seq_thms = List.map fst eeq
			in SIMP_RULE bool_ss env_seq_thms gl1 end
	(*val _ = dbgTools.DTH (dpfx^   res)  val _ = dbgTools.DST (dpfx^  " ielc res\n") (*DBG*)*)
	val _ = dbgTools.DEX dpfx "ielc" (*DBG*)
    in res end

(* show that term of conjuncts of the form e[q<--x] p = e'[q<--x] p can be mapped to conjuncts e p = e'p
either because q != p or if q=p then that particular conjunct becomes true and disappears *)
fun mk_ante_eq_thm goal seth =
    let val _ = dbgTools.DEN dpfx "maet"(*DBG*)
        val _ = dbgTools.DTM (dpfx^"maet_gl") goal(*DBG*)
        val goals = strip_conj goal
	val thms = List.map (fn g => let (*val _ = dbgTools.DTM (dpfx^ g)  val _ = dbgTools.DST (dpfx^ " goal\n") (*DBG*)*)
					 val (glhs,grhs) = dest_eq g
					 (*val _ = dbgTools.DTM (dpfx^ glhs)  val _ = dbgTools.DST (dpfx^" glhs\n") (*DBG*)
					 val _ = dbgTools.DTM (dpfx^grhs)  val _ = dbgTools.DST (dpfx^ " grhs\n") (*DBG*)*)
					 val (lenv,p) = dest_comb glhs
					 val (renv,_) = dest_comb grhs
					 val ll1 = snd(strip_comb lenv)
					 val le = List.nth(ll1,0)
					 val q = List.nth(ll1,1)
					 val x = List.nth(ll1,2)
					 val ll2 = snd(strip_comb renv)
					 val re = List.nth(ll2,0)
					 val ps = fromHOLstring p val qs = fromHOLstring q
					 val seqthm = Binarymap.find(Binarymap.find(seth,qs),ps)
					 (*val _ = dbgTools.DTH (dpfx^seqthm) (*DBG*) *)
					 val eqth = GEN_ALL(List.hd(List.tl(CONJUNCTS(SPEC_ALL EQ_CLAUSES))))
					 val eqth1 =  if (is_neg (concl seqthm)) then eqth else ISPEC (fst(dest_eq(concl seqthm))) eqth
					 (*val _ = dbgTools.DTH (dpfx^ eqth) (*DBG*)*)
					 val seqthm = if (is_neg (concl seqthm)) then seqthm else PURE_ONCE_REWRITE_RULE [eqth1] seqthm
					 (*val _ = dbgTools.DTH (dpfx^   seqthm)  (*DBG*)*)
					 val envth = if (String.compare(qs,ps)=EQUAL) then ENV_EVAL_EQ_INV else ENV_EVAL_NEQ_INV
					 (*val _ = dbgTools.DTH (dpfx^   (ISPECL [le,re,q,p,x] envth))
                                           val _ = dbgTools.DST (dpfx^  " envth\n") (*DBG*)*)
					 val th = MP (ISPECL [le,re,q,p,x] envth) seqthm
				     in if (is_neg(concl seqthm)) then th
					else PURE_ONCE_REWRITE_RULE [ISPEC (concl th) (GSYM eqth)] th end) goals
	(*val _ = List.app (fn tt => dbgTools.DTH (dpfx^"maet_sethm")  tt)) thms(*DBG*)*)
	val thl = List.map (fn (g,th) => PURE_ONCE_REWRITE_CONV [th] g) (ListPair.zip(goals,thms))
	(*val _ = List.app (fn tt => let val _ = dbgTools.DTH (dpfx^"maet_sethm2"  tt)  in () end) thl(*DBG*)*)
        val _ = dbgTools.DEX dpfx "maet"(*DBG*)
    in thl end

fun mk_inv_zero_ante speclist spec_thm mp_thm  =
    let
	val _ = dbgTools.DEN dpfx "i0" (*DBG*)
	val _ = profTools.bgt (dpfx^"i0")(*PRF*)
	(*val _ = dbgTools.DTH (dpfx^   spec_thm)  val _ = dbgTools.DST (dpfx^  " spec_thm\n") (*DBG*)
	val _ = dbgTools.DTH (dpfx^   mp_thm)  val _ = dbgTools.DST (dpfx^  " mp_thm\n") (*DBG*)
	val _ = List.app (fn tt=> let val _= dbgTools.DTM (dpfx^ tt)  in () end) speclist(*DBG*) *)
        val (l,bod) = strip_forall (concl spec_thm)
	val jf = (fn _ => MATCH_MP (CONV_RULE FORALL_IMP_CONV ((CONV_RULE (LAST_FORALL_CONV FORALL_IMP_CONV))
									   (ISPECL speclist spec_thm))) mp_thm)
	val th = mk_lthm (fn _ => (list_mk_forall(List.drop(l,List.length speclist),
					    subst (List.map (fn (f,r) => (f|->r)) (ListPair.zip(l,speclist))) (rand bod)),jf)) jf
	(*val _ = dbgTools.DTH (dpfx^   th)  val _ = dbgTools.DST (dpfx^  " th\n") (*DBG*)*)
	val _ = profTools.ent (dpfx^"i0")(*PRF*)
	val _ = dbgTools.DEX dpfx "i0" (*DBG*)
    in th end

fun mk_inv_one_ante args cthm tthm ithm left =
 let val _ = dbgTools.DEN dpfx "i1" (*DBG*)
     val _ = profTools.bgt (dpfx^"i1")(*PRF*)
     (*val _ = dbgTools.DTM (dpfx^  (List.hd args))  val _ = dbgTools.DST (dpfx^  " hd args\n") (*DBG*)
     val _ = dbgTools.DTM (dpfx^  (List.last args))  val _ = dbgTools.DST (dpfx^  " last args\n") (*DBG*)
     val _ = dbgTools.DTH (dpfx^   cthm)  val _ = dbgTools.DST (dpfx^  " cthm\n") (*DBG*)
     val _ = dbgTools.DTH (dpfx^   tthm)  val _ = dbgTools.DST (dpfx^  " tthm\n") (*DBG*)
     val _ = dbgTools.DTH (dpfx^   ithm)  val _ = dbgTools.DST (dpfx^  " ithm\n") (*DBG*)*)
     val (ante,tc) = dest_imp(snd(strip_forall(concl cthm)))
     val (l,bod) = strip_forall (concl ithm)
     val jf = (fn _ => let val (ql,t) = strip_forall(concl tthm)
			   val tthm2 = prove(list_mk_forall(ql,mk_imp(ante,t)),SIMP_TAC std_ss [tthm])
			   (*val _ = dbgTools.DTH (dpfx^   tthm2)  val _ = dbgTools.DST (dpfx^  " tthm2\n") (*DBG*)*)
			   val th2 = CONV_RULE (QUANT_CONV AND_FORALL_CONV)
					       (CONV_RULE AND_FORALL_CONV (LIST_CONJ (if left then [cthm,tthm2] else [tthm2,cthm])))
			   (*val _ = dbgTools.DTH (dpfx^   th2)  val _ = dbgTools.DST (dpfx^  " th2\n") (*DBG*)*)
			   val th3 = MATCH_MP (ISPECL ([ante,ante]@(if left then [tc,t] else [t,tc])) fol1) (SPEC_ALL th2)
			   (*val _ = dbgTools.DTH (dpfx^   th3)  val _ = dbgTools.DST (dpfx^  " th3\n") (*DBG*)*)
			   val th4 = SIMP_RULE bool_ss [] (GENL [List.hd ql,List.last ql] th3)
			   (*val _ = dbgTools.DTH (dpfx^   th4)  val _ = dbgTools.DST (dpfx^  " th4\n") (*DBG*)*)
                           val geninv = (ISPECL [List.hd args,List.last args, List.hd ql,List.last ql] ithm)
                           (*val _ = dbgTools.DTH (dpfx^   geninv)  val _ = dbgTools.DST (dpfx^  " geninv\n") (*DBG*)*)
                           val sfol = ISPECL (ante::((if left then [tc,t] else [t,tc])@[snd(dest_imp(concl geninv))])) fol3
                           (*val _ = dbgTools.DTH (dpfx^   sfol)  val _ = dbgTools.DST (dpfx^  " sfol\n") (*DBG*)*)
                           val th5 = MATCH_MP  sfol geninv
			   (*val _ = dbgTools.DTH (dpfx^   th5)  val _ = dbgTools.DST (dpfx^  " th5\n")  (*DBG*)*)
                           val th6 = MATCH_MP th5 (SPEC_ALL th4)
                           (*val _ = dbgTools.DTH (dpfx^   th6)  val _ = dbgTools.DST (dpfx^  " th6\n")  (*DBG*)*)
                           val res = GENL [List.hd ql,List.last ql] th6
			   (*val _ = dbgTools.DTH (dpfx^  res)  val _ = dbgTools.DST (dpfx^  " res\n")  (*DBG*)*)
		       in res end)
     val th = mk_lthm (fn _ => (list_mk_forall(List.drop(l,List.length args),
					       mk_imp(ante,subst (List.map (fn (f,r) => (f|->r)) (ListPair.zip(l,args))) (rand bod))),
				jf)) jf
     val _ = profTools.ent (dpfx^"i1")(*PRF*)
     (*val _ = dbgTools.DTH (dpfx^ th)  val _ = dbgTools.DST (dpfx^  " th\n")  (*DBG*)*)
     val _ = dbgTools.DEX dpfx "i1" (*DBG*)
 in th end

fun mk_inv_two_ante args ithml ithm =
    let
	val _ = dbgTools.DEN dpfx "i2" (*DBG*)
	val _ = profTools.bgt (dpfx^"i2")(*PRF*)
	(*val _ = dbgTools.DTM (dpfx^  (List.hd args))  val _ = dbgTools.DST (dpfx^  " hd args\n") (*DBG*)
	val _ = dbgTools.DTM (dpfx^  (List.last args))  val _ = dbgTools.DST (dpfx^  " last args\n") (*DBG*)*)
	val cthm1 = List.hd ithml
        val (ante1,t1) = dest_imp(snd(strip_forall(concl cthm1)))
        val cthm2 = List.last ithml
	(*val _ = dbgTools.DTH (dpfx^  ithm)  val _ = dbgTools.DST (dpfx^  " ithm\n")  (*DBG*)
	val _ = dbgTools.DTH (dpfx^  cthm1)  val _ = dbgTools.DST (dpfx^  " cthm1\n")  (*DBG*)
	val _ = dbgTools.DTH (dpfx^  cthm2)  val _ = dbgTools.DST (dpfx^  " cthm2\n")  (*DBG*)*)
        val (ante2,t2) = dest_imp(snd(strip_forall(concl cthm2)))
	val (l,bod) = strip_forall (concl ithm)
	val jf = (fn _ =>
		     let val (ql,_) = strip_forall(concl cthm1)
			 val th2 = CONV_RULE (QUANT_CONV AND_FORALL_CONV) (CONV_RULE AND_FORALL_CONV (LIST_CONJ [cthm1,cthm2]))
			 val th3 = MATCH_MP (ISPECL [ante1,ante2,t1,t2] fol1) (SPEC_ALL th2)
			 val th4 = (*CONV_RULE (STRIP_QUANT_CONV(LAND_CONV(SIMP_CONV bool_ss [])))*) (GENL ql th3)
			 val geninv = (ISPECL [List.hd args, List.last args,List.hd ql,List.last ql] ithm)
			 val sfol = ISPECL [(*snd(dest_eq(concl(SIMP_CONV bool_ss [] (mk_conj(ante1,ante2))))) handle ex =>*)
					    (mk_conj(ante1,ante2)), t1,t2,snd(dest_imp(concl geninv))] fol3
			 val th5 = MATCH_MP sfol geninv
			 val th6 = MATCH_MP th5 (SPEC_ALL th4)
			 val res = GENL ql th6
		     (*val _ = dbgTools.DTH (dpfx^  res)  val _ = dbgTools.DST (dpfx^  " res\n")  (*DBG*)*)
		     in res end)
	val th = mk_lthm (fn _ => (list_mk_forall(List.drop(l,List.length args),
					 mk_imp(mk_conj(ante1,ante2),
						subst (List.map (fn (f,r) => (f|->r)) (ListPair.zip(l,args))) (rand bod))),jf)) jf
	(*val _ = dbgTools.DTH (dpfx^  th)  val _ = dbgTools.DST (dpfx^  " th\n")  (*DBG*)*)
	val _ = profTools.ent (dpfx^"i2")(*PRF*)
	val _ = dbgTools.DEX dpfx "i2" (*DBG*)
    in th end

fun mk_inv_modal_ante args ithml ithm1 ithm2 chc state env =
    let val _ = dbgTools.DEN dpfx "imod" (*DBG*)
	val _ = profTools.bgt (dpfx^"imod") (*PRF*)
	val res =
	    if (chc=0)
	    then (* child does not have antecedents *)
		let
		    val _ = dbgTools.DST (dpfx^"imod_ modal no ante") (*DBG*)
		    val th =  mk_inv_zero_ante [List.hd args,List.last args] ithm1 (List.hd ithml)
		    val _ = dbgTools.DST (dpfx^"imod_ modal no ante done") (*DBG*)
		in th end
	    else
		let val _ = dbgTools.DST (dpfx^"imod_ modal with ante") (*DBG*)
		    val cthm = List.hd ithml
		    (*val _ = dbgTools.DTH (dpfx^   cthm)  val _ = dbgTools.DST (dpfx^  " cthm\n") (*DBG*)*)
		    val (ante,_) = dest_imp(snd(strip_forall(concl cthm)))
		    val (l,bod) = strip_forall (concl ithm2)
		    val jf = (fn _ =>
				 let val (ql,_) = strip_forall(concl cthm)
				     val geninv = ISPECL [List.hd args,List.last args,List.hd ql,List.last ql] ithm2
				     (*val _ = dbgTools.DTH (dpfx^"imod_ ithm2") ithm2 (*DBG*)
				       val _ = dbgTools.DTH (dpfx^"imod_ geninv") geninv)  (*DBG*)*)
				     val tc3 = fst(dest_imp(concl geninv))
				     val sfol = ISPECL [ante,tc3,snd(dest_imp(concl geninv))] fol5
				     (*val _ = dbgTools.DTH (dpfx^   sfol)  val _ = dbgTools.DST (dpfx^  " sfol\n") (*DBG*)*)
				     val th1 = MATCH_MP sfol geninv
				     (*val _ = dbgTools.DTH (dpfx^   th1)  val _ = dbgTools.DST (dpfx^  " th1\n") (*DBG*)*)
				     val cth2 = SPEC_ALL cthm
				     (*val _ = dbgTools.DTH (dpfx^   cth2)  val _ = dbgTools.DST (dpfx^  " cth2\n") (*DBG*)*)
				     val th2 = MATCH_MP th1 cth2
				     (*val _ = dbgTools.DTH (dpfx^   th2)  val _ = dbgTools.DST (dpfx^  " th2\n") (*DBG*)*)
				     val res =GENL [``e:^(ty_antiq(type_of env))``,``e':^(ty_antiq(type_of env))``] th2
				 (*val _ = dbgTools.DTH (dpfx^  res)  val _ = dbgTools.DST (dpfx^  " res\n") (*DBG*)*)
				 in res end)
		    val th = mk_lthm (fn _ => (list_mk_forall(List.drop(l,List.length args),
						     mk_imp(ante,subst (List.map (fn (f,r) => (f|->r))
										 (ListPair.zip(l,args))) (rand bod))),jf)) jf
		    val _ = dbgTools.DST (dpfx^"imod_ modal with ante done") (*DBG*)
		in th end
	val _ = profTools.ent (dpfx^"imod")(*PRF*)
	val _ = dbgTools.DEX dpfx "imod" (*DBG*)
    in res end

fun remove_bv ante bv = (* ante is e Q = e' Q /\ e P = e' P ... term, bv is current bound var *)
    let val eqs = strip_conj ante
        val ante' = List.filter (fn el => not (Term.compare(snd(dest_comb(fst(dest_eq el))),bv)=EQUAL)) eqs
    in if (List.null ante') then T else list_mk_conj ante' end

fun mk_inv_fp_ante args ithml ithm chc state seth  =
    let
	val _ = dbgTools.DEN dpfx "ifp" (*DBG*)
	val _ = profTools.bgt (dpfx^"ifp")(*PRF*)
	val th = if (chc=0) (* child does not have antecedents *)
		 then
		     let val _ = dbgTools.DST (dpfx^"ifp_ mk_inv_fp_ante no ante") (*DBG*)
                         val cthm = List.hd ithml
			 (*val _ =  dbgTools.DTH (dpfx^   ithm)  val _ = dbgTools.DST (dpfx^  " ithm\n") (*DBG*)
			 val _ =  DMSG(TM(List.hd args))  val _ = dbgTools.DST (dpfx^ " hd args\n") (*DBG*)
			 val _=  DMSG(TM(List.last args)) val _=dbgTools.DST (dpfx^" last args\n") (*DBG*)*)
			 val (l,bod) = strip_forall (concl ithm)
			 val jf = (fn _ => let val (ql,_) = strip_forall(concl cthm)
					       (*val _ = with_flag (show_types,true) DMSG(TM(List.hd ql))  *)
					       (*val _ = dbgTools.DST (dpfx^ " hd ql\n") (*DBG*)*)
					       (*val _ = with_flag(show_types,true) DMSG(TM(List.last ql))  *)
					       (*val _ =dbgTools.DST (dpfx^ " last ql\n") (*DBG*)*)
					       val geninv = ISPECL [List.hd args, List.last args,List.hd ql,List.last ql] ithm
					       (*val _ = dbgTools.DTH (dpfx^ geninv) val _ = dbgTools.DST (dpfx^  " geninv\n") (*DBG*)*)
			                       val X = ``X: ^(ty_antiq(type_of state --> bool))``
					       val cthm2 = ISPECL [``^(List.hd ql)[[[^(List.hd args)<--^X]]]``,
								      ``^(List.last ql)[[[^(List.hd args)<--^X]]]``] cthm
					       (*val _ = dbgTools.DTH (dpfx^  cthm2)  val _ = dbgTools.DST (dpfx^  " cthm2\n") (*DBG*)*)
			                       val cthm3 =  (GEN X cthm2)
					       val th1 = GENL [List.hd ql, List.last ql] (MATCH_MP geninv cthm3)
					       val _ = dbgTools.DST (dpfx^"ifp_ mk_inv_fp_ante no ante done") (*DBG*)
					   in th1 end)
			 val th = mk_lthm (fn _ => (list_mk_forall(List.drop(l,List.length args),
							  subst (List.map (fn (f,r) => (f|->r))
								 (ListPair.zip(l,args))) (rand bod)),jf)) jf
		     in th end
		 else
		     let val _ = dbgTools.DST (dpfx^"ifp_ mk_inv_fp_ante yes ante") (*DBG*)
			 val cthm = List.hd ithml
			 (*val _ = dbgTools.DTH (dpfx^   cthm)  val _ = dbgTools.DST (dpfx^  " cthm\n") (*DBG*)*)
			 val (ql,_) = strip_forall(concl cthm)
			 val (ante,_) = dest_imp(snd(strip_forall(concl cthm)))
			 val ante1 = remove_bv ante (List.hd args)
			 val X = ``X: ^(ty_antiq(mk_type("fun",[type_of state,``:bool``])))``
			 val cthm2 = ISPECL [``^(List.hd ql)[[[^(List.hd args)<--^X]]]``,
						``^(List.last ql)[[[^(List.hd args)<--^X]]]``] cthm
			 (*val _ = dbgTools.DTH (dpfx^   cthm2)  val _ = dbgTools.DST (dpfx^  " cthm2\n") (*DBG*)*)
			 val (sante,_) = dest_imp(snd(strip_forall(concl cthm2))) (* no need to remove_bv; mk_ante_eq takes care of it*)
			 val geninv = ISPECL [List.hd args, List.last args,List.hd ql,List.last ql] ithm
			 (*val _ = dbgTools.DTH (dpfx^   geninv)  val _ = dbgTools.DST (dpfx^  " geninv\n") (*DBG*)*)
			 val tc3 = fst(dest_imp(concl geninv))
			 val _ = dbgTools.DST (dpfx^"ifp_ mk_inv_fp_ante yes ante done") (*DBG*)
		     in if (Term.compare(ante1,T)=EQUAL)
			then (* no antecedents left, remove completely; this happens if bv was the only sub-RV *)
			    let
				val (l,bod) = strip_forall (concl ithm)
				val jf = (fn _ => let val noantethm = mk_ante_eq_thm sante seth
						      val cthm3 = SIMP_RULE std_ss noantethm cthm2
						      val cthm4 = (GEN X cthm3)
						      (*val _ = dbgTools.DTH (dpfx^   cthm4)  (*DBG*)*)
					              val th1 = GENL [List.hd ql, List.last ql] (MATCH_MP geninv cthm4)
						  in th1 end)
				val th = mk_lthm (fn _ => (list_mk_forall(List.drop(l,List.length args),
								 subst (List.map (fn (f,r) => (f|->r))
										    (ListPair.zip(l,args))) (rand bod)),jf)) jf
			    in th end
			else (* antecedents still left; ripple to current inv thm *)
			    let val (l,bod) = strip_forall (concl ithm)
				val jf = (fn _ => let val sfol = ISPECL [ante1,tc3,snd(dest_imp(concl geninv))] fol5
						      val th1 = MATCH_MP sfol geninv
						      val ae = mk_ante_eq_thm sante seth
						      val cthm3 = REWRITE_RULE ae cthm2
						      val cthm4 =  (CONV_RULE FORALL_IMP_CONV (GEN X cthm3))
						      val th2 = MATCH_MP th1 cthm4
						      val res = GENL ql th2
						  in res end)
				val th = mk_lthm (fn _ => (list_mk_forall(List.drop(l,List.length args),
								 mk_imp(ante1,subst (List.map (fn (f,r) => (f|->r))
										    (ListPair.zip(l,args))) (rand bod))),jf)) jf
			    in th end
		     end
	(*val _ = dbgTools.DTH (dpfx^  th)  val _ = dbgTools.DST (dpfx^  " final th\n") (*DBG*)*)
	val _ = profTools.ent (dpfx^"ifp")(*PRF*)
	val _ = dbgTools.DEX dpfx "ifp" (*DBG*)
    in th end

(* return NONE if entire list is NONE, else a list of just the thms*)
fun merge_abthms abthml = List.map Option.valOf (List.filter Option.isSome abthml)

fun mk_inv_thm opr args env ithml (githms as [AP_I,RV_I,T_I,F_I,NEG_I,NEG_I2,CONJ_I,CONJ_I2,DISJ_I,DISJ_I2,DMD_I,DMD_I2,BOX_I,BOX_I2,LFP_I,LFP_I2,GFP_I,GFP_I2]) state chc (msp as [MU_SAT_T,MU_SAT_F,MU_SAT_NEG,MU_SAT_CONJ,MU_SAT_DISJ]) seth =
    let val _ = dbgTools.DEN dpfx "mit" (*DBG*)
        val _ = profTools.bgt (dpfx^"mit")(*PRF*)
	val res = case (fst (dest_const opr)) of
            "AP"      => let (*val _ = with_flag(show_types,true) dbgTools.DTH (dpfx^   AP_I)  (*DBG*)
			     val _ = dbgTools.DST (dpfx^  " (AP_I)\n") (*DBG*)
			     val _ = with_flag(show_types,true)dbgTools.DTM (dpfx^  (List.hd args)) (*DBG*)
			     val _ = dbgTools.DST (dpfx^  " (hd args)\n") (*DBG*) *)
			 in ISPEC (List.hd args) AP_I end
          | "RV"      => ISPEC (List.hd args) RV_I (* note this is not used if this RV is current bound *)
          | "And"     => (case chc of (* 0=neither child has antecedents, 1=left child, 2= right, 3 = both *)
                             0 => mk_inv_zero_ante [List.hd args, List.last args] CONJ_I (LIST_CONJ ithml)
                           | 1 => mk_inv_one_ante args (List.hd ithml) (List.last ithml) CONJ_I2 true
                           | 2 => mk_inv_one_ante args (List.last ithml) (List.hd ithml) CONJ_I2 false
                           | 3 => mk_inv_two_ante args ithml CONJ_I2
                           | _ => Raise Match )
          | "Or"      =>  (case chc of (* 0=neither child has antecedents, 1=left child, 2= right, 3 = both *)
                             0 => mk_inv_zero_ante [List.hd args, List.last args] DISJ_I (LIST_CONJ ithml)
                           | 1 => mk_inv_one_ante args (List.hd ithml) (List.last ithml) DISJ_I2 true
                           | 2 => mk_inv_one_ante args (List.last ithml) (List.hd ithml) DISJ_I2 false
                           | 3 => mk_inv_two_ante args ithml DISJ_I2
                           | _ => Raise Match)
          | "Not"     => if (chc=0)
                         then (* child does not have antecedents *)
                             let val _ = profTools.bgt (dpfx^"ineg")(*PRF*)
				 val res = mk_inv_zero_ante [List.hd args] NEG_I (List.hd ithml)
				 val _ = profTools.ent (dpfx^"ineg")(*PRF*)
			     in res end
                         else
                             let val _ = profTools.bgt (dpfx^"ineg")(*PRF*)
				 val cthm = List.hd ithml
                                 val (ante,tc) = dest_imp(snd(strip_forall(concl cthm)))
				 val (l,bod) = strip_forall (concl NEG_I2)
				 val jf = (fn _ => let val (ql,_) = strip_forall(concl cthm)
						       val geninv = ISPECL [List.hd args,List.hd ql,List.last ql] NEG_I2
						       val sfol = ISPECL [ante,tc,snd(dest_imp(concl geninv))] fol5
						       val th1 = MATCH_MP sfol geninv
						       val th2 = MATCH_MP th1 (SPEC_ALL cthm)
						       val th3 =GENL[``e:^(ty_antiq(type_of env))``,``e':^(ty_antiq(type_of env))``] th2
					      in th3 end)
				 val th = mk_lthm (fn _ => (list_mk_forall(List.drop(l,List.length args),
								  mk_imp(ante,subst (List.map (fn (f,r) => (f|->r))
										     (ListPair.zip(l,args))) (rand bod))),jf)) jf
				 val _ = profTools.ent (dpfx^"ineg")(*PRF*)
                                 (*val _ = dbgTools.DTH (dpfx^  th)  val _ = dbgTools.DST (dpfx^  " Not th\n") (*DBG*)*)
                             in th end
          | "TR"      => T_I
          | "FL"      => F_I
          | "DIAMOND" => mk_inv_modal_ante args ithml DMD_I DMD_I2 chc state env
          | "BOX"     => mk_inv_modal_ante args ithml BOX_I BOX_I2 chc state env
          | "mu"      => mk_inv_fp_ante args ithml LFP_I2 chc state seth
          | "nu"      => mk_inv_fp_ante args ithml GFP_I2 chc state seth
          | _         => Raise Match
        val _ = profTools.ent (dpfx^"mit")(*PRF*)
	val _ = dbgTools.DEX dpfx "mit" (*DBG*)
    in res end
| mk_inv_thm _ _ _ _ _ _ _ _ _  = Raise Match

fun print_rsc rsc label = let
in
  print (label^" rsc ");
  Vector.appi (fn (i,iv) => print (Int.toString i^":"^
                                   Int.toString(Vector.sub(rsc,i))^" "))
              rsc;
  print "\n"
end

fun is_eq_rsc rsc rsc' =
    let val _ = profTools.bgt (dpfx^"ier")(*PRF*)
	val res = List.foldl (fn (i,t) => t andalso Vector.sub(rsc,i)=Vector.sub(rsc',i)) true (List.tabulate(Vector.length rsc,I))
	val _ = profTools.ent (dpfx^"ier")(*PRF*)
    in res end

(* cache entry is (term_bdd,gth,sth,env for which sth and tb are valid, index of RV tb if any else -1,
reverse scope of bound RV, environment invariance thm for this node, abbrev thm for this node, ado sub thm, ado eq thm *)
fun cache_add depth rvnm2ix env (nf,mf) mfo ce rsc rvty ithml (githms as [_,_,T_I,F_I,_,_,_,_,_,_,_,_,_,_,_,_,_,_])
	      state seth msp guid abthml (cons as (ctm,dtm,ntm,dmdtm,boxtm,rvtm,mutm,nutm,imftm)) =
    let val _ = dbgTools.DEN dpfx "ca" (*DBG*)
        val _ = profTools.bgt (dpfx^"ca")(*PRF*)
        val _ = profTools.bgt (dpfx^"ca_init")(*PRF*)
        val _ = profTools.bgt (dpfx^"ca_init_irv")(*PRF*)
	val irv = is_RV mf
        val _ = profTools.ent (dpfx^"ca_init_irv")(*PRF*)
        val _ = profTools.bgt (dpfx^"ca_init_mrv")(*PRF*)
	val cekey = if irv then mk_comb(rvtm, (fromMLstring((fromHOLstring(rand mf))^(int_to_string depth)))) else mf
	(*mu_RV (type_of state) (fromMLstring((fromHOLstring(rand mf))^(int_to_string depth))) else mf*)
        val _ = profTools.ent (dpfx^"ca_init_mrv")(*PRF*)
	(*val _ = dbgTools.DTM (dpfx^  cekey)  val _ = dbgTools.DST (dpfx^  " cekey\n") (*DBG*)*)
	val _ = profTools.bgt (dpfx^"ca_init_bmp")(*PRF*)
	val en = Polyhash.peek ce cekey(*Redblackmap.peek(ce,cekey)*)
	val _ = profTools.ent (dpfx^"ca_init_bmp")(*PRF*)
        (*val _ = dbgTools.DTM (dpfx^  mf)  val _ = dbgTools.DST (dpfx^  " mf\n") (*DBG*)*)
	fun same_rsc rsc en = let val (_,_,_,_,_,rsc',_,_,_,_) = !(Option.valOf en) in is_eq_rsc rsc rsc' end
        val _ = profTools.ent (dpfx^"ca_init")(*PRF*)
    (* if not RV then must agree on reverse scope otherwise (say) <.> Q and <.> Q in different scopes would be identified *)
    (* reverse scoping for RV's is more complicated, so it is quicker to just cache on name+depth (a la de Bruijn) to tell them apart *)
	val res =
	    if (Option.isSome en) andalso (is_RV mf orelse same_rsc rsc en) then
	      let
                val (_,_,_,_,_,rsc,ithm,abthm,_,_) = !(Option.valOf en)
		val _ = dbgTools.DST (dpfx^"ca_ already cached") (*DBG*)
	      in
                (Option.valOf en,(ce,rsc,ithm,abthm))
              end
	    else let
                fun mk_abbr rhs = let
                  val _ = profTools.bgt (dpfx^"ca_ma")(*PRF*)
		  val df = mk_adf (nf^(int_to_string (!guid))) rhs (* fast abbrev definition *)
	          val _ = (guid := (!guid)+1)
		  val _ = profTools.ent (dpfx^"ca_ma")(*PRF*)
		in
                  df
                end
	        val (opr,args) = strip_comb mf
	        val (_,argso) = strip_comb mfo
                val (en,rsc,ithm,abthm) =
                    case (fst (dest_const opr)) of
                      "AP"      => let
                        val _ = profTools.bgt (dpfx^"ca_ap")(*PRF*)
			val abthm = REFL mf
			val _ = profTools.ent (dpfx^"ca_ap")(*PRF*)
			val ithm = mk_inv_thm opr args env ithml githms
                                              state 0 msp seth
                      in
                        (ref (NONE,NONE,NONE,env,~1,rsc,ithm,SOME abthm,
                              NONE,NONE),rsc,ithm,SOME abthm)
                      end
                    | "RV"      => let
                        val _ = profTools.bgt (dpfx^"ca_rv")(*PRF*)
			val rv = snd(dest_comb mf)
                        (*val _ = dbgTools.DST (dpfx^ ("RV")) ; val _ = dbgTools.DST (dpfx^ (fromHOLstring rv)) ;(*DBG*)
                         val _ = List.app (fn (b,i) =>
					      let val _ = dbgTools.DST (dpfx^  (b^"::"^(int_to_string i)^"\n"))  in () end)
                                          (rvnm2ix)(*DBG*)*)
                        val ix =  commonTools.listkeyfind
                                    rvnm2ix
                                    (fromHOLstring rv)
                                    String.compare
                        val rsc =
                            Vector.mapi
			      (fn (i,v)=> if (i=ix) then let
                                              val ty = commonTools.listkeyfind
                                                         rvty rv Term.compare
					    in
                                               if ty then 2 else 1
					    end handle NotFound => 0
					  else v)
                              rsc
                        (*val _ = print_rsc rsc "RV cache_add depth"*)
			val abthm = REFL mf
			val _ = profTools.ent (dpfx^"ca_rv")(*PRF*)
                        val ithm = mk_inv_thm opr args env ithml githms
                                              state 0 msp seth
                      in
                        (ref (NONE,SOME TRUTH,NONE,env,ix,rsc,ithm,SOME abthm,
                              NONE,NONE),rsc,ithm,SOME abthm)
                      end
                    | "And"     => let
                        val _ = dbgTools.DST (dpfx^  "ca_ And") (*DBG*)
                        (*val _ = dbgTools.DTH (dpfx^   CONJ_I) (*DBG*)*)
                        (*val _ = dbgTools.DST (dpfx^  " gen\n") (*DBG*)*)
			val _ = profTools.bgt (dpfx^"ca_c1")(*PRF*)
                        val chc = (if (is_imp(snd(strip_forall(concl(List.hd ithml))))) then 1 else 0)
                                  +(if (is_imp(snd(strip_forall(concl(List.last ithml))))) then 2 else 0)
			val lcabthmnm = lhs(concl(Option.valOf(List.hd abthml)))
			val rcabthmnm = lhs(concl(Option.valOf(List.last abthml)))
			val _ = profTools.ent (dpfx^"ca_c1")(*PRF*)
                        val abthm = mk_abbr (list_mk_comb(ctm,[lcabthmnm,rcabthmnm]))
                        val ithm = mk_inv_thm opr [lcabthmnm,rcabthmnm] env ithml githms state chc msp seth
			val _ = profTools.bgt (dpfx^"ca_c2")(*PRF*)
			val ithm = PURE_ONCE_REWRITE_RULE [SYM abthm] ithm
			val _ = profTools.ent (dpfx^"ca_c2")(*PRF*)
                      in
                        (ref (NONE,NONE,NONE,env,~1,rsc,ithm,SOME abthm,
                              NONE,NONE),rsc,ithm,SOME abthm)
                      end
                    | "Or"      => let
                        val _ = dbgTools.DST (dpfx^"ca_ Or") (*DBG*)
                        (*val _ = dbgTools.DTH (dpfx^   DISJ_I) (*DBG*)*)
                        (* val _ = dbgTools.DST (dpfx^  " gen\n") (*DBG*)*)
			val _ = profTools.bgt (dpfx^"ca_d1")(*PRF*)
                        val chc = (if (is_imp(snd(strip_forall(concl(List.hd ithml))))) then 1 else 0)
                                  +(if (is_imp(snd(strip_forall(concl(List.last ithml))))) then 2 else 0)
			val lcabthmnm = lhs(concl(Option.valOf(List.hd abthml)))
			val rcabthmnm = lhs(concl(Option.valOf(List.last abthml)))
			val _ = profTools.ent (dpfx^"ca_d1")(*PRF*)
                        val abthm = mk_abbr (list_mk_comb(dtm,[lcabthmnm,rcabthmnm]))(*``Or(^lcabthmnm)(^rcabthmnm)``*)
                        val ithm = mk_inv_thm opr [lcabthmnm,rcabthmnm] env ithml githms state chc msp seth
			val _ = profTools.bgt (dpfx^"ca_d2")(*PRF*)
			val ithm = PURE_ONCE_REWRITE_RULE [SYM abthm] ithm
			val _ = profTools.ent (dpfx^"ca_d2")(*PRF*)
                      in
                        (ref (NONE,NONE,NONE,env,~1,rsc,ithm,SOME abthm,
                              NONE,NONE),rsc,ithm,SOME abthm)
                      end
                    | "Not"     => let
                        val _ = profTools.bgt (dpfx^"ca_n1")(*PRF*)
			val chc = (if (is_imp(snd(strip_forall(concl(List.hd ithml))))) then 1 else 0)
			val cabthmnm = lhs(concl(Option.valOf(List.hd abthml)))
			val _ = profTools.ent (dpfx^"ca_n1")(*PRF*)
                        val abthm = mk_abbr (mk_comb(ntm,cabthmnm))(*``Not (^cabthmnm)`` *)
                        val ithm = mk_inv_thm opr [cabthmnm] env ithml githms state chc msp seth
			val _ = profTools.bgt (dpfx^"ca_n2")(*PRF*)
			val ithm = PURE_ONCE_REWRITE_RULE [SYM abthm] ithm
			val _ = profTools.ent (dpfx^"ca_n2")(*PRF*)
                      in
                        (ref (NONE,NONE,NONE,env,~1,rsc,ithm,SOME abthm,
                              NONE,NONE),rsc,ithm,SOME abthm)
                      end
                    | "TR"      => (ref (NONE,NONE,NONE,env,~1,rsc,T_I,
                                         SOME (REFL mf),NONE,NONE),rsc,T_I,
                                    SOME (REFL mf))
                    | "FL"      => (ref (NONE,NONE,NONE,env,~1,rsc,F_I,
                                         SOME (REFL mf),NONE,NONE),rsc,F_I,
                                    SOME (REFL mf))
                    | "DIAMOND" => let
                        val _ = dbgTools.DST (dpfx^"ca_ DMD\n") (*DBG*)
                        (*val _ = dbgTools.DTH (dpfx^   DMD_I)  val _ = dbgTools.DST (dpfx^  " gen\n") (*DBG*)*)
			val _ = profTools.bgt (dpfx^"ca_dmd")(*PRF*)
                        val chc = (if (is_imp(snd(strip_forall(concl(List.last ithml))))) then 1 else 0)
			val cabthmnm = lhs(concl(Option.valOf(List.hd abthml)))
			val actnm = List.hd args
			val _ = profTools.ent (dpfx^"ca_dmd")(*PRF*)
                        val abthm = mk_abbr (list_mk_comb(dmdtm,[actnm,cabthmnm]))(*``DIAMOND (^actnm) (^cabthmnm)``*)
                        val ithm = mk_inv_thm opr [List.hd args,cabthmnm] env ithml githms state chc msp seth
			val _ = profTools.bgt (dpfx^"ca_dmd")(*PRF*)
			val ithm = PURE_ONCE_REWRITE_RULE [SYM abthm] ithm
			val _ = profTools.ent (dpfx^"ca_dmd")(*PRF*)
                      in
                        (ref (NONE,NONE,NONE,env,~1,rsc,ithm,SOME abthm,
                              NONE,NONE),rsc,ithm,SOME abthm)
                      end
                    | "BOX"     => let
                        val _ = dbgTools.DST (dpfx^  "ca_ BOX") (*DBG*)
                        (*val _ = dbgTools.DTH (dpfx^   BOX_I)  val _ = dbgTools.DST (dpfx^  " gen\n") (*DBG*)*)
			val _ = profTools.bgt (dpfx^"ca_box")(*PRF*)
                        val chc = (if (is_imp(snd(strip_forall(concl(List.last ithml))))) then 1 else 0)
			val cabthmnm = lhs(concl(Option.valOf(List.hd abthml)))
			val actnm = List.hd args
			val _ = profTools.ent (dpfx^"ca_box")(*PRF*)
                        val abthm = mk_abbr (list_mk_comb(boxtm,[actnm,cabthmnm]))(*``BOX (^actnm) (^cabthmnm)``*)
                        val ithm = mk_inv_thm opr [List.hd args,cabthmnm] env ithml githms state chc msp seth
			val _ = profTools.bgt (dpfx^"ca_box")(*PRF*)
			val ithm = PURE_ONCE_REWRITE_RULE [SYM abthm] ithm
			val _ = profTools.ent (dpfx^"ca_box")(*PRF*)
                      in
                        (ref (NONE,NONE,NONE,env,~1,rsc,ithm,SOME abthm,
                              NONE,NONE),rsc,ithm,SOME abthm)
                      end
                    | "mu"      => let
                        val _ = dbgTools.DST (dpfx^  "ca_ mu") (*DBG*)
                        val _ = profTools.bgt (dpfx^"ca_mu")(*PRF*)
			val chc = (if (is_imp(snd(strip_forall(concl(List.last ithml))))) then 1 else 0)
			val cabthmnm = lhs(concl(Option.valOf(List.hd abthml)))
			val rvnm = List.hd args
                        val _ = profTools.ent (dpfx^"ca_mu")(*PRF*)
                        val abthm = mk_abbr (list_mk_comb(mutm,[rvnm,cabthmnm]))(*``mu (^rvnm) .. (^cabthmnm)``*)
                        val ithm = mk_inv_thm opr [List.hd args,cabthmnm] env
                                              ithml githms state chc msp seth
                        val _ = profTools.bgt (dpfx^"ca_mu")(*PRF*)
			val ithm = PURE_ONCE_REWRITE_RULE [SYM abthm] ithm
                        val _ = profTools.ent (dpfx^"ca_mu")(*PRF*)
                      in
                        (ref (NONE,NONE,NONE,env,~1,rsc,ithm,SOME abthm,
                              NONE,NONE),rsc,ithm,SOME abthm)
                      end
                    | "nu"      => let
                        val _ = dbgTools.DST (dpfx^  "ca_ nu") (*DBG*)
                        val _ = profTools.bgt (dpfx^"ca_nu")(*PRF*)
			val chc = (if (is_imp(snd(strip_forall(concl(List.last ithml))))) then 1 else 0)
			val cabthmnm = lhs(concl(Option.valOf(List.hd abthml)))
			val rvnm = List.hd args
                        val _ = profTools.ent (dpfx^"ca_nu")(*PRF*)
                        val abthm = mk_abbr (list_mk_comb(nutm,[rvnm,cabthmnm]))(*``nu (^rvnm) .. (^cabthmnm)`` *)
                        val ithm = mk_inv_thm opr [List.hd args,cabthmnm] env ithml githms state chc msp seth
                        val _ = profTools.bgt (dpfx^"ca_nu")(*PRF*)
			val ithm = PURE_ONCE_REWRITE_RULE [SYM abthm] ithm
                        val _ = profTools.ent (dpfx^"ca_nu")(*PRF*)
                      in
                        (ref (NONE,NONE,NONE,env,~1,rsc,ithm,SOME abthm,
                              NONE,NONE),rsc,ithm,SOME abthm)
                      end
                    | _         => Raise Match
              in
                let
                  val _ = profTools.bgt(dpfx^"ca_bmi")(*PRF*)
	          val _ = Polyhash.insert ce (cekey,en)(*Redblackmap.insert(ce,cekey,en) *)
	          val _ = profTools.ent(dpfx^"ca_bmi")(*PRF*)
	        in
                  (en,(ce,rsc,ithm,abthm))
                end
	      end
        val _ = profTools.ent (dpfx^"ca")(*PRF*)
	val _ = dbgTools.DEX dpfx "ca" (*DBG*)
    in res end
| cache_add _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = Raise Match

(* take two reverse scopes and merge into one *)
fun rcs_merge r1 r2 =
    Vector.mapi (fn (i,_) => if (Vector.sub(r1,i)>Vector.sub(r2,i)) then
                               Vector.sub(r1,i)
                             else Vector.sub(r2,i))
                (Vector.tabulate(Vector.length r1,fn i => 0))

fun BST_merge b1 b2 = (* merge two binary maps, b2 overwriting b1 in case of key collision *)
    let val _ = profTools.bgt (dpfx^"bstm")(*PRF*)
	val res = Binarymap.foldl (fn (k,v,ab) => Binarymap.insert(ab,k,v)) b1 b2
	val _ = profTools.ent (dpfx^"bstm")(*PRF*)
    in res end

fun PH_merge p1 p2 = (* merge two hashtables, p2 overwriting p1 in case of key collision *)
    let val _ = profTools.bgt (dpfx^"phm")(*PRF*)
	val _ = Polyhash.map (fn (k,v) => Polyhash.peekInsert p2 (k,v)) p1
	val _ = profTools.ent (dpfx^"phm")(*PRF*)
    in p2 end

(* these are place holders for whatever data structure I use to handle the frv abbrev thms*)
val frv_merge = PH_merge(*BST_merge*)
fun frv_insert (s,k,v) = (Polyhash.insert s (k,v); s)(*Binarymap.insert(s,k,v)*)
fun frv_empty ce = Polyhash.mkDict Term.compare
fun frv_find s k = Polyhash.find s k

(* ASSERT: mf = uniq mf (fv mf) [] *)
fun mk_cache_aux ee rvnm2ix env (nf,mf) mfo ce rscope depth rvty githms state seth msp guid tysimps p_ty
  (cons as (ctm,dtm,ntm,dmdtm,boxtm,rvtm,mutm,nutm,imftm)) =
    let
	val _ = dbgTools.DEN dpfx "mca" (*DBG*)
	val (opr,args) = strip_comb mf
	val (opro,argso) = strip_comb mfo
        (*val _ = dbgTools.DTM (dpfx^  mf)  val _ = dbgTools.DST (dpfx^  " mf\n") (*DBG*)*)
        val lab = ""(*DBG*)
	val res =  case (fst(dest_const opr)) of
           "TR" =>let val _ = profTools.bgt (dpfx^"mca_t")(*PRF*)
		      val (pt,(ce1,rsc,ithm,abthm)) = cache_add depth rvnm2ix env (nf,mf) mfo ce rscope rvty []
								githms state seth msp guid [] cons
		      val frv = lhs(concl (Option.valOf abthm))
		      val res = ((muTR pt,
			(Binarymap.mkDict Term.compare),frv_insert(frv_empty ce,frv,Option.valOf abthm)),
		       (ce1,rsc,ithm,abthm,Option.valOf abthm))
		      val _ = profTools.ent (dpfx^"mca_t")(*PRF*)
                  in res end
         | "FL" =>let val _ = profTools.bgt (dpfx^"mca_f")(*PRF*)
		      val (pt,(ce1,rsc,ithm,abthm)) = cache_add depth rvnm2ix env (nf,mf) mfo ce rscope rvty []
								githms state seth msp guid [] cons
		      val frv = lhs(concl (Option.valOf abthm))
		      val res = ((muFL pt,
		       (Binarymap.mkDict Term.compare),frv_insert(frv_empty ce,frv,Option.valOf abthm)),
		       (ce1,rsc,ithm,abthm,Option.valOf abthm))
		      val _ = profTools.ent (dpfx^"mca_f")(*PRF*)
                  in res end
         | "RV" =>let val (pt,(ce1,rsc,ithm,abthm)) = cache_add depth rvnm2ix env (nf,mf) mfo ce rscope rvty []
								githms state seth msp guid [] cons
		      val _ = profTools.bgt (dpfx^"mca_rv")(*PRF*)
		      val frv = lhs(concl (Option.valOf abthm))
		      val res  = ((muRV pt,
		       (Binarymap.mkDict Term.compare),frv_insert(frv_empty ce,frv,Option.valOf abthm)),
		       (ce1,rsc,ithm,abthm,Option.valOf abthm))
		      val _ = profTools.ent (dpfx^"mca_rv")(*PRF*)
                  in res end
         | "AP" =>let val (pt,(ce1,rsc,ithm,abthm)) = cache_add depth rvnm2ix env (nf,mf) mfo ce rscope rvty []
								githms state seth msp guid [] cons
		      val _ = profTools.bgt (dpfx^"mca_ap")(*PRF*)
		      val frv = lhs(concl (Option.valOf abthm))
		      val res = ((muAP pt,
		       (Binarymap.mkDict Term.compare),frv_insert(frv_empty ce,frv,Option.valOf abthm)),
		       (ce1,rsc,ithm,abthm,Option.valOf abthm))
		      val _ = profTools.ent (dpfx^"mca_ap")(*PRF*)
                  in res end
         | "Not" =>let val ((pt1,imfs,abs),(ce1,rsc,ithm,abthm,xabthm)) =
			   mk_cache_aux ee rvnm2ix env (nf,(List.hd args)) (List.hd argso)
					ce rscope depth rvty githms state seth msp guid tysimps p_ty cons
                       val (pt,(ce2,rsc2,ithm,abthm)) = cache_add depth rvnm2ix env (nf,mf) mfo ce1 rsc rvty
								   [ithm] githms state seth msp guid [abthm] cons
		       val _ = profTools.bgt (dpfx^"mca_n")(*PRF*) (* this is here so we don't include the recursive call as part of Not *)
		       val xabthm = PURE_ONCE_REWRITE_RULE [xabthm] (Option.valOf abthm)
		       val abs = frv_insert(abs,lhs(concl (xabthm)),xabthm)
		       val _ = profTools.ent (dpfx^"mca_n")(*PRF*)
                    in ((muNot(pt,pt1),imfs,abs),(ce2,rsc2,ithm,abthm,xabthm)) end
         | "And" =>let val ((ptl,imfsl,absl),(ce1,rsc,it1,ab1,xab1)) =
			   mk_cache_aux ee rvnm2ix env (nf,(List.hd args)) (List.hd argso) ce
                                        rscope depth rvty githms state seth msp guid tysimps p_ty cons
                       val ((ptr,imfsr,absr),(ce2,rsc2,it2,ab2,xab2)) =
			   mk_cache_aux ee rvnm2ix env (nf,(List.last args)) (List.last argso) ce1
					rsc depth rvty githms state seth msp guid tysimps p_ty cons
                       val (pt,(ce3,rsc3,ithm,abthm)) = cache_add depth rvnm2ix env (nf,mf) mfo ce2 (rcs_merge rsc rsc2)
								  rvty [it1,it2] githms state seth msp guid [ab1,ab2] cons
		       val _ = profTools.bgt (dpfx^"mca_c")(*PRF*)
		       val _ = profTools.bgt (dpfx^"mca_c1")(*PRF*)
		       val xabthm = PURE_ONCE_REWRITE_RULE [xab1] (PURE_ONCE_REWRITE_RULE [xab2] (Option.valOf abthm))
		       val _ = profTools.ent (dpfx^"mca_c1")(*PRF*)
		       val _ = profTools.bgt (dpfx^"mca_c2")(*PRF*)
		       val abs = frv_insert(frv_merge absl absr,lhs(concl (xabthm)),xabthm)
		       val _ = profTools.ent (dpfx^"mca_c2")(*PRF*)
		       val _ = profTools.bgt (dpfx^"mca_c3")(*PRF*)
		       val res = ((muAnd(pt,(ptl,ptr)),BST_merge imfsl imfsr,abs),(ce3,rsc3,ithm,abthm,xabthm))
		       val _ = profTools.ent (dpfx^"mca_c3")(*PRF*)
		       val _ = profTools.ent (dpfx^"mca_c")(*PRF*)
                    in res end
         | "Or" =>let val ((ptl,imfsl,absl),(ce1,rsc,it1,ab1,xab1)) =
			  mk_cache_aux ee rvnm2ix env (nf,(List.hd args)) (List.hd argso) ce
                                       rscope depth rvty githms state seth msp guid tysimps p_ty cons
                      val ((ptr,imfsr,absr),(ce2,rsc2,it2,ab2,xab2)) =
			  mk_cache_aux ee rvnm2ix env (nf,(List.last args)) (List.last argso) ce1
                                       rsc depth rvty githms state seth msp guid tysimps p_ty cons
                      val (pt,(ce3,rsc3,ithm,abthm)) = cache_add depth rvnm2ix env (nf,mf) mfo ce2 (rcs_merge rsc rsc2)
								 rvty [it1,it2] githms state seth msp guid [ab1,ab2] cons
		      val _ = profTools.bgt (dpfx^"mca_d")(*PRF*)
		      val xabthm = PURE_ONCE_REWRITE_RULE [xab1] (PURE_ONCE_REWRITE_RULE [xab2] (Option.valOf abthm))
		      val abs = frv_insert(frv_merge absl absr,lhs(concl (xabthm)),xabthm)
		      val res = ((muOr(pt,(ptl,ptr)),BST_merge imfsl imfsr,abs),(ce3,rsc3,ithm,abthm,xabthm))
		      val _ = profTools.ent (dpfx^"mca_d")(*PRF*)
                   in res end
         | "DIAMOND" =>let val ((pt1,imfs,abs),(ce1,rsc,ithm,ab,xab)) =
			       mk_cache_aux ee rvnm2ix env (nf,(List.last args)) (List.last argso) ce
                                            rscope depth rvty githms state seth msp guid tysimps p_ty cons
                           val (pt,(ce2,rsc2,ithm,ab))=cache_add depth rvnm2ix env (nf,mf) mfo ce1 rsc rvty
								 [ithm] githms state seth msp guid [ab] cons
			   val _ = profTools.bgt (dpfx^"mca_dmd")(*PRF*)
			   val xabthm = PURE_ONCE_REWRITE_RULE [xab] (Option.valOf ab)
			   val abs = frv_insert(abs,lhs(concl (xabthm)),xabthm)
			   val res = ((muDIAMOND(pt,(fromHOLstring(List.hd args),pt1)),imfs,abs),(ce2,rsc2,ithm,ab,xabthm))
			   val _ = profTools.ent (dpfx^"mca_dmd")(*PRF*)
                        in res end
         | "BOX" =>let val ((pt1,imfs,abs),(ce1,rsc,ithm,ab,xab)) =
			   mk_cache_aux ee rvnm2ix env (nf,(List.last args)) (List.last argso) ce
                                        rscope depth rvty githms state seth msp guid tysimps p_ty cons
                       val (pt,(ce2,rsc2,ithm,ab))=cache_add depth rvnm2ix env (nf,mf) mfo ce1 rsc rvty
							     [ithm] githms state seth msp guid [ab] cons
		       val _ = profTools.bgt (dpfx^"mca_box")(*PRF*)
		       val xabthm = PURE_ONCE_REWRITE_RULE [xab] (Option.valOf ab)
		       val abs = frv_insert(abs,lhs(concl (xabthm)),xabthm)
		       val res  = ((muBOX(pt,(fromHOLstring(List.hd args),pt1)),imfs,abs),(ce2,rsc2,ithm,ab,xabthm))
		       val _ = profTools.ent (dpfx^"mca_box")(*PRF*)
                    in res end
         | "mu" => let val (ptr,(ce0,rsc,ithm,abthm)) = cache_add (depth+1)
								 ((fromHOLstring(List.hd args),depth)::rvnm2ix)
							 env (nf,(mk_comb(rvtm,List.hd args))) (mk_comb(rvtm,List.hd argso)) ce rscope
								 ((List.hd args,false)::rvty) [] githms state seth msp guid [] cons
                      val ((pt1,imfs,abs),(ce1,rsc,ithm,abthm,xabthm)) =
			    mk_cache_aux ee ((fromHOLstring(List.hd args),depth)::rvnm2ix)
                                         env (nf,(List.last args)) (List.last argso) ce0 rscope (depth+1)
                                         ((List.hd args,false)::rvty) githms state seth msp guid tysimps p_ty cons
		      val _ = profTools.bgt (dpfx^"mca_mu")(*PRF*)
		      val abs = frv_insert(abs,List.last args,xabthm)
		      val _ = profTools.ent (dpfx^"mca_mu")(*PRF*)
                      val (pt,(ce2,rsc2,ithm,abthm)) =
                          cache_add depth rvnm2ix env (nf,mf) mfo ce1
                                    (Vector.mapi (fn (i,v) => if (i=depth) then
                                                                0
                                                              else v)
                                                 rsc)
                                    rvty [ithm] githms state seth msp guid
                                    [abthm] cons
		      val _ = profTools.bgt (dpfx^"mca_mu")(*PRF*)
		      val xabthm = PURE_ONCE_REWRITE_RULE [xabthm] (Option.valOf abthm)
		      val imfth = PURE_ONCE_REWRITE_RULE [SYM xabthm] (mk_imf_thm imftm mf tysimps p_ty)
		      val abs = frv_insert(abs,lhs(concl (xabthm)),xabthm)
		      val res = ((fpmu(ptr,pt,pt1),Binarymap.insert(imfs,mf,imfth),abs),(ce2,rsc2,ithm,abthm,xabthm))
		      val _ = profTools.ent (dpfx^"mca_mu")(*PRF*)
		      val _ = dbgTools.DST (dpfx^  "mu done\n")
                    in res end
         | "nu" => let val (ptr,(ce0,rsc,ithm,abthm)) = cache_add (depth+1)
							     ((fromHOLstring(List.hd args),depth)::rvnm2ix)
                                              env (nf,(mk_comb(rvtm,List.hd args))) (mk_comb(rvtm,List.hd argso)) ce rscope
                                              ((List.hd args,true)::rvty) [] githms state seth msp guid [] cons
                       val ((pt1,imfs,abs),(ce1,rsc,ithm,abthm,xabthm)) =
			    mk_cache_aux ee ((fromHOLstring(List.hd args),depth)::rvnm2ix)
                                         env (nf,(List.last args)) (List.last argso) ce0 rscope (depth+1)
                                         ((List.hd args,true)::rvty) githms state seth msp guid tysimps p_ty cons
		       val _ = profTools.bgt (dpfx^"mca_nu1")(*PRF*)
		       val abs = frv_insert(abs,List.last args,xabthm)
		       val _ = profTools.ent (dpfx^"mca_nu1")(*PRF*)
                       val (pt,(ce2,rsc2,ithm,abthm)) =
                           cache_add depth rvnm2ix env (nf,mf) mfo ce1
                                     (Vector.mapi (fn (i,v) => if (i=depth) then
                                                                 0
                                                               else v)
                                                  rsc)
                                     rvty [ithm] githms state seth msp
                                     guid [abthm] cons
		       val _ = profTools.bgt (dpfx^"mca_nu2a")(*PRF*)
		       val xabthm = PURE_ONCE_REWRITE_RULE [xabthm] (Option.valOf abthm)
		       val _ = profTools.ent (dpfx^"mca_nu2a")(*PRF*)
		       val _ = profTools.bgt (dpfx^"mca_nu2b")(*PRF*)
		       val imfth = PURE_ONCE_REWRITE_RULE [SYM xabthm] (mk_imf_thm imftm mf tysimps p_ty)
		       val _ = profTools.ent (dpfx^"mca_nu2b")(*PRF*)
		       val _ = profTools.bgt (dpfx^"mca_nu3")(*PRF*)
		       val abs = frv_insert(abs,lhs(concl (xabthm)),xabthm)
		       val res = ((fpnu(ptr,pt,pt1),Binarymap.insert(imfs,mf,imfth),abs),(ce2,rsc2,ithm,abthm,xabthm))
		       val _ = profTools.ent (dpfx^"mca_nu3")(*PRF*)
		       val _ = dbgTools.DST (dpfx^  "nu done\n")
                    in res  end
         | _         => failwith ("mk_cache_aux Match:"^(term_to_string mf))
	val _ = dbgTools.DEX dpfx "mca" (*DBG*)
    in res end


(*FIXME: this still takes a significant portion of the time *)
fun mk_cache ee env (nf,mf) mfo qd githms state (seth,sel) msp =
    let val _ = dbgTools.DEN dpfx "mc" (*DBG*)
	(*val _ = dbgTools.DTM (dpfx^  mf) *)(*DBG*)
	val _ = profTools.bgt (dpfx^"mc")(*PRF*)
        (* make a mapping from rv's to their index in ee *)
	val rvnm2ix = fst(Array.foldl(fn ((k,tb),(l,n)) => ((k,n)::l,n+1)) ([],0) ee)
        val p_ty = get_prop_type mf
	val res = fst (mk_cache_aux ee rvnm2ix env (nf^"frv",mf) mfo
				    (Polyhash.mkDict Term.compare)
				    (Vector.tabulate(qd+(List.length rvnm2ix),fn ix => 0))
				    (List.length rvnm2ix)
				    []  githms state seth msp (ref 0)
				    (mk_tysimps sel p_ty)
				    p_ty
				    (get_mu_ty_conj_tm p_ty,get_mu_ty_disj_tm p_ty,get_mu_ty_neg_tm p_ty,
				     get_mu_ty_dmd_tm p_ty,get_mu_ty_box_tm p_ty,get_mu_ty_rv_tm p_ty,
				     get_mu_ty_mu_tm p_ty,get_mu_ty_nu_tm p_ty,inst [alpha |-> p_ty] mu_imf_tm)
				    )
	val _ = profTools.ent (dpfx^"mc")(*PRF*)
	val _ = dbgTools.DEX dpfx "mc" (*DBG*)
    in res end


fun upd_cch_tb cch tb = let val (a,b,c,d,e,f,g,h,i,j) = !cch in (cch:=(SOME tb,b,c,d,e,f,g,h,i,j)) end
fun upd_cch_gth cch gth = let val (a,b,c,d,e,f,g,h,i,j) = !cch in (cch:=(a,SOME gth,c,d,e,f,g,h,i,j)) end
fun upd_cch_sth cch sth = let val (a,b,c,d,e,f,g,h,i,j) = !cch in (cch:=(a,b,SOME sth,d,e,f,g,h,i,j)) end
fun upd_cch_env cch env = let val (a,b,c,d,e,f,g,h,i,j) = !cch in (cch:=(a,b,c,env,e,f,g,h,i,j)) end
fun upd_cch_subth cch subth = let val (a,b,c,d,e,f,g,h,i,j) = !cch in (cch:=(a,b,c,d,e,f,g,h,SOME subth,j)) end
fun upd_cch_eqth cch eqth = let val (a,b,c,d,e,f,g,h,i,j) = !cch in (cch:=(a,b,c,d,e,f,g,h,i,SOME eqth)) end

fun mk_ado_sub_thm ado ado_subthm t2 ksname ie1 eeq imf_thms abthm wfKS_ks ie t1 initset finset seth imf_t2 ess eus chainth n =
    let
	(* make ado sub_thm i.e.initset SUBSET STATES f ks e[[[Q<--initset]]],used to discharge GEN_MU_FP_STATES *)
	val _ = dbgTools.DEN dpfx "as" (*DBG*)
	(*val _ = dbgTools.DTM (dpfx^  initset)  val _ = dbgTools.DST (dpfx^  " ADO initset\n") (*DBG*)
	val _ = dbgTools.DTM (dpfx^  finset)  val _ = dbgTools.DST (dpfx^  " ADO finset\n") (*DBG*)*)
        val res = if (Term.compare(initset,finset)=EQUAL) then ado_subthm
	   else
	       let
		   val n = rand finset
		   (*val _ = dbgTools.DTH (dpfx^" spec glc")   (ISPECL [t2,ksname,ie,n,t1,initset] chainth)) (*DBG*)
 		   val _ = dbgTools.DTH (dpfx^   ado_subthm)  val _ = dbgTools.DST (dpfx^  " prev ado_subthm\n") (*DBG*)*)
		   val ado_subthm = (MP (ISPECL [t2,ksname,ie,n,t1,initset] chainth)
					(LIST_CONJ [wfKS_ks,PURE_ONCE_REWRITE_RULE [abthm] imf_t2,ado_subthm]))
		   val ado_subthm'' = CONV_RULE (RAND_CONV(ONCE_REWRITE_CONV [STATES_def]
									     THENC REWRITE_CONV [ENV_EVAL,ENV_UPDATE])) ado_subthm
	   (*val _ = dbgTools.DTH (dpfx^   ado_subthm'')   val _ = dbgTools.DST (dpfx^  " init ado_subthm\n") (*DBG*)*)
	       in ado_subthm'' end
	val _ = dbgTools.DEX dpfx "as" (*DBG*)
    in res end

fun lift_ado_sub_thm ado ado_subthm t2 ksname ie1 eeq imf_thms abthm wfKS_ks ie t1 initset seth imf_t2 ess
		     Ss eus adogeneqthm initsubth n =
    let
	(* make ado sub_thm i.e.initset SUBSET STATES f ks e[[[Q<--initset]]],used to discharge GEN_MU_FP_STATES *)
	val _ = dbgTools.DEN dpfx "al" (*DBG*)
	(*val _ = dbgTools.DTM (dpfx^  initset)  val _ = dbgTools.DST (dpfx^  " ADOlift initset\n") (*DBG*)*)
	val n = if ((Term.compare(initset,ess)=EQUAL) orelse (Term.compare(initset,Ss)=EQUAL)) then numSyntax.zero_tm else rand initset
	val prev_adosubthm = if ado then (Option.valOf ado_subthm)
			     else (ISPEC ``STATES ^t2 ^ksname ^ie1`` initsubth)
	(*val _ = dbgTools.DTH (dpfx^   prev_adosubthm)  val _ = dbgTools.DST (dpfx^  " ADOlift prev ado_subthm\n")  (*DBG*)
        val _ = if (not (null eeq)) then dbgTools.DTH (dpfx^  (fst (hd eeq)))  else dbgTools.DST (dpfx^  "empty")  (*DBG*)
	val _ = dbgTools.DST (dpfx^  " ADOlift hd eeq\n")  (*DBG*) *)
        val ado_subthm =
	    if ado then
		let
		    (*val _ = dbgTools.DTM (dpfx^  t2)  val _ = dbgTools.DST (dpfx^  " ADOlift t1\n") (*DBG*)
		    val _ = dbgTools.DTH (dpfx^ (Binarymap.find(imf_thms,t2)))  (*DBG*)
 		    val _ = dbgTools.DTH (dpfx^   (snd(hd eeq)))  val _ = dbgTools.DST (dpfx^  " ADOlift prev ab th\n") (*DBG*)
		    val _ = dbgTools.DTH (dpfx^   abthm)  val _ = dbgTools.DST (dpfx^  " ADOlift curr ab th\n") (*DBG*)*)
		    val prevth = MATCH_MP STATES_MONO_EQ
			(LIST_CONJ [wfKS_ks,PURE_ONCE_REWRITE_RULE [snd(hd eeq)] (Binarymap.find(imf_thms,t2)),
				    PURE_ONCE_REWRITE_RULE [adogeneqthm] (fst(hd eeq))])
		    (*val _ = dbgTools.DTH (dpfx^   prevth)  val _ = dbgTools.DST (dpfx^  " ADOlift prev th\n") (*DBG*)*)
                    val (ie0,(t1o,_)) = dest_env ie
		    val ie0' = list_mk_comb(eus,[ie0,t1,initset])
		    val prevth2 = REWRITE_RULE [MATCH_MP ENV_SWAP (Binarymap.find(Binarymap.find(seth,fromHOLstring t1),
										  fromHOLstring t1o))] (SPEC ie0' prevth)
		    (*val _ = dbgTools.DTH (dpfx^   prevth2)  val _ = dbgTools.DST (dpfx^  " ADOlift prev th 2\n") (*DBG*)*)
		in MATCH_MP SUBSET_TRANS (LIST_CONJ [prev_adosubthm,prevth2]) end
	    else  prev_adosubthm
	(*val _ = dbgTools.DTH (dpfx^   ado_subthm)   val _ = dbgTools.DST (dpfx^  " lifted ado_subthm\n") (*DBG*)*)
	val _ = dbgTools.DEX dpfx "al" (*DBG*)
    in  ado_subthm end

fun mk_ado_pre_sub_thm ado ado_subthm t2 ksname ie1 eeq imf_thms abthm wfKS_ks ie t1 initset seth imf_t2 ess
		       eus chainth adogeneqthm initsubth n =
    let
	(* make ado sub_thm i.e.initset SUBSET STATES f ks e[[[Q<--initset]]],used to discharge GEN_MU_FP_STATES *)
	val _ = dbgTools.DEN dpfx "ap" (*DBG*)
	(*val _ = dbgTools.DTM (dpfx^  initset)  val _ = dbgTools.DST (dpfx^  " ADOpre initset\n") (*DBG*)
	val _ = dbgTools.DTH (dpfx^" ADOpre spec glc\n"  (ISPECL [t2,ksname,ie,n,t1,initset] chainth))  (*DBG*)*)
	val prev_adosubthm = if ado then (Option.valOf ado_subthm)
			     else (ISPEC ``STATES ^t2 ^ksname ^ie1`` initsubth)
	(*val _ = dbgTools.DTH (dpfx^   prev_adosubthm)  val _ = dbgTools.DST (dpfx^  " ADOpre prev ado_subthm\n")  (*DBG*)*)
	val _ = if (not (null eeq)) then dbgTools.DTH (dpfx^"ap_ hd eeq")  (fst (hd eeq)) else dbgTools.DST (dpfx^"ap_ empty")
	(*val _ = dbgTools.DST (dpfx^  " hd eeq\n") (*DBG*) *)
	val ado_subthm' =
	    if ado then
		let
		    (*val _ = dbgTools.DTM (dpfx^  t2)  val _ = dbgTools.DST (dpfx^  " ADOpre t1\n") (*DBG*)
		    val _ = dbgTools.DTH (dpfx^" ADO prev imf th\n"   (Binarymap.find(imf_thms,t2)))   (*DBG*)
 		    val _ = dbgTools.DTH (dpfx^   (snd(hd eeq)))  val _ = dbgTools.DST (dpfx^  " ADO prev ab th\n") (*DBG*)
	            val _ = dbgTools.DTH (dpfx^   abthm)  val _ = dbgTools.DST (dpfx^  " ADOpre curr ab th\n") (*DBG*)*)
	            val prevth = MATCH_MP STATES_MONO_EQ
			(LIST_CONJ [wfKS_ks,PURE_ONCE_REWRITE_RULE [snd(hd eeq)] (Binarymap.find(imf_thms,t2)),
				    PURE_ONCE_REWRITE_RULE [adogeneqthm] (fst(hd eeq))])
		    (*val _ = dbgTools.DTH (dpfx^   prevth)  val _ = dbgTools.DST (dpfx^  " ADOpre prev th\n") (*DBG*)*)
                    val (ie0,(t1o,_)) = dest_env ie
		    val ie0' = list_mk_comb(eus,[ie0,t1,initset])
		    val prevth2 = REWRITE_RULE [MATCH_MP ENV_SWAP (Binarymap.find(Binarymap.find(seth,fromHOLstring t1),
										  fromHOLstring t1o))] (SPEC ie0' prevth)
		    (*val _ = dbgTools.DTH (dpfx^   prevth2)  val _ = dbgTools.DST (dpfx^  " ADOpre prev th 2\n") (*DBG*)*)
		in MATCH_MP SUBSET_TRANS (LIST_CONJ [prev_adosubthm,prevth2]) end
	    else (MP (ISPECL [t2,ksname,ie,n,t1,initset] chainth)
		  (LIST_CONJ [wfKS_ks,PURE_ONCE_REWRITE_RULE [abthm] imf_t2,prev_adosubthm]))
	(*val _ = dbgTools.DTH (dpfx^   ado_subthm')   val _ = dbgTools.DST (dpfx^  " ado_presubthm'\n") (*DBG*)*)
	val _ = dbgTools.DEX dpfx "ap" (*DBG*)
    in ado_subthm' end

(* called by muCheck.mk_gen_thms *)
fun mk_gen_inv_thms ksname state wfKS_ks =
    let
	val _ = dbgTools.DEN dpfx "mgit"  (*DBG*)
	val res =
	    [ISPEC ksname SAT_AP_ENV_INV,
	     ISPEC ksname SAT_RV_ENV_INV,
	     ISPEC ksname SAT_T_ENV_INV,
	     ISPEC ksname SAT_F_ENV_INV,
	     MP (ISPEC ksname SAT_NEG_ENV_INV) wfKS_ks, MP (ISPEC ksname SAT_NEG_ENV_INV2) wfKS_ks,
	     ISPEC ksname SAT_CONJ_ENV_INV,ISPEC ksname SAT_CONJ_ENV_INV2,
	     ISPEC ksname SAT_DISJ_ENV_INV,ISPEC ksname SAT_DISJ_ENV_INV2,
	     ISPEC ksname SAT_DMD_ENV_INV, ISPEC ksname SAT_DMD_ENV_INV2,
	     ISPEC ksname SAT_BOX_ENV_INV, ISPEC ksname SAT_BOX_ENV_INV2,
	     ISPECL [ksname,state] SAT_LFP_ENV_INV, ISPEC ksname SAT_LFP_ENV_INV2,
	     ISPECL [ksname,state] SAT_GFP_ENV_INV, ISPEC ksname SAT_GFP_ENV_INV2]
	val _ = dbgTools.DEX dpfx "mgit"  (*DBG*)
    in res end


fun mk_ado_imf_goals [] =  []
| mk_ado_imf_goals sigfl =
    let
	val _ = dbgTools.DEN dpfx "aig"  (*DBG*)
	val sfl2 = List.filter (fn (_,l) => not (null l)) (List.map (fn f => (f,top_sigma (is_nu f) (rand f))) sigfl)
	val prop_type = hd(snd(dest_type(type_of (hd sigfl))))
	val ip = inst [alpha|->prop_type]
	val gls = List.map (fn (f,sfl) => List.map (fn sf => mk_comb((ip mu_imf_tm),
								     list_mk_comb(ip(if is_nu f then mu_nu_tm else mu_mu_tm),
										  [rand (rator f),rand sf]))) sfl) sfl2
	val res = (List.concat gls)@(mk_ado_imf_goals (List.concat (List.map snd sfl2)))
	val _ = dbgTools.DEX dpfx "aig"  (*DBG*)
    in res end

(* for each sigma formula sig Q.f, if there exists in f a top-level sig formula of the same type (mu/nu) sig P.g, then prove that
   IMF Q. g *)
fun mk_ado_imf_thms mf seth tysimps frv_thms imf_thms=
    let
	val _ = dbgTools.DEN dpfx "ai"(*DBG*)
        val sigfl = (top_sigma true mf)@(top_sigma false mf)
	val prop_type = hd(snd(dest_type(type_of mf)))
	(*val _ = DMSG (TY prop_type)  val _ = dbgTools.DST (dpfx^  "ptype\n") *)
	val ip = inst [alpha|->prop_type]
        val res = if null sigfl then imf_thms
		  else let
			   val gls = mk_ado_imf_goals sigfl
			   val sel = (List.map (fn (rv,eqs) => eqs) (flatten(List.map (fn (rv,bm)=>Binarymap.listItems bm)
											(Binarymap.listItems seth))))
			   val res = List.foldl (fn (gl,bm) =>
						 let val jf = (fn _ => prove(gl,SIMP_TAC std_ss ([IMF_def,MU_SUB_def,NNF_def,RVNEG_def] @
												 tysimps @ sel)))
						     val th = mk_lthm (fn _ => (gl,jf)) jf
						     (*val _ = dbgTools.DTH (dpfx^" ADO imf th\n" th)   (*DBG*)*)
						     val frv_thm = frv_find frv_thms (rand (rand gl))
						     (*val _ = dbgTools.DTH (dpfx^  frv_thm) (*DBG*)
						     val _ = dbgTools.DST (dpfx^  " ADO ab th\n") (*DBG*)*)
						     val th1 = ONCE_REWRITE_RULE [SYM frv_thm] th
						     (*val _ = dbgTools.DTH (dpfx^" ab ADO imf th" th1)   (*DBG*)*)
						 in Binarymap.insert(bm,lhs(concl frv_thm),th1) end)
			       imf_thms gls
		       in res end
	val _ = dbgTools.DEX dpfx "ai"(*DBG*)
    in res end

end
end


