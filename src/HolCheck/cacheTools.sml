
structure cacheTools =
struct

local

open Globals HolKernel Parse goalstackLib;
infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;
open Psyntax;

open bossLib;
open pairTheory;
open pred_setTheory;
open pred_setLib;
open stringLib;
open listTheory;
open simpLib;
open pairSyntax;
open pairLib;
open PrimitiveBddRules;
open DerivedBddRules;
open Binarymap;
open PairRules;
open pairTools;
open setLemmasTheory;
open muSyntax
open muSyntaxTheory;
open muTheory;
open boolSyntax;
open Drule;
open Tactical;
open Conv;
open Rewrite;
open Tactic;
open boolTheory;
open listSyntax;
open stringTheory;
open stringBinTree;
open boolSimps;
open pureSimps;
open listSimps;
open numLib;
open reachTheory;
open bddTools
open envTheory
open envTools
open muTools
open cacheTheory
open holCheckTools

val dbgct = holCheckTools.dbgall

fun DMSG m v = if v then let val _ = print "cacheTools: " val _ = holCheckTools.DMSG m v in () end else ()

in

(* given f e and e', proves |- !Q. if ~(SUBFORMULA (~RV Q) (NNF f) then e Q = e' Q else e Q SUBSET e' Q where
   e is the env for the previous iteration and e' is the env for the current iteration 
   seth are the string equality theorems required for evaluating the envs *) 
fun ITER_ENV_LEGAL_CONV t2 t1 e e' seth state ksname ttm imf_thms imf_t2 frv_thms wfKS_ks abthm cabthm eeq =  
    let 
	val _ = DMSG (ST  "ITER_ENV_LEGAL_CONV\n") (dbgct)(*DBG*)
        (* FIXME: need to have unwound version of t2 for passing to NNF_RVNEG_CONV but this could have efficiency issues *)
	val gl = ``!Q'. if (SUBFORMULA (~(RV Q')) (NNF ^t2)) then (^e) Q' = (^e') Q' else (^e) Q' SUBSET (^e') Q'``;
	val _ = DMSG (TM  t2) (dbgct) val _ = DMSG (ST  " ielc t2\n") (dbgct)(*DBG*)
        val th1 = PURE_ONCE_REWRITE_RULE [cabthm] (NNF_RVNEG_CONV t2)
	val _ = DMSG (TH   th1) (dbgct) val _ = DMSG (ST  " ielc th1\n") (dbgct)(*DBG*)
	val _ = DMSG (TM  gl) (dbgct) val _ = DMSG (ST  " ielc goal\n") (dbgct)(*DBG*)
	val _ = DMSG (TM  e ) (dbgct) val _ = DMSG (ST  " ielc env\n") (dbgct)(*DBG*)
	val _ = DMSG (TM  e') (dbgct) val _ = DMSG (ST  " ielc env'\n") (dbgct)(*DBG*)
	val gl1 = (REWRITE_CONV [ENV_CASES,th1] THENC REPEATC (SIMP_CONV (bool_ss ++ boolSimps.COND_elim_ss) [SUBSET_REFL])) gl;
	val _ = DMSG (TM  (rhs(concl gl1))) (dbgct) val _ = DMSG (ST  " ielc second goal \n") (dbgct)(*DBG*)
	val res =  if (Term.compare(rhs(concl gl1),T)=EQUAL) then ONCE_REWRITE_RULE [EQ_CLAUSES] gl1 
		   else let val env_seq_thms = List.map fst eeq
			in SIMP_RULE bool_ss env_seq_thms gl1 end
	val _ = DMSG (TH   res) (dbgct) val _ = DMSG (ST  " ielc res\n") (dbgct)(*DBG*)
	val _ = DMSG (ST  "ITER_ENV_LEGAL_CONV done\n") (dbgct)(*DBG*)
    in res end

(* show that term of conjuncts of the form e[q<--x] p = e'[q<--x] p can be mapped to conjuncts e p = e'p 
either because q != p or if q=p then that particular conjunct becomes true and disappears *)
fun mk_ante_eq_thm goal seth =
    let val _ = DMSG (ST  "mk_ante_eq_thm\n") (dbgct)(*DBG*)
        val _ = DMSG (TM  goal) (dbgct)(*DBG*)
        val _ = DMSG (ST  " goals\n") (dbgct)(*DBG*)
        val goals = strip_conj goal
	val thms = List.map (fn g => let (*val _ = DMSG (TM  g) (dbgct) val _ = DMSG (ST  " goal\n") (dbgct)(*DBG*)*)
					 val (glhs,grhs) = dest_eq g
					 (*val _ = DMSG (TM  glhs) (dbgct) val _ = DMSG (ST  " glhs\n") (dbgct)(*DBG*)
					 val _ = DMSG (TM  grhs) (dbgct) val _ = DMSG (ST  " grhs\n") (dbgct)(*DBG*)*)
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
					 (*val _ = DMSG (TH   seqthm) (dbgct) val _ = DMSG (ST  " seq_thm\n") (dbgct)(*DBG*)*) 
					 val eqth = GEN_ALL(List.hd(List.tl(CONJUNCTS(SPEC_ALL EQ_CLAUSES)))) 
					 val eqth1 =  if (is_neg (concl seqthm)) then eqth else ISPEC (fst(dest_eq(concl seqthm))) eqth
					 (*val _ = DMSG (TH   eqth) (dbgct) val _ = DMSG (ST  " eq_thm\n") (dbgct)(*DBG*)*) 
					 val seqthm = if (is_neg (concl seqthm)) then seqthm else PURE_ONCE_REWRITE_RULE [eqth1] seqthm
					 (*val _ = DMSG (TH   seqthm) (dbgct) val _ = DMSG (ST  " seqthm\n") (dbgct)(*DBG*)*) 
					 val envth = if (String.compare(qs,ps)=EQUAL) then ENV_EVAL_EQ_INV else ENV_EVAL_NEQ_INV 
					 (*val _ = DMSG (TH   (ISPECL [le,re,q,p,x] envth)) (dbgct) 
                                           val _ = DMSG (ST  " envth\n") (dbgct)(*DBG*)*)
					 val th = MP (ISPECL [le,re,q,p,x] envth) seqthm 
				     in if (is_neg(concl seqthm)) then th 
					else PURE_ONCE_REWRITE_RULE [ISPEC (concl th) (GSYM eqth)] th end) goals 
	(*val _ = List.app (fn tt => let val _ = DMSG (TH  tt) (dbgct) val _ = DMSG (ST  " se thm\n") (dbgct) in () end) thms(*DBG*)*)
	val thl = List.map (fn (g,th) => PURE_ONCE_REWRITE_CONV [th] g) (ListPair.zip(goals,thms))
	(*val _ = List.app (fn tt => let val _ = DMSG (TH  tt) (dbgct) val _ = DMSG (ST  " se thm2\n") (dbgct) in () end) thl(*DBG*)*)
        val _ = DMSG (ST  "mk_ante_eq_thm done\n") (dbgct)(*DBG*)
    in thl end

fun mk_inv_zero_ante speclist spec_thm mp_thm abthml =
    let 
	val _ = DMSG (ST  " mk_inv_zero_ante\n") (dbgct) (*DBG*)
	(*val _ = DMSG (TH   spec_thm) (dbgct) val _ = DMSG (ST  " spec_thm\n") (dbgct)(*DBG*)
	val _ = DMSG (TH   mp_thm) (dbgct) val _ = DMSG (ST  " mp_thm\n") (dbgct)(*DBG*)
	val _ = List.app (fn tt=> let val _= DMSG (TM tt) (dbgct) val _ = DMSG (ST " speclist\n") (dbgct) in () end) speclist(*DBG*)*)
	(*val _ = List.app (fn tt => let val _ = DMSG (TH tt) (dbgct) val _ = DMSG (ST " abthml\n") (dbgct) in () end) abthml(*DBG*)*)
	val th = MATCH_MP (CONV_RULE FORALL_IMP_CONV ((CONV_RULE (LAST_FORALL_CONV FORALL_IMP_CONV)) (ISPECL speclist spec_thm))) mp_thm
	(*val _ = DMSG (TH   th) (dbgct) val _ = DMSG (ST  " th\n") (dbgct)(*DBG*)*)
    in th end

fun mk_inv_one_ante args cthm tthm ithm left abthml =
 let val _ = DMSG (ST  " mk_inv_one_ante\n") (dbgct) (*DBG*)
     (*val _ = DMSG (TM  (List.hd args)) (dbgct) val _ = DMSG (ST  " hd args\n") (dbgct)(*DBG*)
     val _ = DMSG (TM  (List.last args)) (dbgct) val _ = DMSG (ST  " last args\n") (dbgct)(*DBG*)
     val _ = DMSG (TH   cthm) (dbgct) val _ = DMSG (ST  " cthm\n") (dbgct)(*DBG*)
     val _ = DMSG (TH   tthm) (dbgct) val _ = DMSG (ST  " tthm\n") (dbgct)(*DBG*)
     val _ = DMSG (TH   ithm) (dbgct) val _ = DMSG (ST  " ithm\n") (dbgct)(*DBG*)*)
     val _ = List.app (fn tt => let val _ = DMSG (TH   tt) (dbgct) val _ = DMSG (ST  " abthml\n") (dbgct) in () end) abthml(*DBG*)
     val (ante,tc) = dest_imp(snd(strip_forall(concl cthm)))
     val (ql,t) = strip_forall(concl tthm)
     val tthm2 = prove(list_mk_forall(ql,mk_imp(ante,t)),SIMP_TAC std_ss [tthm])
     (*val _ = DMSG (TH   tthm2) (dbgct) val _ = DMSG (ST  " tthm2\n") (dbgct)(*DBG*)*)
     val th2 = CONV_RULE (QUANT_CONV AND_FORALL_CONV)
         (CONV_RULE AND_FORALL_CONV (LIST_CONJ (if left then [cthm,tthm2] else [tthm2,cthm])))
     (*val _ = DMSG (TH   th2) (dbgct) val _ = DMSG (ST  " th2\n") (dbgct)(*DBG*)*)
     val th3 = MATCH_MP (ISPECL ([ante,ante]@(if left then [tc,t] else [t,tc])) fol1) (SPEC_ALL th2)
     (*val _ = DMSG (TH   th3) (dbgct) val _ = DMSG (ST  " th3\n") (dbgct)(*DBG*)*)
     val th4 = SIMP_RULE bool_ss [] (GENL [List.hd ql,List.last ql] th3)
     (*val _ = DMSG (TH   th4) (dbgct) val _ = DMSG (ST  " th4\n") (dbgct)(*DBG*)*)
     val geninv = (ISPECL [List.hd args,List.last args, List.hd ql,List.last ql] ithm)
     (*val _ = DMSG (TH   geninv) (dbgct) val _ = DMSG (ST  " geninv\n") (dbgct)(*DBG*)*)
     val sfol = ISPECL (ante::((if left then [tc,t] else [t,tc])@[snd(dest_imp(concl geninv))])) fol3
     (*val _ = DMSG (TH   sfol) (dbgct) val _ = DMSG (ST  " sfol\n") (dbgct)(*DBG*)*)
     val th5 = MATCH_MP  sfol geninv
     (*val _ = DMSG (TH   th5) (dbgct) val _ = DMSG (ST  " th5\n") (dbgct) (*DBG*)*)
     val th6 = MATCH_MP th5 (SPEC_ALL th4)
 in GENL [List.hd ql,List.last ql] th6 end

fun mk_inv_two_ante args ithml ithm abthml =
    let 
	val _ = DMSG (ST  " mk_inv_two_ante\n") (dbgct)(*DBG*)
	(*val _ = DMSG (TM  (List.hd args)) (dbgct) val _ = DMSG (ST  " hd args\n") (dbgct)(*DBG*)
	val _ = DMSG (TM  (List.last args)) (dbgct) val _ = DMSG (ST  " last args\n") (dbgct)(*DBG*)*)
	val cthm1 = List.hd ithml
        val (ante1,t1) = dest_imp(snd(strip_forall(concl cthm1)))
        val cthm2 = List.last ithml
        val (ante2,t2) = dest_imp(snd(strip_forall(concl cthm2)))
        val (ql,_) = strip_forall(concl cthm1)
        val th2 = CONV_RULE (QUANT_CONV AND_FORALL_CONV) (CONV_RULE AND_FORALL_CONV (LIST_CONJ [cthm1,cthm2]))
        val th3 = MATCH_MP (ISPECL [ante1,ante2,t1,t2] fol1) (SPEC_ALL th2)
        val th4 = CONV_RULE (STRIP_QUANT_CONV(LAND_CONV(SIMP_CONV bool_ss []))) (GENL ql th3)
        val geninv = (ISPECL [List.hd args, List.last args,List.hd ql,List.last ql] ithm)
        val sfol = ISPECL [snd(dest_eq(concl(SIMP_CONV bool_ss [] (mk_conj(ante1,ante2))))) handle ex => (mk_conj(ante1,ante2)),
                           t1,t2,snd(dest_imp(concl geninv))] fol3
        val th5 = MATCH_MP sfol geninv
        val th6 = MATCH_MP th5 (SPEC_ALL th4)
	val _ = DMSG (ST  " mk_inv_two_ante done\n") (dbgct)(*DBG*)
    in GENL ql th6 end

fun remove_bv ante bv = (* ante is e Q = e' Q /\ e P = e' P ... term, bv is current bound var *)
    let val eqs = strip_conj ante
        val ante' = List.filter (fn el => not (Term.compare(snd(dest_comb(fst(dest_eq el))),bv)=EQUAL)) eqs
    in if (List.null ante') then ``T:bool`` else list_mk_conj ante' end

fun mk_inv_modal_ante args ithml ithm1 ithm2 chc state env abthml =  
    if (chc=0)
	then (* child does not have antecedents *)
	    let 
		val _ = DMSG (ST  " modal no ante\n") (dbgct)(*DBG*)
		val th =  mk_inv_zero_ante [List.hd args,List.last args] ithm1 (List.hd ithml) abthml 
	    val _ = DMSG (ST  " modal no ante done\n") (dbgct)(*DBG*)
	    in th end
    else
    let val _ = DMSG (ST  " modal with ante\n") (dbgct)(*DBG*)
	val cthm = List.hd ithml
	(*val _ = DMSG (TH   cthm) (dbgct) val _ = DMSG (ST  " cthm\n") (dbgct)(*DBG*)*)
        val (ante,_) = dest_imp(snd(strip_forall(concl cthm)))
	val (ql,_) = strip_forall(concl cthm)
	val geninv = ISPECL [List.hd args,List.last args,List.hd ql,List.last ql] ithm2
	(*val _ = DMSG (TH   geninv) (dbgct) val _ = DMSG (ST  " geninv\n") (dbgct)(*DBG*)*)
        val tc3 = fst(dest_imp(concl geninv))
	val sfol = ISPECL [ante,tc3,snd(dest_imp(concl geninv))] fol5
	(*val _ = DMSG (TH   sfol) (dbgct) val _ = DMSG (ST  " sfol\n") (dbgct)(*DBG*)*)
        val th1 = MATCH_MP sfol geninv
	(*val _ = DMSG (TH   th1) (dbgct) val _ = DMSG (ST  " th1\n") (dbgct)(*DBG*)*)
        val cth2 = SPEC_ALL cthm
	(*val _ = DMSG (TH   cth2) (dbgct) val _ = DMSG (ST  " cth2\n") (dbgct)(*DBG*)*)
        val th2 = MATCH_MP th1 cth2
	(*val _ = DMSG (TH   th2) (dbgct) val _ = DMSG (ST  " th2\n") (dbgct)(*DBG*)*)
	val _ = DMSG (ST  " modal with ante done\n") (dbgct)(*DBG*)
    in GENL [``e:^(ty_antiq(type_of env))``,``e':^(ty_antiq(type_of env))``] th2 end

fun mk_inv_fp_ante args ithml ithm chc state seth abthml =
    let 
	val _ = DMSG (ST  " mk_inv_fp_ante\n") (dbgct) (*DBG*)
	val th = if (chc=0) (* child does not have antecedents *)
		 then
		     let (*val _ = DMSG (ST  " mk_inv_fp_ante no ante\n") (dbgct)(*DBG*)*)
                         val cthm = List.hd ithml
			 val (ql,_) = strip_forall(concl cthm)
			 (*val _ = with_flag (show_types,true) DMSG (TH   ithm) (dbgct) val _ = DMSG (ST  " ithm\n") (dbgct)(*DBG*)
			 val _ = with_flag (show_types,true) DMSG (TM  (List.hd args)) (dbgct) val _ = DMSG (ST  " hd args\n") (dbgct)(*DBG*)
			 val _ = with_flag (show_types,true) DMSG (TM  (List.last args)) (dbgct) val _ = DMSG (ST  " last args\n") (dbgct)(*DBG*)
			 val _ = with_flag (show_types,true) DMSG (TM  (List.hd ql)) (dbgct) val _ = DMSG (ST  " hd ql\n") (dbgct)(*DBG*)
			 val _ = with_flag (show_types,true) DMSG (TM  (List.last ql)) (dbgct) val _ = DMSG (ST  " last ql\n") (dbgct)(*DBG*)*)
			 val geninv = ISPECL [List.hd args, List.last args,List.hd ql,List.last ql] ithm
			 (*val _ = DMSG (TH   geninv) (dbgct) val _ = DMSG (ST  " geninv\n") (dbgct)(*DBG*)*)
			 val X = ``X: ^(ty_antiq(mk_type("fun",[type_of state,``:bool``])))``
			 val cthm2 = ISPECL [``^(List.hd ql)[[[^(List.hd args)<--^X]]]``,
					     ``^(List.last ql)[[[^(List.hd args)<--^X]]]``] cthm
			 (*val _ = DMSG (TH   cthm2) (dbgct) val _ = DMSG (ST  " cthm2\n") (dbgct)(*DBG*)*)
			 val cthm3 =  (GEN X cthm2)
			 val th1 = GENL [List.hd ql, List.last ql] (MATCH_MP geninv cthm3)
			 (*val _ = DMSG (ST  " mk_inv_fp_ante no ante done\n") (dbgct)(*DBG*)*)
		     in th1 end
		 else
		     let (*val _ = DMSG (ST  " mk_inv_fp_ante yes ante\n") (dbgct)(*DBG*)*)
			 val cthm = List.hd ithml
			 (*val _ = DMSG (TH   cthm) (dbgct) val _ = DMSG (ST  " cthm\n") (dbgct)(*DBG*)*)
			 val (ql,_) = strip_forall(concl cthm)
			 val (ante,_) = dest_imp(snd(strip_forall(concl cthm)))
			 val ante1 = remove_bv ante (List.hd args)
			 val X = ``X: ^(ty_antiq(mk_type("fun",[type_of state,``:bool``])))``
			 val cthm2 = ISPECL [``^(List.hd ql)[[[^(List.hd args)<--^X]]]``,
						``^(List.last ql)[[[^(List.hd args)<--^X]]]``] cthm
			(* val _ = DMSG (TH   cthm2) (dbgct) val _ = DMSG (ST  " cthm2\n") (dbgct)(*DBG*)*)
			 val (sante,_) = dest_imp(snd(strip_forall(concl cthm2))) (* no need to remove_bv; mk_ante_eq takes care of it*)
			 val geninv = ISPECL [List.hd args, List.last args,List.hd ql,List.last ql] ithm
			 (*val _ = DMSG (TH   geninv) (dbgct) val _ = DMSG (ST  " geninv\n") (dbgct)(*DBG*)*)
			 val tc3 = fst(dest_imp(concl geninv))
			 (*val _ = DMSG (ST  " mk_inv_fp_ante yes ante done\n") (dbgct)(*DBG*)*)
		     in if (Term.compare(ante1,``T:bool``)=EQUAL)
			then (* no antecedents left, remove completely; this happens if bv was the only sub-RV *)
			    let val noantethm = mk_ante_eq_thm sante seth
				val cthm3 = SIMP_RULE std_ss noantethm cthm2
				(*val _ = DMSG (ST  " doing cthm4\n") (dbgct)(*DBG*)*)
				val cthm4 = (GEN X cthm3)
				(*val _ = DMSG (TH   cthm4) (dbgct) val _ = DMSG (ST  " done cthm4\n") (dbgct)(*DBG*)*)
				val th1 = GENL [List.hd ql, List.last ql] (MATCH_MP geninv cthm4)
			    in th1 end
			else (* antecedents still left; ripple to current inv thm *)
			    let val sfol = ISPECL [ante1,tc3,snd(dest_imp(concl geninv))] fol5
				val th1 = MATCH_MP sfol geninv
				val ae = mk_ante_eq_thm sante seth
				val cthm3 = REWRITE_RULE ae cthm2
				val cthm4 =  (CONV_RULE FORALL_IMP_CONV (GEN X cthm3))
				val th2 = MATCH_MP th1 cthm4
			    in  GENL ql th2 end
		     end
	val _ = DMSG (ST  " mk_inv_fp_ante done\n") (dbgct)(*DBG*)
    in th end

(* return NONE if entire list is NONE, else a list of just the thms*)
fun merge_abthms abthml = List.map Option.valOf (List.filter Option.isSome abthml) 

fun mk_inv_thm opr args env ithml (githms as [AP_I,RV_I,T_I,F_I,NEG_I,NEG_I2,CONJ_I,CONJ_I2,DISJ_I,DISJ_I2,DMD_I,DMD_I2,BOX_I,BOX_I2,LFP_I,LFP_I2,GFP_I,GFP_I2]) state chc (msp as [MU_SAT_T,MU_SAT_F,MU_SAT_NEG,MU_SAT_CONJ,MU_SAT_DISJ]) seth abthml =
    let (*val _ = DMSG (TM  opr) (dbgct)*) val _ = DMSG (ST  " mk_inv_thm\n") (dbgct)(*DBG*)
    in  case (fst (dest_const opr)) of
            "AP"      => let (*val _ = with_flag(show_types,true) DMSG (TH   AP_I) (dbgct) (*DBG*)
			     val _ = DMSG (ST  " (AP_I)\n") (dbgct)(*DBG*)
			     val _ = with_flag(show_types,true)DMSG (TM  (List.hd args)) (dbgct)(*DBG*)
			     val _ = DMSG (ST  " (hd args)\n") (dbgct)(*DBG*) *)
			 in ISPEC (List.hd args) AP_I end
          | "RV"      => ISPEC (List.hd args) RV_I (* note this is not used if this RV is current bound *)
          | "And"     => (case chc of (* 0=neither child has antecedents, 1=left child, 2= right, 3 = both *)
                             0 => mk_inv_zero_ante [List.hd args, List.last args] CONJ_I (LIST_CONJ ithml) (merge_abthms abthml) 
                           | 1 => mk_inv_one_ante args (List.hd ithml) (List.last ithml) CONJ_I2 true (merge_abthms abthml) 
                           | 2 => mk_inv_one_ante args (List.last ithml) (List.hd ithml) CONJ_I2 false (merge_abthms abthml) 
                           | 3 => mk_inv_two_ante args ithml CONJ_I2 (merge_abthms abthml)
                           | _ => Raise Match )
          | "Or"      =>  (case chc of (* 0=neither child has antecedents, 1=left child, 2= right, 3 = both *)
                             0 => mk_inv_zero_ante [List.hd args, List.last args] DISJ_I (LIST_CONJ ithml) (merge_abthms abthml) 
                           | 1 => mk_inv_one_ante args (List.hd ithml) (List.last ithml) DISJ_I2 true (merge_abthms abthml) 
                           | 2 => mk_inv_one_ante args (List.last ithml) (List.hd ithml) DISJ_I2 false (merge_abthms abthml) 
                           | 3 => mk_inv_two_ante args ithml DISJ_I2 (merge_abthms abthml)
                           | _ => Raise Match)
          | "Not"     => if (chc=0)
                         then (* child does not have antecedents *)
                             mk_inv_zero_ante [List.hd args] NEG_I (List.hd ithml) (merge_abthms abthml) 
                         else
                             let val cthm = List.hd ithml
                                 val (ante,tc) = dest_imp(snd(strip_forall(concl cthm)))
                                 val (ql,_) = strip_forall(concl cthm)
                                 val geninv = ISPECL [List.hd args,List.hd ql,List.last ql] NEG_I2
                                 val sfol = ISPECL [ante,tc,snd(dest_imp(concl geninv))] fol5
                                 val th1 = MATCH_MP sfol geninv
                                 val th2 = MATCH_MP th1 (SPEC_ALL cthm)
                                 (*val _ = DMSG (TH   th2) (dbgct) val _ = DMSG (ST  " Not th2\n") (dbgct)(*DBG*)*)
                             in GENL [``e:^(ty_antiq(type_of env))``,``e':^(ty_antiq(type_of env))``] th2 end
          | "TR"      => T_I
          | "FL"      => F_I
          | "DIAMOND" => mk_inv_modal_ante args ithml DMD_I DMD_I2 chc state env (merge_abthms abthml)  
          | "BOX"     => mk_inv_modal_ante args ithml BOX_I BOX_I2 chc state env (merge_abthms abthml)  
          | "mu"      => mk_inv_fp_ante args ithml LFP_I2 chc state seth (merge_abthms abthml) 
          | "nu"      => mk_inv_fp_ante args ithml GFP_I2 chc state seth (merge_abthms abthml) 
          | _         => Raise Match
    end
| mk_inv_thm opr args env ithml githms state chc msp seth abthml = Raise Match

fun print_rsc rsc label =
    let val _ = print  (label^" rsc ")
        val _ = Vector.appi (fn (i,iv) => print  ((Int.toString i)^":"^(Int.toString(Vector.sub(rsc,i)))^" ")) (rsc,0,NONE)
    in print "\n" end

fun is_eq_rsc rsc rsc' = List.foldl (fn (i,t) => t andalso Vector.sub(rsc,i)=Vector.sub(rsc',i)) true (List.tabulate(Vector.length rsc,I))

(* cache entry is (term_bdd,gth,sth,env for which sth and tb are valid, index of RV tb if any else -1,
reverse scope of bound RV, environment invariance thm for this node, abbrev thm for this node, ado sub thm, ado eq thm *)
fun cache_add depth rvnm2ix env mf mfo ce rsc rvty ithml (githms as [_,_,T_I,F_I,_,_,_,_,_,_,_,_,_,_,_,_,_,_]) state seth msp guid abthml =
    let val _ = DMSG (ST  (" cache_add\n")) (dbgct) (*DBG*)
	val cekey = if is_RV mf then mu_RV state (fromMLstring((fromHOLstring(rand mf))^(int_to_string depth))) else mf
	val _ = DMSG (TM  cekey) (dbgct) val _ = DMSG (ST  " cekey\n") (dbgct)(*DBG*)
	val en = Binarymap.peek(ce,cekey)
        val _ = DMSG (TM  mf) (dbgct) val _ = DMSG (ST  " mf\n") (dbgct)(*DBG*)
	fun same_rsc rsc en = let val (_,_,_,_,_,rsc',_,_,_,_) = !(Option.valOf en) in is_eq_rsc rsc rsc' end
    (* if not RV then must agree on reverse scope otherwise (say) <.> Q and <.> Q in different scopes would be identified *)
    (* reverse scoping for RV's is more complicated, so it is quicker to just cache on name+depth to tell them apart *)
    in if (Option.isSome en) andalso (is_RV mf orelse same_rsc rsc en) 
       then
           let val (_,_,_,_,_,rsc,ithm,abthm,_,_) = !(Option.valOf en)
	       val _ = DMSG (ST  " already cached\n") (dbgct)
           in (Option.valOf en,(ce,rsc,ithm,abthm)) end
       else
           let val (opr,args) = strip_comb mf
	       val (_,argso) = strip_comb mfo
               val (en,rsc,ithm,abthm) =
                   case (fst (dest_const opr)) of
                       "AP"      => let val abthm = REFL mf 
					val ithm = mk_inv_thm opr args env ithml githms state 0 msp seth abthml
                                    in (ref (NONE,NONE,NONE,env,~1,rsc,ithm,SOME abthm,NONE,NONE),rsc,ithm,SOME abthm) end
                     | "RV"      => let val rv = snd(dest_comb mf)
                                        val _ = DMSG (ST ("RV")) (dbgct); val _ = DMSG (ST (fromHOLstring rv)) (dbgct);(*DBG*)
                                        val _ = List.app (fn (b,i) => let val _ = DMSG (ST  (b^"::"^(int_to_string i)^"\n")) (dbgct) in () end)
                                                         (rvnm2ix)(*DBG*)
                                        val ix =  holCheckTools.listkeyfind rvnm2ix (fromHOLstring rv) String.compare
                                        val rsc = Vector.mapi 
					    (fn (i,v)=> if (i=ix)
							    then ((let val ty = holCheckTools.listkeyfind rvty rv Term.compare
								   in if ty then 2 else 1
								   end) handle NotFound => 0)
							else v) (rsc,0,NONE)
                                        (*val _ = print_rsc rsc "RV cache_add depth"*)
                                        val ithm = mk_inv_thm opr args env ithml githms state 0 msp seth abthml
					val abthm = REFL mf
                                    in (ref (NONE,SOME TRUTH,NONE,env,ix,rsc,ithm,SOME abthm,NONE,NONE),rsc,ithm,SOME abthm) end
                       | "And"     => let val _ = DMSG (ST  "cache_add depth And\n") (dbgct)(*DBG*)
                                          (*val _ = DMSG (TH   CONJ_I) (dbgct)(*DBG*)*)
                                          (*val _ = DMSG (ST  " gen\n") (dbgct)(*DBG*)*)
                                          val chc = (if (is_imp(snd(strip_forall(concl(List.hd ithml))))) then 1 else 0)
                                                    +(if (is_imp(snd(strip_forall(concl(List.last ithml))))) then 2 else 0)
					  val lcabthmnm = lhs(concl(Option.valOf(List.hd abthml)))
					  val rcabthmnm = lhs(concl(Option.valOf(List.last abthml)))
                                          val abthm = let val vnm = "frv"^(int_to_string (!guid))
                                                      in hd(Defn.eqns_of(Hol_defn (vnm) 
										  `^(mk_eq(mk_var(vnm,type_of mf),
											   ``And (^lcabthmnm) (^rcabthmnm)``))`)) end
                                          val _ = (guid := (!guid)+1)
                                          val ithm = mk_inv_thm opr [lcabthmnm,rcabthmnm] env ithml githms state chc msp seth abthml
					  val ithm = PURE_ONCE_REWRITE_RULE [SYM abthm] ithm    
                                      in (ref (NONE,NONE,NONE,env,~1,rsc,ithm,SOME abthm,NONE,NONE),rsc,ithm,SOME abthm) end
                       | "Or"      => let val _ = DMSG (ST  "cache_add depth Or\n") (dbgct)(*DBG*)
                                          (*val _ = DMSG (TH   DISJ_I) (dbgct)(*DBG*)*)
                                         (* val _ = DMSG (ST  " gen\n") (dbgct)(*DBG*)*)
                                          val chc = (if (is_imp(snd(strip_forall(concl(List.hd ithml))))) then 1 else 0)
                                                    +(if (is_imp(snd(strip_forall(concl(List.last ithml))))) then 2 else 0)
					  val lcabthmnm = lhs(concl(Option.valOf(List.hd abthml)))
					  val rcabthmnm = lhs(concl(Option.valOf(List.last abthml)))
                                          val abthm = let val vnm = "frv"^(int_to_string (!guid))
                                                      in hd(Defn.eqns_of(Hol_defn (vnm) 
										  `^(mk_eq(mk_var(vnm,type_of mf),
											   ``Or (^lcabthmnm) (^rcabthmnm)``))`)) end
                                          val _ = (guid := (!guid)+1)
                                          val ithm = mk_inv_thm opr [lcabthmnm,rcabthmnm] env ithml githms state chc msp seth abthml
					  val ithm = PURE_ONCE_REWRITE_RULE [SYM abthm] ithm    
                                      in (ref (NONE,NONE,NONE,env,~1,rsc,ithm,SOME abthm,NONE,NONE),rsc,ithm,SOME abthm)  end
                       | "Not"     => let val chc = (if (is_imp(snd(strip_forall(concl(List.hd ithml))))) then 1 else 0)
					  val cabthmnm = lhs(concl(Option.valOf(List.hd abthml)))
                                          val abthm = let val vnm = "frv"^(int_to_string (!guid))
                                                      in hd(Defn.eqns_of(Hol_defn (vnm) 
									 `^(mk_eq(mk_var(vnm,type_of mf),``Not (^cabthmnm)``))`)) end
                                          val _ = (guid := (!guid)+1)
                                          val ithm = mk_inv_thm opr [cabthmnm] env ithml githms state chc msp seth abthml
					  val ithm = PURE_ONCE_REWRITE_RULE [SYM abthm] ithm    
                                      in (ref (NONE,NONE,NONE,env,~1,rsc,ithm,SOME abthm,NONE,NONE),rsc,ithm,SOME abthm) end
                       | "TR"      => (ref (NONE,NONE,NONE,env,~1,rsc,T_I,SOME (REFL mf),NONE,NONE),rsc,T_I,SOME (REFL mf))
                       | "FL"      => (ref (NONE,NONE,NONE,env,~1,rsc,F_I,SOME (REFL mf),NONE,NONE),rsc,F_I,SOME (REFL mf))
                       | "DIAMOND" => let val _ = DMSG (ST  "cache_add depth DMD\n") (dbgct)(*DBG*)
                                          (*val _ = DMSG (TH   DMD_I) (dbgct) val _ = DMSG (ST  " gen\n") (dbgct)(*DBG*)*)
                                          val chc = (if (is_imp(snd(strip_forall(concl(List.last ithml))))) then 1 else 0)
					  val cabthmnm = lhs(concl(Option.valOf(List.hd abthml)))
					  val actnm = List.hd args
                                          val abthm = let val vnm = "frv"^(int_to_string (!guid))
                                                      in hd(Defn.eqns_of(Hol_defn (vnm) 
									 `^(mk_eq(mk_var(vnm,type_of mf),
										  ``DIAMOND (^actnm) (^cabthmnm)``))`)) end
                                          val _ = (guid := (!guid)+1)
                                          val ithm = mk_inv_thm opr [List.hd args,cabthmnm] env ithml githms state chc msp seth abthml
					  val ithm = PURE_ONCE_REWRITE_RULE [SYM abthm] ithm    
                                      in (ref (NONE,NONE,NONE,env,~1,rsc,ithm,SOME abthm,NONE,NONE),rsc,ithm,SOME abthm) end
                       | "BOX"     => let val _ = DMSG (ST  "cache_add depth BOX\n") (dbgct)(*DBG*)
                                          (*val _ = DMSG (TH   BOX_I) (dbgct) val _ = DMSG (ST  " gen\n") (dbgct)(*DBG*)*)
                                          val chc = (if (is_imp(snd(strip_forall(concl(List.last ithml))))) then 1 else 0)
					  val cabthmnm = lhs(concl(Option.valOf(List.hd abthml)))
					  val actnm = List.hd args
                                          val abthm = let val vnm = "frv"^(int_to_string (!guid))
                                                      in hd(Defn.eqns_of(Hol_defn (vnm) 
									 `^(mk_eq(mk_var(vnm,type_of mf),
										  ``BOX (^actnm) (^cabthmnm)``))`)) end
                                          val _ = (guid := (!guid)+1)
                                          val ithm = mk_inv_thm opr [List.hd args,cabthmnm] env ithml githms state chc msp seth abthml
					  val ithm = PURE_ONCE_REWRITE_RULE [SYM abthm] ithm    
                                      in (ref (NONE,NONE,NONE,env,~1,rsc,ithm,SOME abthm,NONE,NONE),rsc,ithm,SOME abthm) end
                       | "mu"      => let val _ = DMSG (ST  "cache_add depth mu\n") (dbgct)(*DBG*)
                                          val chc = (if (is_imp(snd(strip_forall(concl(List.last ithml))))) then 1 else 0)
					  val cabthmnm = lhs(concl(Option.valOf(List.hd abthml)))
					  val rvnm = List.hd args
                                          val abthm = let val vnm = "frv"^(int_to_string (!guid))
                                                      in hd(Defn.eqns_of(Hol_defn (vnm) 
									 `^(mk_eq(mk_var(vnm,type_of mf),
										  ``mu (^rvnm) .. (^cabthmnm)``))`)) end
                                          val _ = (guid := (!guid)+1)
                                          val ithm = mk_inv_thm opr [List.hd args,cabthmnm] env ithml githms state chc msp seth abthml
					  val ithm = PURE_ONCE_REWRITE_RULE [SYM abthm] ithm    
                                      in  (ref (NONE,NONE,NONE,env,~1,rsc,ithm,SOME abthm,NONE,NONE),rsc,ithm,SOME abthm) end
                       | "nu"      => let val _ = DMSG (ST  "cache_add depth nu\n") (dbgct)(*DBG*)
                                          val chc = (if (is_imp(snd(strip_forall(concl(List.last ithml))))) then 1 else 0)
					  val cabthmnm = lhs(concl(Option.valOf(List.hd abthml)))
					  val rvnm = List.hd args
                                          val abthm = let val vnm = "frv"^(int_to_string (!guid))
                                                      in hd(Defn.eqns_of(Hol_defn (vnm) 
									 `^(mk_eq(mk_var(vnm,type_of mf),
										  ``nu (^rvnm) .. (^cabthmnm)``))`)) end
                                          val _ = (guid := (!guid)+1)
                                          val ithm = mk_inv_thm opr [List.hd args,cabthmnm] env ithml githms state chc msp seth abthml
					  val ithm = PURE_ONCE_REWRITE_RULE [SYM abthm] ithm    
                                      in (ref (NONE,NONE,NONE,env,~1,rsc,ithm,SOME abthm,NONE,NONE),rsc,ithm,SOME abthm) end
                       | _         => Raise Match
           in (en,(Binarymap.insert(ce,cekey,en),rsc,ithm,abthm)) end 
    end
| cache_add depth rvnm2ix env mf mfo ce rsc rvty ithml githms state seth msp guid abthml = Raise Match

(* take two reverse scopes and merge into one *)
fun rcs_merge r1 r2 =
    Vector.mapi (fn (i,_) => if (Vector.sub(r1,i)>Vector.sub(r2,i)) then Vector.sub(r1,i) else Vector.sub(r2,i))
    (Vector.tabulate(Vector.length r1,fn i => 0),0,NONE)

fun BST_merge b1 b2 = Binarymap.foldl (fn (k,v,ab) => Binarymap.insert(ab,k,v)) b1 b2

(* ASSERT: mf = uniq mf (fv mf) [] *)
fun mk_cache_aux ee rvnm2ix env mf mfo ce rscope depth rvty githms state seth msp guid tysimps =
    let         
	val _ = DMSG (ST  ("mk_cache_aux ee\n")) (dbgct)(*DBG*)
	val (opr,args) = strip_comb mf
	val (opro,argso) = strip_comb mfo
        val prop_type = List.hd(snd(dest_type(type_of mf)))
        val _ = DMSG (TM  mf) (dbgct) val _ = DMSG (ST  " mf\n") (dbgct)(*DBG*)
        val lab = ""(*DBG*)
    in case (fst(dest_const opr)) of
           "TR" => let val (pt,(ce1,rsc,ithm,abthm)) = cache_add depth rvnm2ix env mf mfo ce rscope rvty [] githms state seth msp guid []

		       val frv = lhs(concl (Option.valOf abthm))
                   in ((muTR pt,(Binarymap.mkDict Term.compare),Binarymap.insert((Binarymap.mkDict Term.compare),frv,Option.valOf abthm)),
		       (ce1,rsc,ithm,abthm,Option.valOf abthm)) end
         | "FL" => let val (pt,(ce1,rsc,ithm,abthm)) = cache_add depth rvnm2ix env mf mfo ce rscope rvty [] githms state seth msp guid []

		       val frv = lhs(concl (Option.valOf abthm))
                   in ((muFL pt,(Binarymap.mkDict Term.compare),Binarymap.insert((Binarymap.mkDict Term.compare),frv,Option.valOf abthm)),
		       (ce1,rsc,ithm,abthm,Option.valOf abthm)) end
         | "RV" => let val (pt,(ce1,rsc,ithm,abthm)) = cache_add depth rvnm2ix env mf mfo ce rscope rvty [] githms state seth msp guid []

		       val frv = lhs(concl (Option.valOf abthm))
                   in ((muRV pt,(Binarymap.mkDict Term.compare),Binarymap.insert((Binarymap.mkDict Term.compare),frv,Option.valOf abthm)),
		       (ce1,rsc,ithm,abthm,Option.valOf abthm)) end
         | "AP" => let val (pt,(ce1,rsc,ithm,abthm)) = cache_add depth rvnm2ix env mf mfo ce rscope rvty [] githms state seth msp guid []

		       val frv = lhs(concl (Option.valOf abthm))
                   in ((muAP pt,(Binarymap.mkDict Term.compare),Binarymap.insert((Binarymap.mkDict Term.compare),frv,Option.valOf abthm)),
		       (ce1,rsc,ithm,abthm,Option.valOf abthm)) end
         | "Not" => let val ((pt1,imfs,abs),(ce1,rsc,ithm,abthm,xabthm)) = mk_cache_aux ee rvnm2ix env (List.hd args) (List.hd argso) ce
                                                                rscope depth rvty githms state seth msp guid tysimps 
                        val (pt,(ce2,rsc2,ithm,abthm)) = cache_add depth rvnm2ix env mf mfo ce1 rsc rvty 
								   [ithm] githms state seth msp guid [abthm]
			val xabthm = PURE_ONCE_REWRITE_RULE [xabthm] (Option.valOf abthm)
			val abs = Binarymap.insert(abs,lhs(concl (xabthm)),xabthm)
                    in ((muNot(pt,pt1),imfs,abs),(ce2,rsc2,ithm,abthm,xabthm)) end
         | "And" => let val ((ptl,imfsl,absl),(ce1,rsc,it1,ab1,xab1)) = mk_cache_aux ee rvnm2ix env (List.hd args) (List.hd argso) ce
                                                               rscope depth rvty githms state seth msp guid tysimps 
                        val ((ptr,imfsr,absr),(ce2,rsc2,it2,ab2,xab2)) = mk_cache_aux ee rvnm2ix env (List.last args) (List.last argso) ce1
                                                                rsc depth rvty githms state seth msp guid tysimps 
                        val (pt,(ce3,rsc3,ithm,abthm)) = cache_add depth rvnm2ix env mf mfo ce2
                                                             (rcs_merge rsc rsc2) rvty [it1,it2] githms state seth msp guid [ab1,ab2]
			val xabthm = PURE_ONCE_REWRITE_RULE [xab1] (PURE_ONCE_REWRITE_RULE [xab2] (Option.valOf abthm))
			val abs = Binarymap.insert(BST_merge absl absr,lhs(concl (xabthm)),xabthm)
                    in ((muAnd(pt,(ptl,ptr)),BST_merge imfsl imfsr,abs),(ce3,rsc3,ithm,abthm,xabthm)) end
         | "Or" => let val ((ptl,imfsl,absl),(ce1,rsc,it1,ab1,xab1)) = mk_cache_aux ee rvnm2ix env (List.hd args) (List.hd argso) ce
                                                              rscope depth rvty githms state seth msp guid tysimps 
                        val ((ptr,imfsr,absr),(ce2,rsc2,it2,ab2,xab2)) = mk_cache_aux ee rvnm2ix env (List.last args) (List.last argso) ce1
                                                                rsc depth rvty githms state seth msp guid tysimps 
                        val (pt,(ce3,rsc3,ithm,abthm)) = cache_add depth rvnm2ix env mf mfo ce2
                                                             (rcs_merge rsc rsc2) rvty [it1,it2] githms state seth msp guid [ab1,ab2]
			val xabthm = PURE_ONCE_REWRITE_RULE [xab1] (PURE_ONCE_REWRITE_RULE [xab2] (Option.valOf abthm))
			val abs = Binarymap.insert(BST_merge absl absr,lhs(concl (xabthm)),xabthm)
                   in ((muOr(pt,(ptl,ptr)),BST_merge imfsl imfsr,abs),(ce3,rsc3,ithm,abthm,xabthm)) end
         | "DIAMOND" => let val ((pt1,imfs,abs),(ce1,rsc,ithm,ab,xab)) = mk_cache_aux ee rvnm2ix env (List.last args) (List.last argso) ce
                                                                    rscope depth rvty githms state seth msp guid tysimps 
                            val (pt,(ce2,rsc2,ithm,ab))=cache_add depth rvnm2ix env mf mfo ce1 rsc rvty 
								  [ithm] githms state seth msp guid [ab]
			    val xabthm = PURE_ONCE_REWRITE_RULE [xab] (Option.valOf ab)
			    val abs = Binarymap.insert(abs,lhs(concl (xabthm)),xabthm)
                        in ((muDIAMOND(pt,(fromHOLstring(List.hd args),pt1)),imfs,abs),(ce2,rsc2,ithm,ab,xabthm)) end
         | "BOX" => let val ((pt1,imfs,abs),(ce1,rsc,ithm,ab,xab)) =mk_cache_aux ee rvnm2ix env (List.last args) (List.last argso) ce
                                                                rscope depth rvty githms state seth msp guid tysimps 
                        val (pt,(ce2,rsc2,ithm,ab)) =cache_add depth rvnm2ix env mf mfo ce1 rsc rvty [ithm] githms state seth msp guid [ab]
			val xabthm = PURE_ONCE_REWRITE_RULE [xab] (Option.valOf ab)
			val abs = Binarymap.insert(abs,lhs(concl (xabthm)),xabthm)
                    in ((muBOX(pt,(fromHOLstring(List.hd args),pt1)),imfs,abs),(ce2,rsc2,ithm,ab,xabthm)) end
         | "mu" =>  let val tirv = inst [``:'a``|->prop_type] ``RV``
                        val (ptr,(ce0,rsc,ithm,abthm)) = cache_add (depth+1)
								    ((fromHOLstring(List.hd args),depth)::rvnm2ix)
                                              env (mk_comb(tirv,List.hd args)) (mk_comb(tirv,List.hd argso)) ce rscope
                                              ((List.hd args,false)::rvty) [] githms state seth msp guid []
                        val ((pt1,imfs,abs),(ce1,rsc,ithm,abthm,xabthm)) = mk_cache_aux ee                                            
									       ((fromHOLstring(List.hd args),depth)::rvnm2ix)
                                            env (List.last args) (List.last argso) ce0 rscope (depth+1)
                                            ((List.hd args,false)::rvty) githms state seth msp guid tysimps 
			val abs = Binarymap.insert(abs,List.last args,xabthm)
                        val (pt,(ce2,rsc2,ithm,abthm)) = cache_add depth rvnm2ix env mf mfo ce1
                                                        (Vector.mapi (fn (i,v) => if (i=depth) then 0 else v) (rsc,0,NONE))
                                                        rvty [ithm] githms state seth msp guid [abthm]
			val xabthm = PURE_ONCE_REWRITE_RULE [xabthm] (Option.valOf abthm)
			val imfth = PURE_ONCE_REWRITE_RULE [SYM xabthm] (mk_imf_thm mf tysimps prop_type)
			val abs = Binarymap.insert(abs,lhs(concl (xabthm)),xabthm)
			val _ = DMSG (ST  "mu done\n") (dbgct)
                    in ((fpmu(ptr,pt,pt1),Binarymap.insert(imfs,mf,imfth),abs),(ce2,rsc2,ithm,abthm,xabthm)) 
		    end
         | "nu" =>  let val tirv = inst [``:'a``|->prop_type] ``RV``
			val (ptr,(ce0,rsc,ithm,abthm)) = cache_add (depth+1)  
							     ((fromHOLstring(List.hd args),depth)::rvnm2ix)
                                              env (mk_comb(tirv,List.hd args)) (mk_comb(tirv,List.hd argso)) ce rscope
                                              ((List.hd args,true)::rvty) [] githms state seth msp guid []
                        val ((pt1,imfs,abs),(ce1,rsc,ithm,abthm,xabthm)) = mk_cache_aux ee                                            
					     ((fromHOLstring(List.hd args),depth)::rvnm2ix)
                                            env (List.last args) (List.last argso) ce0 rscope (depth+1)
                                            ((List.hd args,true)::rvty) githms state seth msp guid tysimps 
			val abs = Binarymap.insert(abs,List.last args,xabthm)
                        val (pt,(ce2,rsc2,ithm,abthm)) = cache_add depth rvnm2ix env mf mfo ce1
                                                        (Vector.mapi (fn (i,v) => if (i=depth) then 0 else v) (rsc,0,NONE))
                                                        rvty [ithm] githms state seth msp guid [abthm]
			val xabthm = PURE_ONCE_REWRITE_RULE [xabthm] (Option.valOf abthm)
			val imfth = PURE_ONCE_REWRITE_RULE [SYM xabthm] (mk_imf_thm mf tysimps prop_type)
			val abs = Binarymap.insert(abs,lhs(concl (xabthm)),xabthm)
			val _ = DMSG (ST  "nu done\n") (dbgct)
                    in ((fpnu(ptr,pt,pt1),Binarymap.insert(imfs,mf,imfth),abs),(ce2,rsc2,ithm,abthm,xabthm))
		    end
         | _         => failwith ("mk_cache_aux Match:"^(term_to_string mf)) end


fun mk_cache ee env mf mfo qd githms state seth msp = 
    let (*val _ = DMSG (TM  mf) (dbgct)*)(*DBG*)
	val _ = DMSG (ST  " mk_cache\n") (dbgct)(*DBG*)
        (* make a mapping from rv's to their index in ee *) 
	(*val rvnm2ix = fst(Array.foldl (fn ((k,tb),(bm,n)) => (Binarymap.insert(bm,k,n),n+1)) 
				      (Binarymap.mkDict String.compare,0) ee)*)
	val rvnm2ix = fst(Array.foldl(fn ((k,tb),(l,n)) => ((k,n)::l,n+1)) ([],0) ee)
    in 
	fst (mk_cache_aux ee rvnm2ix env mf mfo (Binarymap.mkDict Term.compare)
                          (Vector.tabulate(qd+(List.length rvnm2ix),fn ix => 0))
                          (List.length rvnm2ix)
                          []  githms state seth msp (ref 0)
			  ((List.hd(CONJUNCTS(List.last(tsimps "mu"))))
			   ::((List.filter (fn th => can (match_term 
							(``~(((RV a):'prop mu) = (b:'prop mu))``)) 
					    (concl (SPEC_ALL th))) (tsimps "mu"))@
			      (List.filter (fn th => can (match_term 
							(``~(((Not a):'prop mu) = (b:'prop mu))``)) 
					    (concl (SPEC_ALL th))) (tsimps "mu"))),
			   (List.map (fn (rv,eqs) => eqs) (flatten(List.map (fn (rv,bm)=>Binarymap.listItems bm) 
									    (Binarymap.listItems seth)))))) 
    end


fun upd_cch_tb cch tb = let val (a,b,c,d,e,f,g,h,i,j) = !cch in (cch:=(SOME tb,b,c,d,e,f,g,h,i,j)) end
fun upd_cch_gth cch gth = let val (a,b,c,d,e,f,g,h,i,j) = !cch in (cch:=(a,SOME gth,c,d,e,f,g,h,i,j)) end
fun upd_cch_sth cch sth = let val (a,b,c,d,e,f,g,h,i,j) = !cch in (cch:=(a,b,SOME sth,d,e,f,g,h,i,j)) end
fun upd_cch_env cch env = let val (a,b,c,d,e,f,g,h,i,j) = !cch in (cch:=(a,b,c,env,e,f,g,h,i,j)) end
fun upd_cch_subth cch subth = let val (a,b,c,d,e,f,g,h,i,j) = !cch in (cch:=(a,b,c,d,e,f,g,h,SOME subth,j)) end
fun upd_cch_eqth cch eqth = let val (a,b,c,d,e,f,g,h,i,j) = !cch in (cch:=(a,b,c,d,e,f,g,h,i,SOME eqth)) end

fun mk_ado_sub_thm ado ado_subthm t2 ksname ie1 eeq imf_thms abthm wfKS_ks ie t1 initset finset seth imf_t2 ess eus chainth n =
    let 
	(* make ado sub_thm i.e.initset SUBSET STATES f ks e[[[Q<--initset]]],used to discharge GEN_MU_FP_STATES *)
	val _ = DMSG (ST  "mk_ado_sub_thm\n") (dbgct)(*DBG*)
	val _ = DMSG (TM  initset) (dbgct) val _ = DMSG (ST  " ADO initset\n") (dbgct)(*DBG*)
	val _ = DMSG (TM  finset) (dbgct) val _ = DMSG (ST  " ADO finset\n") (dbgct)(*DBG*)
        in if (Term.compare(initset,finset)=EQUAL) then ado_subthm else 
	let 
	    val n = rand finset
	    val _ = DMSG (TH    (ISPECL [t2,ksname,ie,n,t1,initset] chainth)) (dbgct) val _ = DMSG (ST  " spec glc\n") (dbgct)(*DBG*)
 	    val _ = DMSG (TH   ado_subthm) (dbgct) val _ = DMSG (ST  " prev ado_subthm\n") (dbgct)(*DBG*)
            val ado_subthm = (MP (ISPECL [t2,ksname,ie,n,t1,initset] chainth)
			      (LIST_CONJ [wfKS_ks,PURE_ONCE_REWRITE_RULE [abthm] imf_t2,ado_subthm]))
	    val ado_subthm'' = CONV_RULE (RAND_CONV(ONCE_REWRITE_CONV [STATES_def] 
						    THENC REWRITE_CONV [ENV_EVAL,ENV_UPDATE])) ado_subthm		   
	    val _ = DMSG (TH   ado_subthm'') (dbgct)  val _ = DMSG (ST  " init ado_subthm\n") (dbgct)(*DBG*)
	in ado_subthm'' end
    end

fun lift_ado_sub_thm ado ado_subthm t2 ksname ie1 eeq imf_thms abthm wfKS_ks ie t1 initset seth imf_t2 ess Ss eus adogeneqthm initsubth n =
    let 
	(* make ado sub_thm i.e.initset SUBSET STATES f ks e[[[Q<--initset]]],used to discharge GEN_MU_FP_STATES *)
	val _ = DMSG (ST  "lift_ado_sub_thm\n") (dbgct)(*DBG*)
	val _ = DMSG (TM  initset) (dbgct) val _ = DMSG (ST  " ADOlift initset\n") (dbgct)(*DBG*)
	val n = if ((Term.compare(initset,ess)=EQUAL) orelse (Term.compare(initset,Ss)=EQUAL)) then numSyntax.zero_tm else rand initset
	val prev_adosubthm = if ado then (Option.valOf ado_subthm)
			     else (ISPEC ``STATES ^t2 ^ksname ^ie1`` initsubth) 
	val _ = DMSG (TH   prev_adosubthm) (dbgct) val _ = DMSG (ST  " ADOlift prev ado_subthm\n") (dbgct) (*DBG*)
        val _ = if (not (null eeq)) then DMSG (TH  (fst (hd eeq))) (dbgct) else DMSG (ST  "empty") (dbgct) val _ = DMSG (ST  " ADOlift hd eeq\n") (dbgct) (*DBG*) 
        val ado_subthm = 
	    if ado then 
		let 
		    val _ = DMSG (TM  t2) (dbgct) val _ = DMSG (ST  " ADOlift t1\n") (dbgct)(*DBG*)
		    val _ = DMSG (TH (Binarymap.find(imf_thms,t2))) (dbgct) val _ = DMSG (ST  " ADOlift prev imf th\n") (dbgct)(*DBG*)
		    val _ = DMSG (TH   (snd(hd eeq))) (dbgct) val _ = DMSG (ST  " ADOlift prev ab th\n") (dbgct)(*DBG*)
		    val _ = DMSG (TH   abthm) (dbgct) val _ = DMSG (ST  " ADOlift curr ab th\n") (dbgct)(*DBG*)
		    val prevth = MATCH_MP STATES_MONO_EQ 
			(LIST_CONJ [wfKS_ks,PURE_ONCE_REWRITE_RULE [snd(hd eeq)] (Binarymap.find(imf_thms,t2)),
				    PURE_ONCE_REWRITE_RULE [adogeneqthm] (fst(hd eeq))])   
		    val _ = DMSG (TH   prevth) (dbgct) val _ = DMSG (ST  " ADOlift prev th\n") (dbgct)(*DBG*)
                    val (ie0,(t1o,_)) = dest_env ie
		    val ie0' = list_mk_comb(eus,[ie0,t1,initset])
		    val prevth2 = REWRITE_RULE [MATCH_MP ENV_SWAP (Binarymap.find(Binarymap.find(seth,fromHOLstring t1),
										  fromHOLstring t1o))] (SPEC ie0' prevth)
		    val _ = DMSG (TH   prevth2) (dbgct) val _ = DMSG (ST  " ADOlift prev th 2\n") (dbgct)(*DBG*)
		in MATCH_MP SUBSET_TRANS (LIST_CONJ [prev_adosubthm,prevth2]) end
	    else  prev_adosubthm
	val _ = DMSG (TH   ado_subthm) (dbgct)  val _ = DMSG (ST  " lifted ado_subthm\n") (dbgct)(*DBG*)
    in  ado_subthm end

fun mk_ado_pre_sub_thm ado ado_subthm t2 ksname ie1 eeq imf_thms abthm wfKS_ks ie t1 initset seth imf_t2 ess eus chainth adogeneqthm initsubth n =
    let 
	(* make ado sub_thm i.e.initset SUBSET STATES f ks e[[[Q<--initset]]],used to discharge GEN_MU_FP_STATES *)
	val _ = DMSG (TM  initset) (dbgct) val _ = DMSG (ST  " ADOpre initset\n") (dbgct)(*DBG*)
	val _ = DMSG (TH  (ISPECL [t2,ksname,ie,n,t1,initset] chainth)) (dbgct) val _ = DMSG (ST  " ADOpre spec glc\n") (dbgct)(*DBG*)
	val prev_adosubthm = if ado then (Option.valOf ado_subthm)
			     else (ISPEC ``STATES ^t2 ^ksname ^ie1`` initsubth) 
	val _ = DMSG (TH   prev_adosubthm) (dbgct) val _ = DMSG (ST  " ADOpre prev ado_subthm\n") (dbgct) (*DBG*)
	val _ = if (not (null eeq)) then DMSG (TH  (fst (hd eeq))) (dbgct) else DMSG (ST  "empty") (dbgct) val _ = DMSG (ST  " hd eeq\n") (dbgct)(*DBG*) 
	val ado_subthm' = 
	    if ado then 
		let 
		    val _ = DMSG (TM  t2) (dbgct) val _ = DMSG (ST  " ADOpre t1\n") (dbgct)(*DBG*)
		    val _ = DMSG (TH   (Binarymap.find(imf_thms,t2))) (dbgct) val _ = DMSG (ST  " ADO prev imf th\n") (dbgct)(*DBG*)
		    val _ = DMSG (TH   (snd(hd eeq))) (dbgct) val _ = DMSG (ST  " ADO prev ab th\n") (dbgct)(*DBG*)
	            val _ = DMSG (TH   abthm) (dbgct) val _ = DMSG (ST  " ADOpre curr ab th\n") (dbgct)(*DBG*)
	            val prevth = MATCH_MP STATES_MONO_EQ 
			(LIST_CONJ [wfKS_ks,PURE_ONCE_REWRITE_RULE [snd(hd eeq)] (Binarymap.find(imf_thms,t2)),
				    PURE_ONCE_REWRITE_RULE [adogeneqthm] (fst(hd eeq))])   
		    val _ = DMSG (TH   prevth) (dbgct) val _ = DMSG (ST  " ADOpre prev th\n") (dbgct)(*DBG*)
                    val (ie0,(t1o,_)) = dest_env ie
		    val ie0' = list_mk_comb(eus,[ie0,t1,initset])
		    val prevth2 = REWRITE_RULE [MATCH_MP ENV_SWAP (Binarymap.find(Binarymap.find(seth,fromHOLstring t1),
										  fromHOLstring t1o))] (SPEC ie0' prevth)
		    val _ = DMSG (TH   prevth2) (dbgct) val _ = DMSG (ST  " ADOpre prev th 2\n") (dbgct)(*DBG*)
		in MATCH_MP SUBSET_TRANS (LIST_CONJ [prev_adosubthm,prevth2]) end
	    else (MP (ISPECL [t2,ksname,ie,n,t1,initset] chainth)
		  (LIST_CONJ [wfKS_ks,PURE_ONCE_REWRITE_RULE [abthm] imf_t2,prev_adosubthm]))
	val _ = DMSG (TH   ado_subthm') (dbgct)  val _ = DMSG (ST  " ado_presubthm'\n") (dbgct)(*DBG*)
    in ado_subthm' end

(* called by muCheck.mk_gen_thms *)
fun mk_gen_inv_thms ksname state wfKS_ks =
    let 
	val _ = DMSG (ST ("(make_gen_inv)\n")) (dbgct) (*DBG*)
    in 
	[ISPECL [ksname] SAT_AP_ENV_INV, ISPECL [ksname] SAT_RV_ENV_INV, ISPECL [ksname] SAT_T_ENV_INV, ISPECL [ksname] SAT_F_ENV_INV,
	 MATCH_MP (ISPECL [ksname] SAT_NEG_ENV_INV) wfKS_ks, MATCH_MP (ISPECL [ksname] SAT_NEG_ENV_INV2) wfKS_ks,
	 ISPECL [ksname] SAT_CONJ_ENV_INV,ISPECL [ksname] SAT_CONJ_ENV_INV2,
	 ISPECL [ksname] SAT_DISJ_ENV_INV,ISPECL [ksname] SAT_DISJ_ENV_INV2,
	 ISPECL [ksname] SAT_DMD_ENV_INV, ISPECL [ksname] SAT_DMD_ENV_INV2,
	 ISPECL [ksname] SAT_BOX_ENV_INV, ISPECL [ksname] SAT_BOX_ENV_INV2,
	 ISPECL [ksname,state] SAT_LFP_ENV_INV, ISPECL [ksname] SAT_LFP_ENV_INV2,
	 ISPECL [ksname,state] SAT_GFP_ENV_INV, ISPECL [ksname] SAT_GFP_ENV_INV2] 
    end


fun mk_ado_imf_goals [] =  []
| mk_ado_imf_goals sigfl = 
    let 
	val _ = DMSG (ST ("mk_ado_imf_goals\n")) (dbgct) (*DBG*)
	val sfl2 = List.filter (fn (_,l) => not (null l)) (List.map (fn f => (f,top_sigma (is_nu f) (rand f))) sigfl)
	val prop_type = hd(snd(dest_type(type_of (hd sigfl))))
	val ip = inst [alpha|->prop_type] 
	val gls = List.map (fn (f,sfl) => List.map (fn sf => mk_comb((ip ``IMF``),
								     list_mk_comb(ip(if is_nu f then ``$nu`` else ``$mu``),
										  [rand (rator f),rand sf]))) sfl) sfl2 
	val res = (List.concat gls)@(mk_ado_imf_goals (List.concat (List.map snd sfl2))) 
	val _ = DMSG (ST ("mk_ado_imf_goals done\n")) (dbgct) (*DBG*)
    in res end

(* for each sigma formula sig Q.f, if there exists in f a top-level sig formula of the same type (mu/nu) sig P.g, then prove that
   IMF Q. g *)
fun mk_ado_imf_thms mf seth tysimps frv_thms imf_thms= 
    let 
	val _ = DMSG (ST ("mk_ado_imf_thms\n")) (dbgct) (*DBG*)
        val sigfl = (top_sigma true mf)@(top_sigma false mf)
	val prop_type = hd(snd(dest_type(type_of mf)))
	val _ = DMSG (TY prop_type) (dbgct) val _ = DMSG (ST  "ptype\n") (dbgct)
	val ip = inst [alpha|->prop_type] 
        val res = if null sigfl then imf_thms 
		  else let 
			   val gls = mk_ado_imf_goals sigfl     
			   val res = List.foldl (fn (gl,bm) => 
						 let val th = prove(gl,SIMP_TAC std_ss 
								    ([IMF_def,MU_SUB_def,NNF_def,RVNEG_def]
								     @tysimps@(List.map (fn (rv,eqs) => eqs) 
									       (flatten(List.map (fn (rv,bm)=>Binarymap.listItems bm) 
											(Binarymap.listItems seth))))))
						     val _ = DMSG (TH   th) (dbgct) val _ = DMSG (ST  " ADO imf th\n") (dbgct)(*DBG*)
						     val frv_thm = Binarymap.find(frv_thms,rand (rand gl))		 
						     val _ = DMSG (TH   frv_thm) (dbgct)(*DBG*)
						     val _ = DMSG (ST  " ADO ab th\n") (dbgct)(*DBG*)
						     val th1 = ONCE_REWRITE_RULE [SYM frv_thm] th 
						     val _ = DMSG (TH th1) (dbgct) val _ = DMSG (ST " ab ADO imf th\n") (dbgct)(*DBG*)
						 in Binarymap.insert(bm,lhs(concl frv_thm),th1) end) 
						imf_thms gls
		       in res end 
	val _ = DMSG (ST ("mk_ado_imf_thms done\n")) (dbgct) (*DBG*)
    in res end

(* return the alternation depth of the given formula *)
fun alt_depth mf = 
   let val (opr,args) = strip_comb mf
    in case (fst(dest_const opr)) of
           "TR" => 0
         | "FL"  => 0
         | "Not" => alt_depth (List.hd args)
         | "And" => Int.max(alt_depth (List.hd args),alt_depth (List.last args))
         | "Or" =>  Int.max(alt_depth (List.hd args),alt_depth (List.last args))
         | "RV" => 0
         | "AP" => 0
         | "DIAMOND" => alt_depth (List.last args)
         | "BOX" => alt_depth (List.last args)
         | "mu" => listmax [1,alt_depth (List.last args),1+listmax (List.map alt_depth (top_sigma true (List.last args)))]
         | "nu" => listmax [1,alt_depth (List.last args),1+listmax (List.map alt_depth (top_sigma false (List.last args)))]
         | _         => failwith ("alt_depth Match:"^(term_to_string mf)) end

(* return the max same-quantifier nesting depth of the given formula *)
fun sameq_depth mf = 
   let val (opr,args) = strip_comb mf
    in case (fst(dest_const opr)) of
           "TR" => 0
         | "FL"  => 0
         | "Not" => sameq_depth (List.hd args)
         | "And" => Int.max(sameq_depth (List.hd args),sameq_depth (List.last args))
         | "Or" =>  Int.max(sameq_depth (List.hd args),sameq_depth (List.last args))
         | "RV" => 0
         | "AP" => 0
         | "DIAMOND" => sameq_depth (List.last args)
         | "BOX" => sameq_depth (List.last args)
         | "mu" => listmax [1,sameq_depth (List.last args),1+listmax (List.map sameq_depth (top_sigma false (List.last args)))]
         | "nu" => listmax [1,sameq_depth (List.last args),1+listmax (List.map sameq_depth (top_sigma true (List.last args)))]
         | _         => failwith ("sameq_depth Match:"^(term_to_string mf)) end

end 
end


