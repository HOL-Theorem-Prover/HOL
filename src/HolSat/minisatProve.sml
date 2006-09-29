 
structure minisatProve = 
struct 

local

open Lib boolLib Globals Parse Term Type Thm Drule Psyntax Conv Feedback
open satTools dimacsTools SatSolvers minisatResolve satCommonTools 
	      minisatParse satTheory satConfig dpll

 
in 

fun termFromFile fname = 
    let val ins        = TextIO.openIn (fname^".term")
	val res        = TextIO.inputAll ins
	val _          = TextIO.closeIn ins
    in Term [QUOTE res] end

fun termToFile fname t = 
let val fout = TextIO.openOut (fname^".term")
    val _ = TextIO.output (fout,with_flag (show_types,true) term_to_string t)
    val _ = TextIO.flushOut fout
    val _ = TextIO.closeOut fout
in () end

(* assert: t is an unsatisfiable cnf term whose minisat-p proof 
   trace is in the file fname.minisatp.proof *)
(* if the file does not exist, we will assume that minisatp discovered UNSAT 
   during the read-in phase and did not bother with a proof log. 
   In that case the problem is simple and can be delegated to DPLL_TAUT *)
(* assumes t is in cnf, invokes minisatp, returns |- t = F or |- model ==> t *)
fun invoke_solver mcth cnfv nt ntdcnf vc svm sva tmpname = 
    let 
 	val nr = Array.length mcth 
 	val res =
	    let 
 		val answer = invokeSat minisatp ntdcnf (SOME vc) (SOME nr) 
				       (SOME mcth) svm sva tmpname
 	    in
	    (case answer of
		SOME model => (* returns |- model ==> ~t *)
		let val model2 = if isSome cnfv then 
				     List.filter (fn p => Term.compare(hd(free_vars p),
								       valOf cnfv) <> EQUAL)
						 model 
				 else model
		in satCheck model2 nt end 
	      | NONE    => (* returns cnf(~t) = F *)
		(let val rt2o = Dynarray.array(nr,~1)
		 in (case replayMinisatProof (valOf svm) (valOf sva) rt2o nr 
					   (valOf tmpname) minisatp vc mcth of
			SOME th => th
		      | NONE => UNDISCH (EQT_ELIM (dpll.DPLL_TAUT (mk_imp(dest_neg nt,F)))))
		 end))
	    end
     in res end

(* Taken from MN's DPLL chapter in the HOL4-K3 Tutorial *)
fun transform gv body_imp_F = 
    let 
	val fa_body_imp_F = GEN gv body_imp_F
 	val ex_body_imp_F = CONV_RULE (LAST_FORALL_CONV FORALL_IMP_CONV) fa_body_imp_F
     in CONV_RULE (REWR_CONV IMP_F_EQ_F) ex_body_imp_F end

exception Sat_counterexample of thm

fun mk_conjuncts nt_dcnf_th = 
    let 
         val cths = 
	    if is_exists (rhs(concl nt_dcnf_th))
	    then CONJUNCTSR (ASSUME (snd(dest_exists(rhs (concl nt_dcnf_th)))))
	    else CONJUNCTSR (ASSUME (rhs (concl nt_dcnf_th)))
	val mcth = Array.fromList cths 
     in mcth end

fun to_cnf is_cnf t nt =
    if is_cnf 
    then (REWR_CONV NOT_NOT nt,dest_neg t,[],NONE,
	  HOLset.numItems (FVL [t] (HOLset.empty Term.var_compare)))	
    else 
	let val cnfv = mk_var("SP",numLib.num-->bool)
	    val _ = (defCNF.dcnfgv := K cnfv)
 	    val nt_dcnf_th = defCNF.DEF_CNF_VECTOR_CONV nt
 	    val ngv = numSyntax.int_of_term (!defCNF.ndefs)
	    val ovc = HOLset.numItems (FVL [t] (HOLset.empty Term.var_compare))
	    val vc = ngv + ovc  
 	    val (gv,ntdcnf) = strip_exists (rhs(concl nt_dcnf_th))
	in (nt_dcnf_th,ntdcnf,gv,SOME cnfv,vc) end

(* raise exception if countermodel was found, 
   else deduce input term from solver's result *)
fun finalise th gv cnfv is_cnf nt_dcnf_th = 
    if is_imp (concl th) 
    then raise (Sat_counterexample th)
    else let 
              val th0 = DISCH (hd (hyp th)) th
	     val th1 = if gv=[] 
		       then CONV_RULE (REWR_CONV IMP_F_EQ_F) th0 
		       else transform (valOf cnfv) th0
 	     val th2 = 
		 if is_cnf 
		 then EQF_ELIM th1
		 else CONV_RULE (REWR_CONV NOT_NOT)
				(EQF_ELIM (TRANS nt_dcnf_th th1))
	in th2 end

(* convert input to term to CNF and write out DIMACS file *)
(* if infile is SOME name, then assume name.cnf exists and is_cnf=true  *)
(* if is_cnf, then assume t=~s and s is in CNF *)
fun initialise infile is_cnf t = 
    if isSome infile
    then let val fname = valOf infile
	     val (t,svm,sva) = genReadDimacs (fname^".cnf")
	     val t = mk_neg t
	     val nt = mk_neg t
	     val (nt_dcnf_th,ntdcnf,gv,cnfv,vc) = to_cnf is_cnf t nt
	     val mcth = mk_conjuncts nt_dcnf_th
	 in (SOME (nt_dcnf_th,ntdcnf,gv,cnfv,vc,mcth,nt,svm,sva,fname),TRUTH) end
    else 
	if is_T t 
	then (NONE,TRUTH)
	else 
	    let val nt = mk_neg t 
		val (nt_dcnf_th,ntdcnf,gv,cnfv,vc) = to_cnf is_cnf t nt
	    in 
		if is_F ntdcnf
		then (NONE, CONV_RULE (REWR_CONV NOT_NOT) (EQF_ELIM nt_dcnf_th))
		else let 
			val mcth = mk_conjuncts nt_dcnf_th
			val (tmpname,sva,svm) = 
			    generateDimacs (SOME vc) t (SOME mcth) 
					   (SOME (Array.length mcth))
		    in (SOME (nt_dcnf_th,ntdcnf,gv,cnfv,vc,mcth,nt,svm,sva,tmpname),TRUTH) end
	    end

fun GEN_SAT_TAUT_PROVE conf t = 
    let 
         val (init,th0) = initialise (get_infile conf) (get_flag_is_cnf conf) t
    in if isSome init 
       then 
	   let 
 	       val (nt_dcnf_th,ntdcnf,gv,cnfv,vc,mcth,nt,svm,sva,tmpname) = valOf init
               val th = invoke_solver mcth cnfv nt ntdcnf vc (SOME svm) (SOME sva) (SOME tmpname)
 	       val res = finalise th gv cnfv (get_flag_is_cnf conf) nt_dcnf_th
 	 in res end
       else th0
    end

val SAT_TAUT_PROVE = GEN_SAT_TAUT_PROVE default_config 

end

end


