 
structure minisatProve = 
struct 

local

open Lib boolLib Globals Parse Term Type Thm Drule Psyntax Conv Feedback
open satTools dimacsTools SatSolvers minisatResolve satCommonTools minisatParse satTheory

 
in 

exception fsatProveError 

(* will return clause info at index ci *)
fun getRootClause cl ci =
    let 
 	val res = case Array.sub(cl,ci) of 
		      ROOT (LL ll) => raise Domain
		    | ROOT (RTHM x) => x
		    | CHAIN _ => raise Domain
		    | LEARNT x => raise Domain
		    | BLANK => raise Domain
     in res end

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

(* assert: if t is NONE then fname.cnf and fname.term have already been created *)
fun fsatOracle sat_solver fname t vc =
 let val SatSolver {name,
                    URL,
                    executable,
                    notime_run,
                    time_run,
                    only_true,
                    failure_string,
                    start_string,
                    end_string} = sat_solver
     val t = if isSome t then (termToDimacsFile (SOME fname) (valOf t) 
			        (if isSome vc then valOf vc else length(all_vars (valOf t)));
			       termToFile fname (valOf t); 
			       valOf t)
	     else termFromFile fname
     val res = invokeSat sat_solver (SOME fname) t vc
 in
  case res of
    SOME l => Thm.mk_oracle_thm (Tag.read name) ([], mk_imp(list_mk_conj l, t))
  | NONE   => Thm.mk_oracle_thm (Tag.read name) ([], mk_neg t)
 end;

(* assert: t is an unsatisfiable cnf term whose minisat-p proof 
   trace is in the file fname.minisatp.proof *)
(* if the file does not exist, we will assume that minisatp discovered UNSAT 
   during the read-in phase and 
   did not bother with a proof log. In that case the problem is simple and 
   can be delegated to TAUT_PROVE *)
(* FIXME: I do not like the TAUT_PROVE solution; 
   what is trivial for Minisat may not be so for TAUT_PROVE *)
(* returns |- t = F *)

fun getRawRootClause (ROOT (LL l)) = l 
  | getRawRootClause _ = raise Match

(* assumes t is in cnf, invokes minisatp, returns |- t = F or |- model ==> t *)
fun invoke_minisat mcth cnfv nt t rcv vc reord = 
    let 
 	val nr = Vector.length rcv 
 	val res = 
	    case invokeSat minisatp NONE t (SOME vc) of
		SOME model => let val model2 = 
				      List.filter (fn p => Term.compare(hd(free_vars p),
									cnfv) <> EQUAL)
						  model 
			      in satCheck model2 nt end (* returns |- model ==> ~t *)
	      | NONE       => (case parseMinisatProof nr ((!tmp_name)^".minisatp.proof") vc rcv of
				   SOME (cl,sk,scl,lsr,cc) =>
		                     unsatProveResolve mcth (cl,sk,scl,lsr,cc) vc rcv reord
				 | NONE => tautLib.TAUT_PROVE (mk_eq(t,F)))
     in res end

local
    (* Taken from MN's DPLL chapter in the HOL4-K3 Tutorial *)
    fun transform gv body_imp_F = 
	let 
	    val fa_body_imp_F = GEN gv body_imp_F
 	    val ex_body_imp_F = CONV_RULE (LAST_FORALL_CONV FORALL_IMP_CONV) fa_body_imp_F
 	in CONV_RULE (REWR_CONV IMP_F_EQ_F) ex_body_imp_F end
	
in 

val do_reorder = ref false

val _ = register_btrace("HolSat_ms_reorder",do_reorder)

exception Sat_counterexample of thm

fun SAT_TAUT_PROVE t = 
    let 
         val res = 
	    if is_T t then TRUTH
	    else let val nt = mk_neg t
 		     val cnfv = mk_var("SP",numLib.num-->bool)
		     val _ = (defCNF.dcnfgv := K cnfv)
		     val nt_dcnf_th = defCNF.DEF_CNF_VECTOR_CONV nt
                     val cths = 
			 if is_exists (rhs(concl nt_dcnf_th))
			 then CONJUNCTS (ASSUME (snd(dest_exists(rhs (concl nt_dcnf_th)))))
			 else CONJUNCTS (ASSUME (rhs (concl nt_dcnf_th)))
                     val mcth = itlist (fn c => fn m => Redblackmap.insert(m,(concl c),c)) cths 
			 (Redblackmap.mkDict Term.compare)
		     val ngv = numSyntax.int_of_term (!defCNF.ndefs)
 		     val ovc = length (all_vars t)
		     val vc = ngv + ovc  
 		     val (gv,ntdcnf) = strip_exists (rhs(concl nt_dcnf_th))
		     val res = 
			 if is_F ntdcnf
			 then CONV_RULE (REWR_CONV NOT_NOT) (EQF_ELIM nt_dcnf_th) 
			 else let 
				  val rcv = Vector.fromList (strip_conj ntdcnf)
 				  val th = invoke_minisat mcth cnfv nt ntdcnf rcv vc (!do_reorder)
 				  val res = 
				      if is_imp (concl th) 
				      then raise (Sat_counterexample th)
       				      else let 
                                                val th0 = DISCH (hd (hyp th)) th
					       val th1 = if gv=[] 
							 then CONV_RULE (REWR_CONV IMP_F_EQ_F) th0 
							 else transform cnfv th0
 					       val th2 = EQF_ELIM (TRANS nt_dcnf_th th1)
	    				  in CONV_RULE (REWR_CONV NOT_NOT) th2 end
 			      in res end
		 in res end
     in res end
end

end
end

 