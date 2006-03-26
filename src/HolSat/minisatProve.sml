 
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

(* root clauses had been sorted to make resolve go faster... here we recover the original clauses for the final answer*)
local 

val AND_IMP2 = SPEC_ALL (GSYM AND_IMP)

in

fun recoverRootClause scl cl is_first i c th = 
    let 
         fun recoverDropped () = (*filtered, skipped or unused clause; not abbreviated *)
	    if is_first 
		then DISCH c th
	    else CONV_RULE (EREWR_CONV AND_IMP2) (DISCH c th) 
	fun recoverUsed scli =
	    let val (_,_,dl,cdef) = getRootClause cl scli
 	    in if is_first 
		   then CONV_RULE (LAND_CONV (EREWR_CONV cdef)) (DISCH dl th)
	       else CONV_RULE ((LAND_CONV (EREWR_CONV cdef)) THENC (EREWR_CONV AND_IMP2)) (DISCH dl th)
	    end
	val res = let val scli = Array.sub(scl,i)
		  in if scli=(~1) orelse not (isUsedRootClauseIdx cl scli) 			      
		     then (recoverDropped())
		     else (recoverUsed scli)
		  end
     in res end
end

(* assert: t is an unsatisfiable cnf term whose minisat-p proof trace is in the file fname.minisatp.proof *)
(* if the file does not exist, we will assume that minisatp discovered UNSAT during the read-in phase and 
   did not bother with a proof log. In that case the problem is simple and can be delegated to TAUT_PROVE *)
(* FIXME: I do not like the TAUT_PROVE solution; what is trivial for Minisat may not be so for TAUT_PROVE *)
(* returns |- t = F *)
fun unsatProve t (cl,sk,scl,lsr,cc) rcv vc = 
    let 
 	val (scl,cl,th) = unsatProveResolve (cl,sk,scl,lsr,cc) vc rcv
	val res = let 
 	             val th1 = fst(Vector.foldri (fn (i,c,(th,is_first)) 
						     => (recoverRootClause scl cl is_first i c th,false))
					    (th,true) (rcv,0,NONE))
		     val th2 = CONV_RULE (REWR_CONV IMP_F_EQ_F)  th1
 		 in th2 end
     in res end 

fun getRawRootClause (ROOT (LL l)) = l 
  | getRawRootClause _ = raise Match

(* assumes t is in cnf, invokes minisatp, returns |- t = F or |- model ==> t *)
fun satProve2 t rcv vc = 
    let 
 	val nr = Vector.length rcv 
 	val res = 
	    case invokeSat minisatp NONE t (SOME vc) of
		SOME model => satCheck model t
	      | NONE       => (case parseMinisatProof nr ((!tmp_name)^".minisatp.proof") vc rcv of
				   SOME (cl,sk,scl,lsr,cc) =>
				   unsatProve t (cl,sk,scl,lsr,cc) rcv vc
				 | NONE => tautLib.TAUT_PROVE (mk_eq(t,F)))
     in res end

local
    (* Taken from MN's DPLL chapter in the HOL4-K3 Tutorial *)
    fun transform gv body_eq_F = 
	let val body_imp_F = CONV_RULE (REWR_CONV (GSYM IMP_F_EQ_F)) body_eq_F
 	    val fa_body_imp_F = GENL gv body_imp_F
 	    val ex_body_imp_F = CONV_RULE (REPEATC (LAST_FORALL_CONV FORALL_IMP_CONV)) fa_body_imp_F
 	in CONV_RULE (REWR_CONV IMP_F_EQ_F) ex_body_imp_F end
	
in 

fun SAT_TAUT_PROVE t = 
    let 
         val res = 
	    if is_T t then TRUTH
	    else let val nt = mk_neg t
 		     val _ = (defCNF.dcnfgv := K (mk_var("SP",numLib.num-->bool)))
		     val nt_dcnf_th = defCNF.DEF_CNF_VECTOR_CONV nt
		     val ngv = fromHOLnum (!defCNF.ndefs)
 		     val ovc = length (all_vars t)
		     val vc = ngv + ovc  
 		     val (gv,ntdcnf) = strip_exists (rhs(concl nt_dcnf_th))
		     val res = 
			 if is_F ntdcnf
			 then CONV_RULE (REWR_CONV NOT_NOT) (EQF_ELIM nt_dcnf_th) 
			 else let 
				  val rcv = Vector.fromList (strip_conj ntdcnf)
 				  val th = satProve2 ntdcnf rcv vc
 				  val res = 
				      if is_imp (concl th) 
				      then failwith("Counterexample found")
       				      else let 
                                   val th1 = transform gv th
 				  val th2 = EQF_ELIM (TRANS nt_dcnf_th th1)
	    				   in CONV_RULE (REWR_CONV NOT_NOT) th2 end
 			      in res end
		 in res end
     in res end
end

end
end

 