 
structure minisatProve = 
struct 

local

open Lib boolLib Globals Parse Term Type Thm Drule Conv Feedback FileSys
open dimacsTools satTools SatSolvers satCommonTools minisatParse satConfig dpll def_cnf

 
in 

fun transform_model cnfv lfn model =
    let val model2 = 
	    if isSome cnfv then
		mapfilter (fn l => let val x = hd(free_vars l) 
				       val y = rbapply lfn x 
				   in if is_var y then subst [x|->y] l 
				      else failwith"" end) model 
	    else model
    in model2 end 

fun invoke_solver solver lfn ntm clauseth cnfv vc svm sva tmpname = 
    let 
         val res = 
	    if access(satdir^(getSolverExe solver),[A_EXEC]) 
	    then let val nr = Array.length clauseth
 		    val answer = invokeSat solver T (SOME vc) (SOME nr) svm sva tmpname
 		in
		    (case answer of
			 SOME model => (* returns |- model ==> ~t *)
			 satCheck (transform_model cnfv lfn model) ntm	 
		       | NONE    => (* returns ~t |- F *)
			 (let val rt2o = Dynarray.array(nr,~1)
			  in (case replayMinisatProof (valOf svm) (valOf sva) rt2o nr 
						      (valOf tmpname) solver vc clauseth lfn of
			      SOME th => th
			    | NONE => DPLL_TAUT (dest_neg ntm)) (*trivial problem*)
			  end))
		end
	    else (* do not have execute access to solver binary, or it does not exist *)
		DPLL_TAUT (dest_neg ntm)	       	   
   in res end

exception Sat_counterexample of thm

(* raise exception if countermodel was found, 
   else deduce input term from solver's result *)
fun finalise is_cnf th  = 
    let
 	val res = 
	    if is_imp(concl th)
	    then raise (Sat_counterexample th)
	    else 
		if is_cnf 
		then (NOT_INTRO(DISCH_ALL th))
		else CONV_RULE NOT_NOT_CONV (NOT_INTRO(DISCH_ALL th))
     in res end

(* convert input to term to CNF and write out DIMACS file               *)
(* if infile is SOME name, then assume name.cnf exists and is_cnf=true  *)
(* if is_cnf, then assume tm \equiv ~s where s is in CNF                *)
fun initialise infile is_cnf tm = 
let 
 val res = 
    if isSome infile
    then let val fname = valOf infile
	     val (tm,svm,sva) = genReadDimacs (fname^".cnf")
	     val (cnfv,vc,lfn,clauseth) = to_cnf is_cnf (mk_neg tm)
	 in (cnfv,vc,svm,sva,fname,mk_neg tm,lfn,clauseth) end
    else 
	let 
             val (cnfv,vc,lfn,clauseth) = to_cnf is_cnf (mk_neg tm)
 	    val (tmpname,sva,svm) = 
		generateDimacs (SOME vc) tm (SOME clauseth) 
			       (SOME (Array.length clauseth))
	in (cnfv,vc,svm,sva,tmpname,mk_neg tm,lfn,clauseth) end	
 in res end

fun GEN_SAT_TAUT_PROVE conf tm = 
    let 
         val (cnfv,vc,svm,sva,tmpname,ntm,lfn,clauseth) = 
	    initialise (get_infile conf) (get_flag_is_cnf conf) tm
     in if vc=0 then (* all 'presimp'-ified conjuncts were either T or F *)
	   let val th0 = presimp_conv tm
	       val t0 = rhs (concl th0)
	   in if is_F t0 then raise Sat_counterexample (EQF_ELIM th0) 
	      else EQT_ELIM th0 end else
       let 
            val th = invoke_solver minisatp lfn ntm clauseth cnfv vc 
				  (SOME svm) (SOME sva) (SOME tmpname)
 	   val res = finalise (get_flag_is_cnf conf) th 
        in res end
    end    

val SAT_TAUT_PROVE = GEN_SAT_TAUT_PROVE default_config 

end
end

