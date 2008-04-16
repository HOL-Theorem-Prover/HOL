 
structure satTools = struct

local 

(*
app load ["Binaryset","FileSys","TextIO","Process","Char","String","Substring","Conv"]
*)

open Lib boolLib Globals Parse Term Type Thm Drule Psyntax Conv Feedback
open SatSolvers satCommonTools satTheory

 
in 

infix |->;

(* 
** Use Binaryset to encode mapping between HOL variable names
** and DIMACS  variable numbers as a set of string*int pairs.
*)

(* Functions for parsing the output of SAT solvers *)

(*
** substringContains s ss
** tests whether substring ss contains string s
*)

fun substringContains s ss = not(Substring.isEmpty(snd(Substring.position s ss)));

(*
** parseSat (s1,s2) ss 
** returns a list of numbers corresponding to the tokenised
** substring of ss (tokenised wrt Char.isSpace) that starts immediately 
** after the first occurrence of s1 and ends just before the first 
** occurrence of s2 that is after the first occurrence of s1
*)

fun parseSat (s1,s2) ss =
 let val (ss1,ss2) = Substring.position s1 ss
     val ss3       = Substring.triml (String.size s1) ss2
     val (ss4,ss5) = Substring.position s2 ss3 
     val ssl       = Substring.tokens Char.isSpace ss4
 in
  List.map (valOf o Int.fromString o Substring.string) ssl
 end 
 handle _ => failwith("parseSat");

(*
** Test for success of the result of Process.system
** N.B. isSuccess expected to primitive in next release of
** Moscow ML, and Process.status will lose eqtype status
*)

fun isSuccess s = PreProcess.isSuccess s

(*
** invokeSat solver t
** invokes solver on t and returns SOME s (where s is the satisfying instance
** as a string of integers) or NONE, if unsatisfiable
*)

fun sat_sysl s = Systeml.system_ps s 

fun invokeSat sat_solver tm vc nr svm sva infile =
 let 
      val (name,executable,notime_run,only_true,
          failure_string,start_string,end_string) = 
	 (getSolverName sat_solver,getSolverExe sat_solver,getSolverRun sat_solver,
	  getSolverTrue sat_solver,getSolverFail sat_solver,getSolverStart sat_solver,
	  getSolverEnd sat_solver)
     val outfile    = infile ^ "." ^ name
     val run_cmd    = notime_run executable (infile,outfile)
     val code       = sat_sysl run_cmd
     val _          = if isSuccess code orelse 
                         (name="minisat" orelse name="minisatp") 
		      then () (* minisat returns non-std exit code on success *)
                      else print("Warning:\n Process.system reports failure \
                                 \signal returned by\n " ^ run_cmd ^ "\n")
     val ins        = TextIO.openIn outfile
     val sat_res_ss = Substring.all (TextIO.inputAll ins)
     val _          = TextIO.closeIn ins
     val result     = substringContains failure_string sat_res_ss
 in
  if result 
   then NONE
   else 
    let val model1 = parseSat (start_string,end_string) sat_res_ss
        val model2 = if only_true 
                      then model1 @
                           (map (fn n => 0-n) 
				(subtract (map snd (snd(dimacsTools.showSatVarMap svm))) model1))
                     else model1
    in let val model3 = SOME(map (dimacsTools.intToLiteral sva) model2)
        in model3 end
    end
 end
handle Io _ => NONE

(*
** satCheck [l1,...,ln] t 
** attempts to prove (l1 /\ ... /\ ln) ==> t 
** if it succeeds then the theorem is returned, else
** exception satCheckError is raised
*)

exception satCheckError;
fun satCheck model t =
 (let 
       val mtm  = list_mk_conj model (*  (l1 /\ ... /\ ln) *)
      val th1  = ASSUME mtm (* l1 /\ ... /\ ln |- l1 /\ ... /\ ln *)
      val thl  = map 
                  (fn th => if is_neg(concl th) 
                             then MP (SPEC (dest_neg(concl th))EQF_Imp1) th
                             else MP (SPEC(concl th)EQT_Imp1) th)
                  (CONJUNCTS th1) (* [ l1 /\ ... /\ ln |- l1 = T, ... ] *)
      val subl = map (fn th => lhs(concl th) |-> th) thl (*[l1 |-> l1 /\ ... /\ ln |- l1 = T,...]*)
      val th2 = SUBST_CONV subl t t (* l1 /\ ... /\ ln |- t = t[l1/T,...] *)
      val th3 = CONV_RULE (RHS_CONV computeLib.EVAL_CONV) th2 (* l1 /\ ... /\ ln |- t = T *)
      val th4 = EQT_ELIM th3 (* l1 /\ ... /\ ln |- t *)
  in
   DISCH mtm th4 (* |- l1 /\ ... /\ ln ==> t *)
  end)  handle Interrupt => raise Interrupt
                    |  _ => raise satCheckError;

end
end

