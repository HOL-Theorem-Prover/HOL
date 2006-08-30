 
structure satTools = struct

local 

(*
app load ["Binaryset","FileSys","TextIO","Process","Char","String","Substring","tautLib","Conv"]
*)

open Lib boolLib Globals Parse Term Type Thm Drule Psyntax Conv Feedback
open dimacsTools SatSolvers 

 
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
** substringToInt converts a substring to an integer
*)

exception substringToIntError;
fun substringToInt ss =
 case Int.fromString(Substring.string ss) of
   SOME n => n
 | _      => raise substringToIntError;

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
  List.map substringToInt ssl
 end;


(*
** invokeSat solver t
** invokes solver on t and returns SOME s (where s is the satisfying instance
** as a string of integers) or NONE, if unsatisfiable
*)

(*
** Reference containing last command used to invoke a SAT solver
*)

val sat_command = ref "undef";

(*
** Test for success of the result of Process.system
** N.B. isSuccess expected to primitive in next release of
** Moscow ML, and Process.status will lose eqtype status
*)

fun isSuccess s = (s = Process.success);

 val satdir = Globals.HOLDIR^"/src/HolSat/"
 
(* if fname is NONE, then use a temp file, otherwise assume fname.cnf alredy exists*)
fun invokeSat sat_solver fname t vc =
 let 
 val SatSolver {name,
                    URL,
                    executable,
                    notime_run,
                    time_run,
                    only_true,
                    failure_string,
                    start_string,
                    end_string} = sat_solver
     val var_count  = if isSome vc then valOf vc else length(all_vars t)
     val tmp        = if isSome fname 
		      then let val _ = initSatVarMap var_count 
			       val _ = termToDimacs t (*FIXME: this is to regenerate sat_var_map: 
						       better to save/load it*)
			  in valOf fname end
		      else termToDimacsFile NONE t var_count
     val infile     = tmp ^ ".cnf"
     val outfile    = tmp ^ "." ^ name
     val ex         = (*Globals.HOLDIR ^*) satdir ^ executable
     val run_cmd    = notime_run ex (infile,outfile)
     val _          = (sat_command := run_cmd)
     val code       = Process.system run_cmd
     val _          = if isSuccess code
                       then ()
		      else if (name="minisat" orelse name="minisatp") 
		      then ()
                      else print("Warning:\n Process.system reports failure signal returned by\n " 
				 ^ run_cmd ^ "\n")
     val ins        = TextIO.openIn outfile
     val sat_res    = TextIO.inputAll ins
     val _          = TextIO.closeIn ins
     val sat_res_ss = Substring.all sat_res
     val result     = substringContains failure_string sat_res_ss
 in
  if result 
   then NONE
   else 
    let val model1 = parseSat(start_string,end_string)sat_res_ss
        val model2 = if only_true 
                      then model1
                           @
                           (map 
                             (fn n => 0-n) 
                             (subtract (map snd (snd(showSatVarMap()))) model1))
                      else model1
    in
     let val model3 = SOME(map intToLiteral model2)
      in model3 end
    end
 end;

(*
** satOracle sat_solver t
** invokes sat_solver on t and returns a theorem tagged by the solver name
** of the form |- (l1 /\ ... ln) ==> t (satisfied with literals l1,...,ln)
** or |- ~t (failure)
*)

(*
val _ = (show_tags := true);
*)

fun satOracle sat_solver t =
 let val SatSolver {name,
                    URL,
                    executable,
                    notime_run,
                    time_run,
                    only_true,
                    failure_string,
                    start_string,
                    end_string} = sat_solver
     val res = invokeSat sat_solver NONE t NONE
 in
  case res of
    SOME l => Thm.mk_oracle_thm (Tag.read name) ([], mk_imp(list_mk_conj l, t))
  | NONE   => Thm.mk_oracle_thm (Tag.read name) ([], mk_neg t)
 end;

(*
** satProve sat_solver t
** invokes sat_solver on t and if a model is found then
** then it is verified using proof in HOL and a theorem
** |- (l1 /\ ... /\ ln) ==> t is returned
** (where l1,...,ln are the literals making up the model);
** Raises satProveError if no model is found.
** Raises satCheckError if the found model is bogus
*)

(*
** satCheck [l1,...,ln] t 
** attempts to prove (l1 /\ ... /\ ln) ==> t 
** if it succeeds then the theorem is returned, else
** exception satCheckError is raised
*)

val EQT_Imp1 = tautLib.TAUT_PROVE ``!b. b ==> (b=T)``
and EQF_Imp1 = tautLib.TAUT_PROVE ``!b. (~b) ==> (b=F)``
and EQT_Imp2 = tautLib.TAUT_PROVE ``!b. (b=T) ==> b``;

exception satCheckError;
fun satCheck model t =
 (let 
        val mtm  = list_mk_conj model
      val th1  = ASSUME mtm
      val thl  = map 
                  (fn th => if is_neg(concl th) 
                             then MP (SPEC (dest_neg(concl th))EQF_Imp1) th
                             else MP (SPEC(concl th)EQT_Imp1) th)
                  (CONJUNCTS th1)
      val subl = map (fn th => lhs(concl th) |-> th) thl
      val th2 = SUBST_CONV subl t t
      val th3 = CONV_RULE(RHS_CONV(Rewrite.REWRITE_CONV[])) th2
      val th4 = MP (SPEC t EQT_Imp2) th3
  in
   DISCH mtm th4
  end)  handle Interrupt => raise Interrupt
                    |  _ => raise satCheckError;

exception satProveError;

(* assumes t is in cnf *)
fun satProve sat_solver t  = 
 case invokeSat sat_solver NONE t NONE of
   SOME model => satCheck model t
 | NONE       => raise satProveError 		

end
end

