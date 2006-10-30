(*
** This file contains specifications of the SAT tools that
** can be invoked from HOL. 
** Details of format in the comments following each field name.
**
** {name            (* solver name                                         *)
**  URL,            (* source for downloading                              *)
**  executable,     (* path to executable                                  *)
**  notime_run,     (* command to invoke solver on a file                  *)
**  time_run,       (* command to invoke on a file and time                *)
**  only_true       (* true if only the true atoms are listed in models    *)
**  failure_string, (* string whose presence indicates unsatisfiability    *)
**  start_string,   (* string signalling start of variable assignment      *)
**  end_string}     (* string signalling end of variable assignment        *)
*)

structure SatSolvers =
struct

datatype sat_solver = 
 SatSolver of
  {name           : string,
   URL            : string,
   executable     : string,    
   notime_run     : string -> string * string -> string,    
   time_run       : string -> (string * string) * int -> string,      
   only_true      : bool,
   failure_string : string,
   start_string   : string,  
   end_string     : string};

fun getSolverName (SatSolver {name,...}) = name
fun getSolverExe (SatSolver {executable,...}) = executable
fun getSolverRun (SatSolver {notime_run,...}) = notime_run
fun getSolverTrue (SatSolver {only_true,...}) = only_true
fun getSolverFail (SatSolver {failure_string,...}) = failure_string
fun getSolverStart (SatSolver {start_string,...}) = start_string
fun getSolverEnd (SatSolver {end_string,...}) = end_string

(*
val grasp =
 SatSolver
  {name           = "grasp",
   URL            = "http://sat.inesc.pt/~jpms/grasp/fgrasp.tar.gz",
   executable     = "sat_solvers/grasp/sat-grasp.st.linux",
   notime_run     = (fn ex => fn (infile,outfile) => 
                     (ex ^ " +V0 +O " ^ infile ^ " > " ^ outfile)),
   time_run       = (fn ex => fn ((infile,outfile),time) => 
                      (ex ^ " +V0 +O +T" ^ (Int.toString time) ^ " " ^ infile ^ " > " ^ outfile)),
   only_true      = false,
   failure_string = "UNSATISFIABLE INSTANCE",
   start_string   = "Variable Assignments Satisfying CNF Formula:",
   end_string     =  "Done searching.... SATISFIABLE INSTANCE"};
*)

val zchaff =
 SatSolver
  {name           = "zchaff", 
   URL            =
    "http://www.ee.princeton.edu/~chaff/zchaff/zchaff.2001.2.17.linux.gz",
   executable     = "sat_solvers/zchaff/zchaff",
   notime_run     = (fn ex => fn (infile,outfile) => 
                      (ex ^ " " ^ infile ^ " > " ^ outfile)),
   time_run       = (fn ex => fn ((infile,outfile),time) => 
                      (ex ^ " " ^ infile ^ " " ^ (Int.toString time) ^ " > " ^ outfile)),
   only_true      = false,
   failure_string = "UNSAT",
   start_string   = "Instance Satisfiable",
   end_string     = "Random Seed Used"};

(*
val sato =
 SatSolver
  {name           = "sato", 
   URL            = "ftp://cs.uiowa.edu/pub/hzhang/sato/sato.tar.gz",
   executable     = "sat_solvers/sato/sato3.2.1/sato",
   notime_run     = (fn ex => fn (infile,outfile) => 
                      (ex ^ " -f " ^ infile ^ " > " ^ outfile)),
   time_run       = (fn ex => fn ((infile,outfile),time) => 
                      (ex ^ " -f -h" ^ (Int.toString time) ^ " " ^ infile ^ " > " ^ outfile)),
   only_true      = true,
   failure_string = "The clause set is unsatisfiable",
   start_string   = "Model #1: (indices of true atoms)",
   end_string     = "The number of found models"};
*)

(*
val minisat =
 SatSolver
  {name           = "minisat", 
   URL            = "http://www.cs.chalmers.se/Cs/Research/FormalMethods/MiniSat/cgi/MiniSat_v1.13_linux.cgi",
   executable     = "sat_solvers/minisat/minisat",
   notime_run     = (fn ex => fn (infile,outfile) => 
                      (ex ^ " " ^ infile ^ " > " ^ outfile)),
   time_run       = (fn ex => fn ((infile,outfile),time) => 
                      (ex ^ " " ^ infile ^ " " ^ (Int.toString time) ^ " > " ^ outfile)),
   only_true      = false,
   failure_string = "UNSAT",
   start_string   = "v",
   end_string     = " 0"};
*)

val minisatp =
 SatSolver
  {name           = "minisatp", 
   URL            = "http://www.cs.chalmers.se/Cs/Research/FormalMethods/MiniSat/cgi/MiniSat_v1.14_linux.cgi",
   executable     = if isSome (Process.getEnv "OS") 
		       andalso String.compare(valOf(Process.getEnv "OS"),"Windows_NT")=EQUAL 
		    then "sat_solvers/minisat/minisat.exe"
		    else "sat_solvers/minisat/minisat",
   notime_run     = (fn ex => fn (infile,outfile) => 
                      (ex ^ " -r " ^ outfile ^ " -p " ^ outfile ^ ".proof " ^ infile ^ " -z > " ^ outfile ^".stats")),
   time_run       = (fn ex => fn ((infile,outfile),time) => 
                      (ex ^ " " ^ infile ^ " " ^ (Int.toString time) ^ " > " ^ outfile)),
   only_true      = false,
   failure_string = "UNSAT",
   start_string   = "SAT",
   end_string     = " 0"};

end
