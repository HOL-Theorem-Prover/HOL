(*
** This file contains specifications of the SAT tools that
** can be invoked from HOL.
** Details of format in the comments following each field name.
**
** {name            (* solver name                                         *)
**  URL,            (* source for downloading                              *)
**  executable,     (* path to executable                                  *)
**  post_exe,       (* path to post_processor executable if any            *)
**  notime_run,     (* command to invoke solver on a file                  *)
**  time_run,       (* command to invoke on a file and time                *)
**  post_run,       (* transform SAT solver output before reading into HOL *)
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
   post_exe       : string option,
   notime_run     : string -> string * string -> string ,
   time_run       : string -> (string * string) * int -> string,
   post_run       : string -> (string * string) -> string ,
   only_true      : bool,
   failure_string : string,
   start_string   : string,
   end_string     : string};

fun getSolverName (SatSolver {name,...}) = name
fun getSolverExe (SatSolver {executable,...}) = executable
fun getSolverPostExe (SatSolver {post_exe,...}) = post_exe
fun getSolverRun (SatSolver {notime_run,...}) = notime_run
fun getSolverPostRun (SatSolver {post_run,...}) = post_run
fun getSolverTrue (SatSolver {only_true,...}) = only_true
fun getSolverFail (SatSolver {failure_string,...}) = failure_string
fun getSolverStart (SatSolver {start_string,...}) = start_string
fun getSolverEnd (SatSolver {end_string,...}) = end_string

val p = Systeml.protect
fun spacify [] = ""
  | spacify [h] = h
  | spacify (h::t) = h ^ " " ^ spacify t


val zchaff =
 SatSolver
  {name           = "zchaff",
   URL            = "http://www.princeton.edu/~chaff/zchaff",
   executable     = if isSome (Process.getEnv "OS")
		       andalso String.compare(valOf(Process.getEnv "OS"),"Windows_NT")=EQUAL
		    then Globals.HOLDIR^"/src/HolSat/sat_solvers/zchaff/zchaff.exe"
		    else Globals.HOLDIR^"/src/HolSat/sat_solvers/zchaff/zchaff",
   post_exe       = SOME (if isSome (Process.getEnv "OS")
		       andalso String.compare(valOf(Process.getEnv "OS"),"Windows_NT")=EQUAL
			  then Globals.HOLDIR^"/src/HolSat/sat_solvers/zc2hs/zc2hs.exe"
			  else Globals.HOLDIR^"/src/HolSat/sat_solvers/zc2hs/zc2hs"),
   notime_run     = (fn ex => fn (infile,outfile) =>
                        spacify [p ex, p infile,">", p outfile]),
   time_run       = (fn ex => fn ((infile,outfile),time) =>
                        spacify [p ex, p infile, p (Int.toString time), ">",
                                 p outfile]),
   post_run        = (fn ex => fn (infile,outfile) =>
                        spacify [p ex, p infile, "-m",
                                 p (outfile ^ ".proof"),
                                 "-z",
                                 "resolve_trace", ">", "zc2hs_trace"]),
   only_true      = false,
   failure_string = "UNSAT",
   start_string   = "Instance Satisfiable",
   end_string     = "Random Seed Used"};

val minisatp =
 SatSolver
  {name           = "minisatp",
   URL            = "http://www.cs.chalmers.se/Cs/Research/FormalMethods/MiniSat",
   executable     = if isSome (Process.getEnv "OS")
		       andalso String.compare(valOf(Process.getEnv "OS"),"Windows_NT")=EQUAL
		    then Globals.HOLDIR^"/src/HolSat/sat_solvers/minisat/minisat.exe"
		    else Globals.HOLDIR^"/src/HolSat/sat_solvers/minisat/minisat",
   post_exe       = NONE,
   notime_run     = (fn ex => fn (infile,outfile) =>
                      spacify [p ex, "-r", p outfile, "-p",
                               p (outfile^".proof"), p infile, "-x", ">",
                               p (outfile ^".stats")]),
   time_run       = (fn ex => fn ((infile,outfile),time) =>
                      spacify [p ex, p infile, p (Int.toString time),  ">",
                               p outfile]),
   post_run        = (fn _ => fn _ => ""),
   only_true      = false,
   failure_string = "UNSAT",
   start_string   = "SAT",
   end_string     = " 0"};

end
