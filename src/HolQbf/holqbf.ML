open OpenTheoryIO
exception D
local
  open SatSolvers satConfig
  val SatSolver m = minisatp
  val m = SatSolver { executable="/home/rk436/bin/minisat",
name= #name m,
URL= #URL m,
post_exe= #post_exe m,
notime_run= #notime_run m,
time_run= #time_run m,
post_run= #post_run m,
only_true= #only_true m,
failure_string= #failure_string m,
start_string= #start_string m,
end_string= #end_string m}
  val c = set_solver m base_config
  fun p tm = HolSatLib.GEN_SAT (set_term tm c)
in
  val _ = HolQbfLib.set_sat_prove p
end
fun main() = let
  val t = article_to_term TextIO.stdIn
  val _ = Feedback.emit_MESG := false
  val _ = thm_to_article TextIO.stdOut (fn () => HolQbfLib.decide t)
in () end
handle Feedback.HOL_ERR e => (print (Feedback.format_ERR e); raise D)
     | Io {name,function,cause=SysErr(s,_)} => (print ("IO error: name="^name^", function="^function^"SysErr="^s); raise D)
     | Io {name,function,cause} => (print ("IO error: name="^name^", function="^function); raise D)
     | e => (print "other error: "; PolyML.print e; raise D)
val _ = PolyML.export("holqbf",main)
