open Opentheory Logging
exception D
fun main() = let
  exception E of term
  val t = ( raw_read_article TextIO.stdIn {
    define_tyop = fn _ => (print "define_tyop"; raise D),
    define_const = fn _ => (print "define_const"; raise D),
    axiom = fn _ => fn (_,c) => raise (E c),
    const_name = const_name_in_map,
    tyop_name = tyop_name_in_map } ; (print "no theorem"; raise D) )
  handle E t => t
  val _ = Feedback.emit_MESG := false
  val _ = raw_start_logging TextIO.stdOut
  val th = HolQbfLib.decide t
  val _ = export_thm th
  val _ = stop_logging()
in () end
handle HOL_ERR e => (print (format_ERR e); raise D)
     | Io {name,function,cause=SysErr(s,_)} => (print ("IO error: name="^name^", function="^function^"SysErr="^s); raise D)
     | Io {name,function,cause} => (print ("IO error: name="^name^", function="^function); raise D)
     | e => (print "other error: "; PolyML.print e; raise D)
val _ = PolyML.export("holqbf",main)
