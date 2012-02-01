open OpenTheoryIO
exception D
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
