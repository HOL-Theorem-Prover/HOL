open OpenTheoryIO
exception D
fun main() = let
  val t = article_to_term TextIO.stdIn
  val _ = thm_to_article TextIO.stdOut (fn () => normalForms.SKICo_CONV t)
in () end
handle HOL_ERR e => (print (format_ERR e); raise D)
     | e => (PolyML.print e; raise D)
val _ = PolyML.export("skico",main)
