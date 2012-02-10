structure OpenTheoryIO :> OpenTheoryIO = struct

open Opentheory Logging HolKernel

val ERR = Feedback.mk_HOL_ERR "OpenTheoryIO"

fun thm_to_article out th = let
  val _ = raw_start_logging out
  val th = th()
  val _ = export_thm th
  val _ = stop_logging()
in () end

fun term_to_article out t = thm_to_article out
  (fn()=>mk_thm([],list_mk_comb(inst[alpha|->bool,beta|->type_of t]``combin$K``,[boolSyntax.F,t])))

val article_to_thm = let
  val ERR = ERR "article_to_thm"
in fn inp => let
  val thms = raw_read_article inp {
    define_tyop = fn _ => raise ERR "define_tyop",
    define_const = fn _ => raise ERR "define_const",
    axiom = axiom_in_db,
    const_name = const_name_in_map,
    tyop_name = tyop_name_in_map}
in hd (Net.listItems thms) end end

val article_to_term = let
  exception E of term
  val ERR = ERR "article_to_term"
in fn inp =>
  ( raw_read_article inp {
    define_tyop = fn _ => raise ERR "define_tyop",
    define_const = fn _ => raise ERR "define_const",
    axiom = fn _ => fn (_,c) => raise (E (rand c)),
    const_name = const_name_in_map,
    tyop_name = tyop_name_in_map } ; raise ERR "no theorem" )
  handle E t => boolSyntax.rhs(concl(NUMERAL_conv t)) handle UNCHANGED => t
end

fun url_conv url tm = let
  val t = OS.FileSys.tmpName()
  val _ = term_to_article (TextIO.openOut t) tm
  val t = Curl.submitFile {url=url,field="article",file=t}
in article_to_thm t end

end
