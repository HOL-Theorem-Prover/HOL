structure OpenTheoryIO :> OpenTheoryIO = struct

open Opentheory Logging

fun term_to_article out t = let
  val _ = raw_start_logging out
  val _ = export_thm (mk_thm([],t))
  val _ = stop_logging()
in () end

fun article_to_thm inp = let
  val thms = raw_read_article inp {
    define_const = fn _ => raise Fail "define_const",
    define_tyop = fn _ => raise Fail "define_tyop",
    axiom = axiom_in_db,
    const_name = const_name_in_map,
    tyop_name = tyop_name_in_map}
in hd (Net.listItems thms) end

end
