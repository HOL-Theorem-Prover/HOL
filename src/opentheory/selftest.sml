open Opentheory
fun cmd pkg out = ("opentheory info --article -o "^out^" "^pkg)
val pkg = "bool-def-1.0"
val tmp = OS.FileSys.tmpName()
val _ = if OS.Process.isSuccess(Systeml.system_ps (cmd pkg tmp)) then let
val thms = read_article (TextIO.openIn tmp) {
  thms=empty_thms,
  types=typesFromList
  [("bool",fn [] => Type.bool),
   ("->",fn ls => Type.mk_type("fun",ls))],
  consts=constsFromList
  [("=",fn ty => Term.mk_const("=",ty)),
   ("Data.Bool.select",fn ty => Term.mk_const("@",ty))]}
val thms = thmsFromList thms
(* TODO: check that thms is the same set that opentheory
         says the package should have produced *)
in () end else ()
