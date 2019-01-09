structure decompileLib :> decompileLib =
struct

open backgroundLib file_readerLib func_decompileLib;

(*

val base_name = "loop/example"
val fast = false
val ignore_names = ""

*)

fun decomp base_name fast ignore_names = let
  val ignore = String.tokens (fn c => Lib.mem c [#",",#" "]) ignore_names
  val () = read_files base_name ignore
  val _ = (skip_proofs := fast)
  val names = section_names()
  val th = prove_funcs_ok names
  in th end;

end
