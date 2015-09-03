structure decompileLib =
struct

open func_decompileLib;

fun decomp base_name fast ignore_names = let
  val ignore = String.tokens (fn c => mem c [#",",#" "]) ignore_names
  val () = read_files base_name ignore
  val _ = (skip_proofs := fast)
  val names = section_names()
  val th = prove_funcs_ok names
  in th end;

end
