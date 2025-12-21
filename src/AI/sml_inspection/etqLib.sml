structure etqLib :> etqLib =
struct

open HolKernel Abbrev

val ERR = mk_HOL_ERR "etqLib"

fun etq_tmo timeout s =
  proofManagerLib.et (s, smlExecute.tactic_of_sml timeout s)
  handle HOL_ERR _ => raise ERR "etq" ("Cannot compile tactic: " ^ s)

val etq = etq_tmo 30.0

end
