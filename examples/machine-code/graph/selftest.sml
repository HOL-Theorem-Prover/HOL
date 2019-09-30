open HolKernel Parse boolLib bossLib;
open decompileLib tttFeature testutils

val hash_thm = tttFeature.hash_term o Thm.concl
val hash_dfn = hash_thm o DB.definition

val thm = decompileLib.decomp "loop/example" false ""

val _ =
  hash_thm thm = 373949126571192 andalso
  hash_dfn "main_funcs" = 729825789649344 andalso
  hash_dfn "f_funcs" = 95180147214897 andalso
  hash_dfn "g_funcs" = 774608748961224 andalso
  (OK(); true) orelse
  die "Decompilation of loop/example produced unexpected result"

(* Currently failing
val thm = decompileLib.decomp "loop-m0/example" false ""
*)

val _ = OS.Process.exit OS.Process.success
