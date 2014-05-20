structure combinLib :> combinLib =
struct

open HolKernel combinTheory computeLib

fun add_combin_compset compset =
  (add_thms
    [K_THM,S_DEF,I_THM,C_DEF,W_DEF,o_THM,K_o_THM,
     APP_DEF,APPLY_UPDATE_THM] compset
  ; set_skip compset combinSyntax.K_tm (SOME 1))

val () = add_combin_compset the_compset

end
