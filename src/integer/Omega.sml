structure Omega :> Omega =
struct

  open HolKernel boolLib OmegaShell IntDP_Munge

  val OMEGA_CONV = BASIC_CONV "OMEGA_CONV" decide_closed_presburger

  val OMEGA_PROVE = EQT_ELIM o OMEGA_CONV
  val OMEGA_TAC = CONV_TAC OMEGA_CONV

end;