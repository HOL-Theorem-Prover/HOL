structure Cooper :> Cooper =
struct

open HolKernel boolLib CooperShell IntDP_Munge



val COOPER_CONV = BASIC_CONV "COOPER_CONV" decide_pure_presburger_term

val COOPER_PROVE = EQT_ELIM o COOPER_CONV
val COOPER_TAC = conv_tac COOPER_CONV;

val pure_goal = CooperShell.pure_goal

end;
