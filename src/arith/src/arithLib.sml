structure arithLib :> arithLib =
struct

  open Arith basicHol90Lib

  val ARITH_PROVE = EQT_ELIM o ARITH_CONV

end;
