structure arithLib :> arithLib =
struct

  open Abbrev Arith

  val ARITH_PROVE = Drule.EQT_ELIM o ARITH_CONV

end;
