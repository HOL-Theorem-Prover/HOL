structure arithLib :> arithLib =
struct

  open Arith
  type term = Term.term
  type thm  = Thm.thm
  type conv = Abbrev.conv

  val ARITH_PROVE = Drule.EQT_ELIM o ARITH_CONV

end;
