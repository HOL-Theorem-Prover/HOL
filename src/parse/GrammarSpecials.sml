structure GrammarSpecials :> GrammarSpecials =
struct

  val fnapp_special = "_ fnapp"
  val bracket_special = "_ bracket"
  val recsel_special = " _ record select"
  val recupd_special = " _ record update"
  val recwith_special = " _ record with"
  val reccons_special = " _ record cons"
  val recnil_special = " _ record nil"
  val vs_cons_special = " _ vs cons"
  val resquan_special = " _ res quan special"
  val nat_elim_term = " _ elim_nat"
  val fromNum_str = "fromNum"
  val std_binder_precedence = 0


end
