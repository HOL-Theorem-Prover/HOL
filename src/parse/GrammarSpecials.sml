structure GrammarSpecials :> GrammarSpecials =
struct

  val fnapp_special = "_ fnapp"
  val bracket_special = "_ bracket"
  val recsel_special = " _ record select"
  val recupd_special = " _ record update"
  val recfupd_special = " _ record fupdate"
  val recwith_special = " _ record with"
  val reccons_special = " _ record cons"
  val recnil_special = " _ record nil"
  val vs_cons_special = " _ vs cons"
  val resquan_special = " _ res quan special"
  val nat_elim_term = "nat_elim__magic"
  val fromNum_str = "&"
  val std_binder_precedence = 0

  val case_special = "case__magic"
  val case_split_special = "case_split__magic"
  val case_arrow_special = "case_arrow__magic"


end
