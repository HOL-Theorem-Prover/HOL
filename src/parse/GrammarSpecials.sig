signature GrammarSpecials =
sig

  val fnapp_special : string
  val bracket_special : string
  val vs_cons_special : string
  val resquan_special : string
  val recsel_special : string
  val recupd_special : string
  val recfupd_special : string
  val reccons_special : string
  val recnil_special : string
  val recwith_special : string

  val std_binder_precedence : int

  val nat_elim_term : string
  val fromNum_str : string

end