signature IntDP_Munge =
sig

  include Abbrev
  val BASIC_CONV : string -> conv -> conv

  val is_presburger : term -> bool
  val non_presburger_subterms : term -> term list
  val dealwith_nats : term -> term * (thm -> thm)

end;
