signature holyHammer =
sig

  val hh: Thm.thm list -> Term.term -> unit
  val hh_atp: string -> Thm.thm list -> Term.term -> unit

end
