signature holyHammer =
sig
  
  val hh: Term.term -> Thm.thm
  val hh_atp: string -> Term.term -> Thm.thm

end
