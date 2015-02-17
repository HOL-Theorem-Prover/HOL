signature holyHammer =
sig
  
  val holyhammer: Term.term -> Thm.thm
  val hh_prover : string -> Term.term -> Thm.thm

end
