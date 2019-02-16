signature hhExportTf0 =
sig

include Abbrev

  val tf0_term_poly : TextIO.outstream -> term -> unit
  val tf0_term_mono : TextIO.outstream -> term -> unit
  val tf0_formula : TextIO.outstream -> term -> unit  

  val ij_axiom : TextIO.outstream -> hol_type -> unit
  val ji_axiom : TextIO.outstream -> hol_type -> unit

  val tf0_monoeq : TextIO.outstream -> (term * int) -> unit
  val tf0_write_pb : string -> 
    ((string * string) * (string * string) list) -> unit

end
