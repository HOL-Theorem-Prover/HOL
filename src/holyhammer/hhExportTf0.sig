signature hhExportTf0 =
sig

include Abbrev

  type thmid = string * string

  val tf0_term_poly : TextIO.outstream -> term -> unit
  val tf0_term_mono : TextIO.outstream -> term -> unit
  val tf0_formula : TextIO.outstream -> term -> unit
  val ij_axiom : TextIO.outstream -> hol_type -> unit
  val ji_axiom : TextIO.outstream -> hol_type -> unit
  val tf0_monoeq : TextIO.outstream -> (term * int) -> unit

  val tf0_write_pb :  string -> (thmid * (string list * thmid list)) -> unit
  val tf0_export_bushy : string -> string list -> unit
  val tf0_export_chainy : string -> string list -> unit

end
