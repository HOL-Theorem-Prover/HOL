signature hhExportTf0 =
sig

include Abbrev

  val tf0_export_bushy : string list -> unit
  val tf0_export_chainy : string list -> unit
  val ij_axiom : TextIO.outstream -> hol_type -> unit
  val ji_axiom : TextIO.outstream -> hol_type -> unit

end
