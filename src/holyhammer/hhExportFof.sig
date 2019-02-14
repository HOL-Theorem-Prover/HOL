signature hhExportFof =
sig

include Abbrev

  val fof_export_bushy : string list -> unit
  val fof_export_chainy : string list -> unit
  val fof_export_pb : string -> term * (string * thm) list -> unit

end
