signature hhExportFof =
sig

include Abbrev

  type thmid = string * string
  val fof_write_pb : string -> (thmid * (string list * thmid list)) -> unit
  val fof_export_bushy : string -> string list -> unit
  val fof_export_chainy : string -> string list -> unit

  (* holyhammer interface *)
  val fof_export_pb : string -> term * (string * thm) list -> unit

end
