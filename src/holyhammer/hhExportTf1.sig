signature hhExportTf1 =
sig

include Abbrev

  val tf1_write_pb : string ->
    ((string * string) * (string * string) list) -> unit

  val tf1_bushy_dir : string
  val tf1_chainy_dir : string
  val tf1_export_bushy : string -> string list -> unit
  val tf1_export_chainy : string -> string list -> unit

end
