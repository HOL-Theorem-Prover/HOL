signature hhExportTh1 =
sig

include Abbrev

  val th1_write_pb : string ->
    ((string * string) * (string * string) list) -> unit

  val th1_bushy_dir : string
  val th1_chainy_dir : string
  val th1_export_bushy : string -> string list -> unit
  val th1_export_chainy : string -> string list -> unit

end
