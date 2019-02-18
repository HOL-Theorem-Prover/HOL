signature hhExportTh1 =
sig

include Abbrev

  val th1_write_pb : string -> 
    ((string * string) * (string * string) list) -> unit 
  val th1_export_bushy : string list -> unit
  val th1_export_chainy : string list -> unit  

end
