signature hhExportTf1 =
sig

include Abbrev

  val combin_cval : (term * int) list
  val app_p_cval : (term * int) list
  val tf1_export_bushy : string list -> unit
  val tf1_export_chainy : string list -> unit

end
