signature hhExport =
sig

  include Abbrev

  val fof_export_thy : string -> unit
  val th1_export : string list -> unit
  val th1_export_decl : string list -> unit
  val th1_export_ax : string list -> unit
  val th1_export_bushy : string list -> unit
  val th1_export_chainy : string list -> unit
  val sexpr_export : string list -> unit

end
