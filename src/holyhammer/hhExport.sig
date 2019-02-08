signature hhExport =
sig

  include Abbrev
 
  val comment_flag : bool ref

  val th1_export_bushy : string list -> unit
  val th1_export_chainy : string list -> unit

end
