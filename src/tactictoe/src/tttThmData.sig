signature tttThmData =
sig

include Abbrev

  type lbl_t = (string * real * goal * goal list)

  val import_thmfea : string list -> unit
  val update_thmfea : string -> unit
  val export_thmfea : string -> unit

end
