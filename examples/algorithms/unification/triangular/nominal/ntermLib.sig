signature ntermLib =
sig

  include Abbrev
  val add_rwts : thm list -> unit
  val add_congs : thm list -> unit
  val add_weakenings : thm list -> unit
  val permify : simpLib.simpset -> simpLib.simpset
  val psrw_ss : unit -> simpLib.simpset
  val export_permrwt : string -> unit
  val export_permcong : string -> unit
  val export_permweakening : string -> unit

end