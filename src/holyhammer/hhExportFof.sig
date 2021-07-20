signature hhExportFof =
sig

include Abbrev

  type thmid = string * string

  val type_flag : bool ref
  val p_flag : bool ref
  val name_flag : bool ref

  val fof_write_pb : string -> (thmid * (string list * thmid list)) -> unit
  val fof_export_bushy : string -> string list -> unit
  val fof_export_chainy : string -> string list -> unit

  (* holyhammer interface *)
  val fof_export_pb : string -> term * (string * thm) list -> unit
  val fof_export_pbfile : string -> term * (string * thm) list -> unit

  (* export a goal without any translation *)
  val fof_export_goal : string -> goal -> unit

  (* tactictoe interface *)
  val ttt_fof_extra : string -> unit
  val ttt_fof_goal : string -> string -> (string * goal) -> unit

end
