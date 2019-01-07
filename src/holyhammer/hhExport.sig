signature hhExport =
sig

  include Abbrev

  (* fof *)
  val fof_export_thy : string -> unit

  (* sexpr *)
  val sexpr_write_thy_ancestry : string -> unit
  val write_thy_ancestry_order : string -> unit

end
