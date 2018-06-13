signature exportLib =
sig

  val export_func : Thm.thm -> string
  val export_graph : string -> Term.term -> unit
  val prepare_for_export_conv : Conv.conv
  val print_export_report : unit -> unit

end
