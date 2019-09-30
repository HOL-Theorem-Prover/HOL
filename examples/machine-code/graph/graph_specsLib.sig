signature graph_specsLib =
sig

  val clear_graph_spec_fails : unit -> unit
  val derive_insts_for : string -> Thm.thm list
  val print_graph_spec_report : unit -> unit list
  val try_map : ('a -> 'b) -> ('a -> 'c) -> 'a list -> 'c list

end
