signature tttXO =
sig

  include tttMCTS

  val tic_build_evalpoli : int list -> int pos -> real * choice list
  val tic_endcheck       : int pos -> endcheck
  val tic_apply_move     : string -> int pos -> int pos
  val tic_startpos       : int pos
  val heatmap_of_node    : int node -> string

end
