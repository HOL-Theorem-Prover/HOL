signature mleSetSynt =
sig

  include Abbrev

  type board = ((term * (bool list * term)) * term)
  type move = term

  (* dataset *)
  val export_setsyntdata : unit -> unit
  (* parameters *)
  val mk_graph : int -> term -> bool list
  val graph_size : int ref 
  val ntarget_level : int ref
 (* interface *)
  val mk_startsit : term -> board
  val dest_startsit : board -> term
  val gamespec : (board,move) mlReinforce.gamespec
  val extspec : board mlReinforce.extgamespec
  (* val test_extspec :
    (mlReinforce.dhtnn, (term * int) * term,
    ((term * int) * term) * bool * int) smlParallel.extspec *)
  (* breadth first search *)
  val search_uniform : int -> term -> int option

end
