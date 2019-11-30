signature mleSetSynt =
sig

  include Abbrev

  type board = ((term * bool list) * term)
  type move = term

  val create_levels : unit -> unit
  val init_leveld : unit -> board mlReinforce.leveld
  val mk_graph : int -> term -> bool list
  val mk_startboard : term -> board
  val dest_startboard : board -> term
  val term_of_graph : int -> bool list -> term
  val term_of_board1 : int -> board -> term
  val term_of_board1c : term -> board -> term
  val dhtnn_param_base : mlTreeNeuralNetwork.dhtnn_param
  val extsearch : board mlReinforce.extsearch
  val rlpreobj : (board,move,term) mlReinforce.rlpreobj
  val rlobj : board mlReinforce.rlobj

end
