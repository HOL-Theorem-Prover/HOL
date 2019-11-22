signature mleSetSynt =
sig

  include Abbrev

  type board = ((term * bool list) * term)
  type move = term

  val create_levels : unit -> unit
  val mk_graph : int -> term -> bool list
  val mk_startboard : term -> board
  val dest_startboard : board -> term
  val term_of_graph : int -> bool list -> term
  val term_of_board1 : int -> board -> term
  val term_of_board2 : int -> board -> term
  val term_of_board3 : board -> term
  val term_of_board4 : int -> board -> term
  val dhtnn_param_base : mlTreeNeuralNetwork.dhtnn_param
  val extsearch : board mlReinforce.extsearch
  val rlpreobj :  (board,move) mlReinforce.rlpreobj
  val rlobj : board mlReinforce.rlobj

end
