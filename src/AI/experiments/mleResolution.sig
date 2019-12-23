signature mleResolution =
sig

  include Abbrev
  
  type 'a set = ('a, unit) Redblackmap.dict
  type lit = int * bool
  type clause = lit list
  val clause_compare : clause * clause -> order

  type board = (clause list * clause list * int)
  type move = int * bool
  val mk_startboard : clause list -> board
  
  val game : (board,move) psMCTS.game
  val brute_pb : int -> clause list -> string * int * int option
  val difficulty : int -> clause list -> int option

  val random_pb : int -> int -> int -> clause list
  val is_sat : clause list -> bool
  val inter_reduce : clause list -> clause list
  val mcts_test : int -> clause set -> bool * (board, move) psMCTS.tree

  val term_of_board : board -> term
  val level_pb : int -> clause set
  val level_targetl : int -> board list

  val dhtnn_param_base : mlTreeNeuralNetwork.dhtnn_param
  val extsearch : board mlReinforce.extsearch
  val rlpreobj : (board,move,unit) mlReinforce.rlpreobj
  val rlobj : board mlReinforce.rlobj

end
