signature mleResolution =
sig

  include Abbrev
  
  type 'a set = ('a, unit) Redblackmap.dict
  type clause = (int, bool) Redblackmap.dict
  val clause_compare : clause * clause -> order

  type board = clause set * int option * int
  datatype move = Select of int | Delete of int
  val game : (board,move) psMCTS.game
  val brute_pb : int -> clause set -> string * int
  val difficulty : int -> clause set -> int option

  val random_pb : int -> int -> clause set
  val satisfiable_pb : clause set -> bool
  val random_solvable : int -> int -> (clause set * int)
  val mcts_test : int -> clause set -> bool * (board, move) psMCTS.tree

  val term_of_board : board -> term
  val collect_solvable :  int -> (int, clause set list) Redblackmap.dict
  val level_targetl : int -> board list

  val dhtnn_param_base : mlTreeNeuralNetwork.dhtnn_param
  val extsearch : board mlReinforce.extsearch
  val rlpreobj : (board,move,unit) mlReinforce.rlpreobj
  val rlobj : board mlReinforce.rlobj

end
