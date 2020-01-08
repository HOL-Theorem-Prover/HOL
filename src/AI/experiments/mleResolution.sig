signature mleResolution =
sig

  include Abbrev
  
  type lit = int * bool
  type clause = lit list
  val clause_compare : clause * clause -> order

  type board = clause list * clause option * int
  type move = clause
  val mk_startboard : clause list -> board
  
  val game : (board,move) psMCTS.game
  val brute_pb : int -> clause list -> string * int * int option
  val difficulty : int -> clause list -> int option

  val random_pb : int -> int -> int -> clause list
  val is_sat : clause list -> bool
  val inter_reduce : clause list -> clause list
  val mcts_test : int -> clause list -> bool * (board, move) psMCTS.tree

  val extsearch : board mlReinforce.es
  val rlobj : (board,move) mlReinforce.rlobj

end
