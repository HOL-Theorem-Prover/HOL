signature mleRewrite =
sig

  include Abbrev

  type board = term * term * int
  type move = string * term

  (* vocabulary *)
  val oo : term * term -> term
  val tag : term -> term
  val cA : term
  val cT : term
  val cS : term
  val cK : term
  val cE : term
  val cts : term -> string 
  val level_targetl : int -> board list
  (* helpers *)
  val subst_match : term -> term -> term
  val game : (board,move) psMCTS.game
  val mcts_test : int -> board -> bool * (board, move) psMCTS.tree
  val movel : move list

  val schedule_base : mlNeuralNetwork.schedule
  val dhtnn_param_base : mlTreeNeuralNetwork.dhtnn_param
  val extsearch : board mlReinforce.extsearch
  val rlpreobj : (board,move,unit) mlReinforce.rlpreobj
  val rlobj : board mlReinforce.rlobj

end
