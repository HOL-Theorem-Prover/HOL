signature mleRewrite =
sig

  include Abbrev

  type board = term * term * int
  type move = term * int list

  (* vocabulary *)
  val oo : term * term -> term
  val tag : term -> term
  val cA : term
  val cT : term
  val cS : term
  val cK : term
  val cE : term
  val cts : term -> string 
  
  (* example generation *)
  val random_board : int -> int -> board
  val level_targetl : int -> board list
  
  (* test *)
  val subst_cmatch : term -> term -> term
  val game : (board,move) psMCTS.game
  val mcts_test : int -> board -> bool * (board, move) psMCTS.tree
  
  (* reinforcement learning *)
  val extsearch : board mlReinforce.es
  val rlobj : (board,move) mlReinforce.rlobj


end
