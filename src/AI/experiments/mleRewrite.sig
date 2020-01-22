signature mleRewrite =
sig

  include Abbrev

  type board = term * term * int
  type move = term

  (* tranformation *)
  val lo_norm : int -> term -> term option
  val list_mk_cA : term list -> term
  val strip_cA : term -> term list

  (* example generation *)
  val random_cterm : int -> term
  val random_walk : int -> board -> board option
  val create_levels : int -> board list
  val level_targetl : int -> board list
  
  (* test *)
  val game : (board,move) psMCTS.game
  val mcts_test : int -> board -> bool * (board, move) psMCTS.tree
  val bsobj : (board,move) psBigSteps.bsobj

  (* reinforcement learning *)
  val extsearch : board mlReinforce.es
  val rlobj : (board,move) mlReinforce.rlobj


end
