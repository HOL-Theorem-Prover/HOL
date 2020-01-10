signature mleRewrite =
sig

  include Abbrev

  type board = term * term * int
  type move = term * int list

  (* combinators *)
  val oo : term * term -> term
  val tag : term -> term
  val cA : term
  val cT : term
  val cS : term
  val cK : term
  val cE : term
  val cts : term -> string
  val cterm_size : term -> int
  val elim_kred : term -> term

  (* example generation *)
  val random_board_fixed : unit -> (board * real) option
  val gen_data : int -> (board * real) list
  val create_data : int -> unit
  val level_targetl : int -> board list
  
  (* test *)
  val subst_cmatch : term -> term -> term
  val game : (board,move) psMCTS.game
  val mcts_test : int -> board -> bool * (board, move) psMCTS.tree
  
  (* reinforcement learning *)
  val extsearch : board mlReinforce.es
  val rlobj : (board,move) mlReinforce.rlobj


end
