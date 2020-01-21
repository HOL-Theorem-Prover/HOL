signature mleRewrite =
sig

  include Abbrev

  type board = term * term * int
  type move = term

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
  val s_thm : term
  val k_thm : term
  val left_thm : term
  val right_thm : term
  
  (* neural networks addition *)
  val tag_subtm : (term * int list) -> term
  val tag_subtml : (term * int list list) -> term
  val mk_cE : term * term -> term

  (* test *)
  val is_rewritable : term -> bool
  val is_nf : term -> bool
  val is_normalizable : term -> bool

  (* tranformation *)
  val lo_norm : int -> term -> term option
  val strip_cA : term -> term list

  (* example generation *)
  val random_cterm : int -> term
  val random_walk : int -> board -> board option
  val random_board_try : int -> int -> int -> board option
  val create_data : int -> board list
  val level_targetl : int -> board list
  
  (* test *)
  val subst_cmatch : term -> term -> term
  val game : (board,move) psMCTS.game
  val mcts_test : int -> board -> bool * (board, move) psMCTS.tree
  val bsobj : (board,move) psBigSteps.bsobj

  (* reinforcement learning *)
  val extsearch : board mlReinforce.es
  val rlobj : (board,move) mlReinforce.rlobj


end
