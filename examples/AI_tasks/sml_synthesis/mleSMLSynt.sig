signature mleSMLSynt =
sig

  include Abbrev
  
  val maxstep : int
  type board = int * int list * (int * mleSMLLib.prog list) list
  type move = mleSMLLib.bprog
  val game : (board,move) psMCTS.game

  val compare_ol : int -> int list -> mleSMLLib.prog -> psMCTS.status
  val compute_ol : int -> mleSMLLib.prog -> int list option
  val random_seql : int -> int list list
  val gen_seql : int -> int -> int list list

  val mk_startboard : int list -> board
  val random_progll : int -> (int * mleSMLLib.prog list) list
  val gameio : board mlReinforce.gameio
  val term_of_board : board -> term list
  val import_targetl : string -> board list
  val mk_targetd :board list -> (board, bool list) Redblackmap.dict
  
  val extsearch : board mlReinforce.es
  val rlobj : (board,move) mlReinforce.rlobj

end
