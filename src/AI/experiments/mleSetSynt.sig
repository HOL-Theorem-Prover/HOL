signature mleSetSynt =
sig

  include Abbrev

  type board = ((term * bool list) * term)
  type move = term

  val export_setsyntdata : unit -> unit
  val mk_graph : int -> term -> bool list
  val mk_startboard : term -> board
  val dest_startboard : board -> term
  val term_of_board1 : board -> term
  val term_of_board2 : board -> term
  val term_of_board3 : board -> term
  val term_of_board4 : board -> term
  val extsearch : board mlReinforce.extsearch
  val rlobj : board mlReinforce.rlobj



end
