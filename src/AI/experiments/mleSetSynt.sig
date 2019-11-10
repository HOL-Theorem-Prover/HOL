signature mleSetSynt =
sig

  include Abbrev

  type board = ((term * bool list) * term)
  type move = term

  val export_setsyntdata : unit -> unit
  val mk_graph : int -> term -> bool list
  val mk_startboard : term -> board
  val dest_startboard : board -> term
  val extsearch : board mlReinforce.extsearch
  val rl_obj : board mlReinforce.rl_obj

end
