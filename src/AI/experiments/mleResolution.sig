signature mleSetSynt =
sig

  include Abbrev

  type board = 
  (
  (int, bool) Redblackmap.dict) set * 
  (int, bool) Redblackmap.dict) option * 
  int
  )
  type move = Select of int | Delete of int
  val game : (board,move) psMCTS.game

end
