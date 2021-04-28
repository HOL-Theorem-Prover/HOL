signature mleSMLSynt =
sig

  include Abbrev
  
  type board = (int list * int) list * int list list
  type move = mleSMLLib.instr
  val game : (board,move) psMCTS.game

end
