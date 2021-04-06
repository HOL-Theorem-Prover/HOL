signature mlePrologSynt =
sig

  include Abbrev
  type board = (term * term) list * term
  type move = (term,term) subst
  val game : (board,move) psMCTS.game

end
