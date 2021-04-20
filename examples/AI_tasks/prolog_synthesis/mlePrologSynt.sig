signature mlePrologSynt =
sig

  include Abbrev
  
  val is_mvar : term -> bool
  val contain_mvar : term -> bool
  val close_qt : term -> term
  val open_qt : term -> term

  val test_ex : mlePrologLib.prog -> mlePrologLib.table -> psMCTS.status

  type board = mlePrologLib.table * term
  type move = (term,term) subst
  val game : (board,move) psMCTS.game

end
