signature mlePrologSynt =
sig

  include Abbrev
  
  val is_mvar : term -> bool
  val contain_mvar : term -> bool

 type board = (term * term) list * (int * int) * term
  type move = (term,term) subst
  val game : (board,move) psMCTS.game

end
