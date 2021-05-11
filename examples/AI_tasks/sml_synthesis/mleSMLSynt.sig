signature mleSMLSynt =
sig

  include Abbrev
  
  type board = int list * (int * mleSMLLib.prog list) list
  type move = mleSMLLib.bprog
  val game : (board,move) psMCTS.game

  val compare_ol : int list -> mleSMLLib.prog -> psMCTS.status
  val compute_ol : int -> mleSMLLib.prog -> int list option
  val random_seql : int -> int list list
  val gen_seql : int -> int -> int list list

  val gameio : mlReinforce.gameio

end
