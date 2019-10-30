signature mleSetSynt =
sig

  include Abbrev

  type board = ((term * (bool list * term)) * term)
  type move = term

  (* dataset *)
  val export_setsyntdata : unit -> unit

  (* interface *)
  val mk_startsit : term -> board
  val dest_startsit : board -> term
  val gamespec : (board,move) mlReinforce.gamespec
  val extspec : board mlReinforce.extgamespec
  (* val test_extspec :
    (mlReinforce.dhtnn, (term * int) * term,
    ((term * int) * term) * bool * int) smlParallel.extspec *)

end
