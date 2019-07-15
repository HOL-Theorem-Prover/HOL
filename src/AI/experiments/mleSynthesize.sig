signature mleSynthesize =
sig

  include Abbrev

  type board = ((term * int) * term)
  type move = (term * int)

  (* interface *)
  val mk_startsit : term -> board
  val gamespec : (board,move) mlReinforce.gamespec
  val extspec : board mlReinforce.extgamespec

  (* statistics *)
  val maxeval_atgen : unit -> int list
  val stats_eval : string -> (int * int) list

end
