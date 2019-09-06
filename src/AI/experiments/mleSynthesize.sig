signature mleSynthesize =
sig

  include Abbrev

  type board = ((term * int) * term)
  type move = (term * int)

  (* interface *)
  val mk_startsit : term -> board
  
  (* with different winning conditions *)
  val normal_gamespec : (board,move) mlReinforce.gamespec
  val normal_extspec : board mlReinforce.extgamespec
  val copy_gamespec : (board,move) mlReinforce.gamespec
  val copy_extspec : board mlReinforce.extgamespec
  val eval_gamespec : (board,move) mlReinforce.gamespec
  val eval_extspec : board mlReinforce.extgamespec

  (* statistics *)
  val maxeval_atgen : unit -> int list
  val stats_eval : string -> (int * int) list

end
