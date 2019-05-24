signature mleSynthesize =
sig

  include Abbrev

  type board = ((term * int) * term)
  type move = (term * int)

  val mk_startsit : term -> board psMCTS.sit
  val gamespec : (board,move) mlReinforce.gamespec

  (* statistics *)
  val maxeval_atgen : unit -> int list
  val stats_eval : string -> (int * int) list

  (* search *)
  val explore_gamespec : term -> unit
  val reinforce_fixed : string -> int ->
    (term * real list * real list) list * mlTreeNeuralNetwork.dhtnn

end
