signature mleRewrite =
sig

  include Abbrev

  type pos = int list
  type board = ((term * pos) * int)
  datatype move = Arg of int | Paramod of (int * bool)

  val mk_startsit : term -> board
  val dest_startsit : board -> term

  (* interface *)
  val gamespec : (board,move) mlReinforce.gamespec
  val extspec : board mlReinforce.extgamespec


  (* statistics *)
  val maxprooflength_atgen : unit -> int list
  val stats_prooflength : string -> (int * int) list

  (* test phase *)
  val test_extspec :
    (mlReinforce.dhtnn, board, board * bool * int) smlParallel.extspec
  val final_eval : string -> mlTreeNeuralNetwork.dhtnn -> term list -> unit

end
