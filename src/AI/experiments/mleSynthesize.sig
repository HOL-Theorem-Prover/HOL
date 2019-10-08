signature mleSynthesize =
sig

  include Abbrev

  type board = ((term * int) * term)
  type move = (term * int)

  (* interface *)
  val mk_startsit : term -> board
  val dest_startsit : board -> term
  
  (* create training sets with gradual difficulty *)
  val create_sorteddata : unit -> unit

  (* with different winning conditions *)
  val normal_gamespec : (board,move) mlReinforce.gamespec
  val normal_extspec : board mlReinforce.extgamespec
  val copy_gamespec : (board,move) mlReinforce.gamespec
  val copy_extspec : board mlReinforce.extgamespec
  val eval_gamespec : (board,move) mlReinforce.gamespec
  val eval_extspec : board mlReinforce.extgamespec

  (* statistics *)
  val max_sizeeval_atgen : unit -> int list
  val stats_eval : string -> (int * int) list

  (* test phase *)
  val test_eval_extspec : 
    (mlReinforce.dhtnn, (term * int) * term,
    ((term * int) * term) * bool * int) smlParallel.extspec
  val final_eval : string -> mlTreeNeuralNetwork.dhtnn -> term list -> unit

end
