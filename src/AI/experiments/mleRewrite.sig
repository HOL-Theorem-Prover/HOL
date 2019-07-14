signature mleRewrite =
sig

  include Abbrev

  type pos = int list
  type pb = (term * pos)
  datatype board = Board of pb | FailBoard
  datatype move = Arg of int | Paramod of (int * bool)

  val mk_startsit : term -> board psMCTS.sit
  
  (* interface *)
  val gamespec : (board,move) mlReinforce.gamespec
  val extspec : board mlReinforce.extgamespec

  (* statistics *)
  val maxprooflength_atgen : unit -> int list
  val stats_prooflength : string -> (int * int) list

  (* exploration *)
  val explore_gamespec : term -> (board, move) psMCTS.node list

end
