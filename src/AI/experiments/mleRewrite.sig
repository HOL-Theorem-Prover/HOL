signature mleRewrite =
sig

  include Abbrev

  type pos = int list
  type board = (term * pos)
  datatype move = Arg of int | Paramod of (int * bool)

  val mk_startsit : term -> board

  (* interface *)
  val gamespec : (board,move) mlReinforce.gamespec
  val extspec : board mlReinforce.extgamespec

  (* statistics *)
  val maxprooflength_atgen : unit -> int list
  val stats_prooflength : string -> (int * int) list

end
