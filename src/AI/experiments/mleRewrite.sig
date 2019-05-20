signature mleRewrite =
sig

  include Abbrev

  type pos = int list
  type pb = (term * pos)
  datatype board = Board of pb | FailBoard
  datatype move = Arg of int | Paramod of (int * bool)
  
  val mk_startsit : term -> board psMCTS.sit
  val gamespec : (board,move) mlReinforce.gamespec
  
  (* proof length *)
  val lo_trace : int -> term -> ((term * pos) list * int) option
  val lo_prooflength : term -> int
  val lo_prooflength_target : board psMCTS.sit -> int



end
