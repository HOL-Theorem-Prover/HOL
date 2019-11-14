signature mleRewrite =
sig

  include Abbrev

  type pos = int list
  type board = ((term * pos) * int)
  datatype move = Arg of int | Paramod of (int * bool)

  val mk_startboard : term -> board
  val dest_startboard : board -> term

  val extsearch : board mlReinforce.extsearch
  val rlobj : board mlReinforce.rlobj

  val create_levels : unit -> unit
  val max_prooflength_atgen : unit -> int list
  val stats_prooflength : string -> (int * int) list

end
