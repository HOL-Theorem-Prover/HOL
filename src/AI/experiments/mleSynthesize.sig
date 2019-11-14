signature mleSynthesize =
sig

  include Abbrev

  type board = ((term * int) * term)
  type move = (term * int)

  val mk_startboard : term -> board
  val dest_startboard : board -> term

  val extsearch : board mlReinforce.extsearch
  val rlobj : board mlReinforce.rlobj

  val create_levels : unit -> unit
  val max_sizeeval_atgen : unit -> int list
  val stats_sizeeval : string -> (int * int) list


end
