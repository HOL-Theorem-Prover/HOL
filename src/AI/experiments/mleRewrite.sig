signature mleRewrite =
sig

  include Abbrev

  type pos = int list
  type board = ((term * pos) * int)
  datatype move = Arg of int | Paramod of (int * bool)

  val mk_startsit : term -> board
  val dest_startsit : board -> term

  (* statistics *)
  val maxprooflength_atgen : unit -> int list
  val stats_prooflength : string -> (int * int) list

  (* *)
  

end
