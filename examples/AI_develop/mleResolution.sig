signature mleResolution =
sig

  include Abbrev
  
  type lit = int * bool
  type clause = lit list
  val clause_compare : clause * clause -> order
  type pb = clause list
  val string_of_pb : pb -> string

  val resolve_calls : int ref

  val subsume : clause -> clause -> bool
  val brute_pb : ((lit list, int) Redblackmap.dict -> bool) ->
    int -> pb -> string * int * pb option
  val abs_time : pb -> int

  val random_pb : int -> int -> int -> pb
  val random_clause : int -> int -> clause
  val is_sat : pb -> bool
  val inter_reduce : pb -> pb

  type board = pb * pb * int list
  datatype move = Select | Delete
  val game : (board,move) psMCTS.game

  val eval_board : board -> real
  val mcts_test : int -> board -> bool * (board, move) psMCTS.tree

end
