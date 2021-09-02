signature mleCombinSynt =
sig

  include Abbrev

  type combin = mleCombinLib.combin
  type board = combin * combin * int
  datatype move = S0 | S1 | S2 | K0 | K1

  (* optimization for unfinished terms *)
  val ignore_metavar : combin -> combin

  (* target *)
  val create_targetl : (combin * combin) list -> (board list * board list)
  val export_targetl : string -> board list -> unit
  val import_targetl : string -> board list
  val mk_targetd : board list -> (board, int * bool list) Redblackmap.dict

  (* reinforcement learning *)
  val extsearch : board mlReinforce.es
  val rlobj : (board,move) mlReinforce.rlobj

end
