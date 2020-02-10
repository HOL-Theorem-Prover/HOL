signature mleCombinSyntHp =
sig

  include Abbrev
  
  type combin = mleCombinLibHp.combin
  type board = (combin * mleCombinLibHp.pose list * bool) * combin * int
  datatype move = AS | AK | NextPos

  (* target *)
  val create_targetl : (combin * combin) list -> (board list * board list)
  val export_targetl : string -> board list -> unit
  val import_targetl : string -> board list
  val mk_targetd : board list -> (board, int * bool list) Redblackmap.dict

  (* reinforcement learning *)
  val extsearch : board mlReinforce.es
  val rlobj : (board,move) mlReinforce.rlobj

end
