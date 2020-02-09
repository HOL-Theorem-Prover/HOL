signature mleCombinSyntHp =
sig

  include Abbrev

  type board = (mleCombinLibHp.combin * mleCombinLibHp.pose list) *
    mleCombinLibHp.combin * int
  datatype move = AS | AK | NextPos

  (* target *)
  val import_targetl : string -> board list
  val mk_targetd : board list -> (board, int * bool list) Redblackmap.dict

  (* reinforcement learning *)
  val extsearch : board mlReinforce.es
  val rlobj : (board,move) mlReinforce.rlobj

end
