signature mleDiophSynt =
sig

  include Abbrev

  type poly = mleDiophLib.poly
  type board = poly * bool list * int
  datatype move = Add of int | Exp of int

  (* target *)
  val create_targetl : (int list * poly) list -> board list
  val export_targetl : string -> board list -> unit
  val import_targetl : string -> board list
  val mk_targetd : board list -> (board, int * bool list) Redblackmap.dict
  
  (* reinforcement learning *)
  val extsearch : board mlReinforce.es
  val rlobj : (board,move) mlReinforce.rlobj

end
