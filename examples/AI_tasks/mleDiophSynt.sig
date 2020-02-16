signature mleDiophSynt =
sig

  include Abbrev

  type poly = mleDiophLib.poly
  type board = poly * bool list * int
  datatype move = Add of int | Exp of int

  (* target *)
  val create_targetl : (int list * poly) list -> (board list * board list)
  val export_targetl : string -> board list -> unit
  val import_targetl : string -> board list
  val mk_targetd : board list -> (board, int * bool list) Redblackmap.dict
  
  (* reinforcement learning *)
  val extsearch : board mlReinforce.es
  val rlobj : (board,move) mlReinforce.rlobj

  (* final testing *)
  val ft_extsearch_uniform : board mlReinforce.ftes
  val ft_extsearch_distance : board mlReinforce.ftes
  val fttnn_extsearch : board mlReinforce.fttnnes
end
