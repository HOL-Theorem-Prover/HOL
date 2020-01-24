signature mleSynthesize =
sig

  include Abbrev

  type board = term * term * int
  type move = term

  (* target *)
  val cgen_random : int -> (int * int) -> term list 
  val cgen_exhaustive : int -> term list
  val create_targetl : term list -> board list
  val export_targetl : board list -> unit
  val import_targetd : unit -> (board, int * bool list) Redblackmap.dict

  (* reinforcement learning *)
  val extsearch : board mlReinforce.es
  val rlobj : (board,move) mlReinforce.rlobj

end
