signature mleSynthesize =
sig

  include Abbrev

  type board = term * term * int
  type move = term

  val witness_cache : (term, term) Redblackmap.dict ref

  val create_levels : int -> board list
  val extsearch : board mlReinforce.es
  val rlobj : (board,move) mlReinforce.rlobj

end
