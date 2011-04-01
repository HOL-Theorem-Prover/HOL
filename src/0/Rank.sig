signature Rank =
sig
  type rank = KernelTypes.rank

  val rho           : rank

  val check         : string -> string -> int -> rank

  val rank_compare  : rank * rank -> order
  val ge_rk         : rank * rank -> bool
  val max           : rank * rank -> rank
  val suc           : rank -> rank
  val promote       : rank -> rank -> rank
  val rank_to_string: rank -> string
  val rank_size     : rank -> int

  val raw_match_rank: bool -> rank -> rank -> rank -> rank
  val match_rank    : rank -> rank -> rank
end
