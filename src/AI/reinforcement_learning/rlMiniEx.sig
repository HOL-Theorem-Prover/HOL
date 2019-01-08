signature rlMiniEx =
sig

  include Abbrev

  val data_mg1 : unit -> (term * real) list * (term * real) list
  val data_mg2 : unit -> term list
  val data_mg3 : unit -> term list

end
