signature rlTruth =
sig

  include Abbrev

  val mk_ttset_ground : int * int -> int ->
    (term * real list) list * (term * real list) list
  val mk_true_arith_eq : int * int -> int -> term list

end
