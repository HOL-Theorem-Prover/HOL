signature rlTruth =
sig

  include Abbrev

  val mk_ttset_ground : int * int -> int ->
    (term * real list) list * (term * real list) list
  val mk_addsuceq : int -> term list
  val list_cost : term -> (term * int) list
  val total_cost : term -> int

end
