signature rlTruth =
sig

  include Abbrev

  val mk_ttset_ground : int * int -> int -> 
    (term * real list) list * (term * real list) list


end
