signature rlMiniConj =
sig

  include Abbrev

  val wrap_rl_loop :
    int -> int -> term list -> (term * real) list * (term * real list) list

  val wrap_rlknn_loop :
    int -> int -> term list -> (term * real) list * (term * real list) list

end
