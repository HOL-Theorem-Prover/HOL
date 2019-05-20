signature mleEntail =
sig

  include Abbrev

  val operl_gen : int -> term list
  val operl_nn : int -> (term * int) list
  val eval_tm : term -> bool list -> bool
  val is_tautology : term -> bool
  val gen_tml : term list -> int -> int -> term list
  val gen_ex :  term list -> int -> (term * real list) list

end
