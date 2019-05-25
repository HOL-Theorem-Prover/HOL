signature mleArithData =
sig

  include Abbrev

  val eval_numtm      : term -> int
  val random_numtm    : (int * int) -> term
  val compressed_size : term -> int

  val create_train : int -> term list
  val create_valid : term list -> int -> term list
  val create_test  : term list -> int -> term list
  val create_big   : term list -> int -> term list

  val dataarith_dir    : string
  val compressed_stats : string -> (int * int) list

end
