signature mleArithData =
sig

  include Abbrev

  val dataarith_dir : string

  val eval_numtm      : term -> int
  val random_numtm    : (int * int) -> term

  val create_train : int -> term list
  val create_valid : term list -> int -> term list
  val create_test  : term list -> int -> term list
  val create_big   : term list -> int -> term list

  val export_arithdata : string -> unit

end
