signature psTermGen =
sig

  include Abbrev

  val nterm : term list -> int * hol_type -> int
  val nterm_oper : term list -> int * hol_type -> term -> int
  val random_term : term list -> int * hol_type -> term
  val random_term_oper : term list -> int * hol_type -> term -> term

  val gen_term_size : int -> (hol_type * term list) -> term list

end
