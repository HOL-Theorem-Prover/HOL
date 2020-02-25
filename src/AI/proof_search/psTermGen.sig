signature psTermGen =
sig

  include Abbrev

  val nterm : term list -> int * hol_type -> real
  val random_term : term list -> int * hol_type -> term
  val random_terml : term list -> int * hol_type -> int -> term list
  val gen_term : term list -> int * hol_type -> term list

end
