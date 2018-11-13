signature psTermGen =
sig

  include Abbrev

  (* randorm terms of a fixed size: top-down *)
  val random_term :
    (hol_type, term list) Redblackmap.dict -> int * hol_type -> term

  val n_random_term : int -> term list -> int * hol_type -> term list
  val uniform_term : int -> term list -> int * hol_type -> term list

  (* randorm terms up to a fixed size: bottom-up *)
  val synthetize :
    (term list -> term list) -> (int * int) -> (hol_type * term list) ->
    term list


end
