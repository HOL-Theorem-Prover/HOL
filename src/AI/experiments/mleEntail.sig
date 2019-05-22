signature mleEntail =
sig

  include Abbrev

  val read_ex : string -> term * real list
  val prime_tag : term
  val prime_term : int -> term -> term
  val prime_boolvar_sub : int -> (term,term) subst

end
