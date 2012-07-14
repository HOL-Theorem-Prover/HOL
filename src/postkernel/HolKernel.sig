signature HolKernel =
sig
  (* This signature file is for documentation purposes only *)

  type term = Term.term
  type thm = Thm.thm

  val bvk_find_term:
     (term list * term -> bool) -> (term -> 'a) -> term -> 'a option
  val disch: term * term list -> term list
  val find_term: (term -> bool) -> term -> term
  val find_terms: (term -> bool) -> term -> term list
  val subst_occs:
     int list list -> {redex: term, residue: term} list -> term -> term

end
