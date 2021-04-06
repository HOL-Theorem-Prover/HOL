signature mlePrologLib =
sig

  include Abbrev

  
  type prog = (term * term list) list
  type ex = (term * term) list

  val g0 : term
  val prog0 : prog
  val operl : term list

  val execute : int -> prog -> term -> (term,term) subst
  val test_board : (ex * term) -> bool
  
  val all_ex : prog -> (int * int) -> ex
  val random_search : ex -> term list -> int -> term
  
  

end
