signature mlePrologLib =
sig

  include Abbrev

  
  type prog = (term * term list) list
  type ex = (term * term) list

  val g0 : term
  val prog0 : prog
  val prog1 : prog
  val operl : term list

  val execute : int -> prog -> term -> (term,term) subst

  val qt_to_prog : term -> prog
  val test_unit : prog -> (term * term) -> (bool * bool)
  
  val anil : term
  val operl_nn : int * int -> term list  

  val random_qt : int -> term
  val all_ex : prog -> (int * int) -> ex
  
  

end
