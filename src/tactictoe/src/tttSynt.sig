signature tttSynt =
sig

  include Abbrev
  
  val number_partition : int -> int -> int list list

  val random_term : 
    (hol_type, term list) Redblackmap.dict -> (int * hol_type) -> term
  
  val n_random_formula : 
    int -> term list -> int -> term list
 
  val uniform_provable : 
    tactic -> int -> term list -> int -> term list  

  val uniform_term : 
    int -> term list -> (int * hol_type) -> term list  

end
