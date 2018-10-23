signature tttSynt =
sig

  include Abbrev
  
  (* randorm terms: top-down *)
  val random_term : 
    (hol_type, term list) Redblackmap.dict -> (int * hol_type) -> term
  
  val n_random_formula : 
    int -> term list -> int -> term list
 
  val uniform_provable : 
    tactic -> int -> term list -> int -> term list  

  val uniform_term : 
    int -> term list -> (int * hol_type) -> term list  
  
  (* selected terms: bottom-up *)
  val evalf_to_filterf : 
    real -> (term -> real) -> term list -> term list

  val synthetize : 
    (term list -> term list) -> (int * int) -> term list -> term list


end
