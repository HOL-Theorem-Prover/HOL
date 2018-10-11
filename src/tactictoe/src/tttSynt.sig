signature tttSynt =
sig

  include Abbrev
  
  val partition : int -> int -> int list list

  val random_term : 
    (hol_type, term list) Redblackmap.dict -> (int * hol_type) -> term

end
