signature mleDiophSynt =
sig

  include Abbrev

  val eval_f: term -> int list -> int

  val random_polynomial: unit -> term

  val gen_diophset : int ->
    (int list, term) Redblackmap.dict ->
    (int list, term) Redblackmap.dict 
  

  

end
