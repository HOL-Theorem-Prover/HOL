signature mleDiophLib =
sig

  include Abbrev

  type poly = int list list
  
  val modulo : int
  val maxexponent : int
  val maxmonomial : int
  val maxvar : int
  val numberl : int list

  val eval_poly : poly -> int list -> int
  val random_poly : unit -> poly

  val dioph_set : poly -> int list
  val dioph_match : poly -> bool list -> bool
  val gen_diophset : int -> (int list, poly) Redblackmap.dict ->
    (int list, poly) Redblackmap.dict 

  val term_of_poly : poly -> term

end
