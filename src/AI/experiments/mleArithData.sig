signature mleArithData =
sig

  include Abbrev

  val eval_numtm : term -> int

  val create_train_valid :  
    int -> term list * term list
  val create_test : term list -> int -> term list
  val create_big : term list -> int -> term list

end
