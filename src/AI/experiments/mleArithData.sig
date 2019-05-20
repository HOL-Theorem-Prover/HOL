signature mleArithData =
sig

  include Abbrev

  val eval_numtm : term -> int

  val create_train_valid :  
    int -> (term * int) list * (term * int) list
  val create_test : 
     ((term * int) list * (term * int) list) ->
           int -> ((int * int) * term list) list

  val stats_ex : (term * int) list -> (int * int) list

end
