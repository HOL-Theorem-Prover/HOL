signature mleCompute =
sig

  include Abbrev

  val create_trainset :  
    term list -> int * int -> int * int -> (term * real list) list 
  val create_all_testset : 
    term list -> int * int -> int -> int -> ((int * int) * (term * real list) list) list

end
