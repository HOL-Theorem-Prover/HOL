signature tttNN =
sig

type layer =
  {a  : real -> real, 
   da : real -> real,
   w  : real vector vector} 

val train_epoch : 
  real ->
  layer list ->
  (real vector * real vector) list list -> 
  layer list

val train_nepoch : 
  int -> real -> layer list -> int -> 
  (real vector * real vector) list -> layer list

val random_nn : int -> int * int -> layer list

val mk_batch : int -> 'a list -> 'a list list



end
