(* ========================================================================= *)
(* A QUEUE DATATYPE FOR ML                                                   *)
(* Created by Joe Hurd, October 2001                                         *)
(* ========================================================================= *)

signature mlibQueue =
sig

type 'a queue

val empty     : 'a queue
val add       : 'a -> 'a queue -> 'a queue
val is_empty  : 'a queue -> bool
val hd        : 'a queue -> 'a               (* raises Empty *)
val tl        : 'a queue -> 'a queue         (* raises Empty *)
val length    : 'a queue -> int
val from_list : 'a list -> 'a queue
val to_list   : 'a queue -> 'a list
val pp_queue  : 'a mlibUseful.pp -> 'a queue mlibUseful.pp

end