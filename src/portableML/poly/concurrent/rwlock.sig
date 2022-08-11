signature rwlock =
sig

type 'a t

val new : 'a -> 'a t

(* completely up to the user to know which is appropriate *)
val read : 'a t -> ('a -> 'b) -> 'b
val write : 'a t -> ('a -> 'b) -> 'b

end
