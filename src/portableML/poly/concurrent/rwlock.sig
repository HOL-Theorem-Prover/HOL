signature rwlock =
sig

type 'a t

val new : 'a -> 'a t

val read : 'a t -> ('a -> 'b) -> 'b
val write : 'a t -> ('a -> unit) -> unit

end
