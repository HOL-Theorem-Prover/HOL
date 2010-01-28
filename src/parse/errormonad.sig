signature errormonad =
sig

datatype ('a,'b) fs = Some of 'a | Error of 'b
type ('a, 'b, 'c) t = 'a -> ('a * ('b,'c) fs)

val fail : string -> ('a, 'b, string) t
val error : 'c -> ('a,'b,'c) t
val return : 'b -> ('a, 'b, 'c) t
val ok : ('a, unit, 'c) t

val >- : ('a, 'b, 'c) t * ('b -> ('a, 'd, 'c) t) -> ('a, 'd, 'c) t
val ++ : ('a, 'b, 'c) t * ('a, 'b, 'c) t -> ('a, 'b, 'c) t
val >> : ('a, 'b, 'c) t * ('a, 'd, 'c) t -> ('a, 'd, 'c) t

val repeat : ('a, 'b, 'c) t -> ('a, unit, 'c) t
val repeatn : int -> ('a, 'b, 'c) t -> ('a, unit, 'c) t

val mmap : ('a -> ('b, 'c, 'd) t) -> 'a list -> ('b, 'c list, 'd) t


end
