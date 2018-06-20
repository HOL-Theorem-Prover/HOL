signature errormonad =
sig

datatype ('a,'b) fs = Some of 'a | Error of 'b
type ('a, 'b, 'c) t = 'a -> ('a * 'b,'c) fs

val fail : string -> ('a, 'b, string) t
val error : 'c -> ('a,'b,'c) t
val return : 'b -> ('a, 'b, 'c) t
val ok : ('a, unit, 'c) t

val >- : ('a, 'b, 'c) t * ('b -> ('a, 'd, 'c) t) -> ('a, 'd, 'c) t
val ++ : ('a, 'b, 'c) t * ('a, 'b, 'd) t -> ('a, 'b, 'd) t
val ++? : ('a,'b,'c) t * ('c -> ('a,'b,'d) t) -> ('a,'b,'d) t
val >> : ('a, 'b, 'c) t * ('a, 'd, 'c) t -> ('a, 'd, 'c) t

val repeat : ('a, 'b, 'c) t -> ('a, unit, 'c) t
val repeatn : int -> ('a, 'b, 'c) t -> ('a, unit, 'c) t
val with_flagM : ('a ref * 'a) -> ('s,'b,'c) t -> ('s,'b,'c) t

val mmap : ('a -> ('b, 'c, 'd) t) -> 'a list -> ('b, 'c list, 'd) t
val foldlM : ('e * 'acc -> ('s,'acc,'error)t) -> 'acc -> 'e list ->
             ('s,'acc,'error)t

val lift : ('a -> 'b) -> ('s,'a,'e) t -> ('s,'b,'e) t
val lift2 : ('a -> 'b -> 'c) -> ('s,'a,'e) t -> ('s,'b,'e) t ->
            ('s,'c,'e) t

val fromOpt : ('a,'b)optmonad.optmonad -> 'c -> ('a,'b,'c)t
val toOpt : ('a,'b,'c)t -> ('a,'b)optmonad.optmonad

val addState : 's -> ('s0*'s,'a,'error)t -> ('s0,'s*'a,'error) t

end
