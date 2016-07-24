signature seqmonad =
sig

type ('a, 'b) seqmonad = 'a -> ('a * 'b) seq.seq

val fail : ('a, 'b) seqmonad
val return : 'b -> ('a, 'b) seqmonad
val ok : ('a, unit) seqmonad

val >- : ('a, 'b) seqmonad * ('b -> ('a, 'c) seqmonad) -> ('a, 'c) seqmonad
val ++ : ('a, 'b) seqmonad * ('a, 'b) seqmonad -> ('a, 'b) seqmonad
val >> : ('a, 'b) seqmonad * ('a, 'c) seqmonad -> ('a, 'c) seqmonad
val >-> : ('a, 'b) seqmonad * ('a, 'c) seqmonad -> ('a, 'b) seqmonad
val +++ : ('a, 'b) seqmonad * ('a, 'b) seqmonad -> ('a, 'b) seqmonad

val repeat : ('a, 'b) seqmonad -> ('a, unit) seqmonad
val repeatn : int -> ('a, 'b) seqmonad -> ('a, unit) seqmonad

val tryall : ('a -> ('b, 'c) seqmonad) -> 'a list -> ('b, 'c) seqmonad

val optional : ('a, 'b) seqmonad -> ('a, 'b option) seqmonad
val mmap : ('a -> ('b, 'c) seqmonad) -> 'a list -> ('b, 'c list) seqmonad

val lift : ('a -> 'b) -> ('s,'a) seqmonad -> ('s,'b) seqmonad
val lift2 : ('a -> 'b -> 'c) -> ('s,'a) seqmonad -> ('s,'b) seqmonad ->
            ('s,'c) seqmonad

val fromOpt : ('s,'a) optmonad.optmonad -> ('s,'a) seqmonad
val fromErr : ('s,'a,'e) errormonad.t -> ('s,'a) seqmonad

(* boolean is true if this was a singleton sequence *)
val toError : 'error -> ('s,'a) seqmonad -> ('s,'a * bool,'error) errormonad.t

end
