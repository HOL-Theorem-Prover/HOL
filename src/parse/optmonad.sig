signature optmonad =
sig

type ('a, 'b) optmonad = 'a -> ('a * 'b option)

val fail : ('a, 'b) optmonad
val return : 'b -> ('a, 'b) optmonad
val ok : ('a, unit) optmonad

val >- : ('a, 'b) optmonad * ('b -> ('a, 'c) optmonad) -> ('a, 'c) optmonad
val ++ : ('a, 'b) optmonad * ('a, 'b) optmonad -> ('a, 'b) optmonad
val >> : ('a, 'b) optmonad * ('a, 'c) optmonad -> ('a, 'c) optmonad
val >-> : ('a, 'b) optmonad * ('a, 'c) optmonad -> ('a, 'b) optmonad
val +++ : ('a, 'b) optmonad * ('a, 'b) optmonad -> ('a, 'b) optmonad

val repeat : ('a, 'b) optmonad -> ('a, unit) optmonad
val repeatn : int -> ('a, 'b) optmonad -> ('a, unit) optmonad

val tryall : ('a -> ('b, 'c) optmonad) -> 'a list -> ('b, 'c) optmonad

val optional : ('a, 'b) optmonad -> ('a, 'b option) optmonad
val mmap : ('a -> ('b, 'c) optmonad) -> 'a list -> ('b, 'c list) optmonad

val many : ('b, 'a) optmonad -> ('b, 'a list) optmonad
val many1 : ('b, 'a) optmonad -> ('b, 'a list) optmonad

end
