signature stmonad =
sig
type ('a, 'b) stmonad = 'a -> ('a * 'b)

val >> : ('a, 'b) stmonad * ('a, 'c) stmonad -> ('a, 'c) stmonad
val >- : ('a, 'b) stmonad * ('b -> ('a, 'c) stmonad) -> ('a, 'c) stmonad
val ok : ('a, unit) stmonad
val return : 'a -> ('b, 'a) stmonad

val mmap : ('a -> ('b, 'c) stmonad) -> 'a list -> ('b, 'c list) stmonad
end
