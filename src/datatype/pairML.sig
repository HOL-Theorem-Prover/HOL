signature pairML = 
sig
   val fst     : 'a * 'b -> 'a
   val snd     : 'a * 'b -> 'b
   val curry   : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
   val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
   val pairmap : ('a -> 'b) * ('c -> 'd) -> 'a * 'c -> 'b * 'd
end
