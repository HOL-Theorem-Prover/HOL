signature pairML =
sig
   val fst      : 'a * 'b -> 'a
   val snd      : 'a * 'b -> 'b
   val curry    : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
   val uncurry  : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
   val pair_map : ('a -> 'b) * ('c -> 'd) -> 'a * 'c -> 'b * 'd
end
