signature combinML =
sig
  val S : ('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c
  val K : 'a -> 'b -> 'a
  val I : 'a -> 'a
  val C : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  val W : ('a -> 'a -> 'b) -> 'a -> 'b
  val o : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
end
