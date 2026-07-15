signature ParList =
sig
  val get_some: ('a -> 'b option) -> 'a list -> 'b option
  val get_first: ('a -> 'b option) -> 'a list -> 'b option
end
