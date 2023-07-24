signature Unsynchronized =
sig

  datatype ref = datatype ref
  val := : 'a ref * 'a -> unit
  val ! : 'a ref -> 'a
  val change: 'a ref -> ('a -> 'a) -> unit
  val change_result: 'a ref -> ('a -> 'b * 'a) -> 'b
  val inc: int ref -> int
  val dec: int ref -> int
  val setmp: 'a ref -> 'a -> ('b -> 'c) -> 'b -> 'c

end
