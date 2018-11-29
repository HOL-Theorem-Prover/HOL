signature Future =
sig

  type 'a future
  val fork : (unit -> 'a) -> 'a future
  val join : 'a future -> 'a
  val joins : 'a future list -> 'a list
  val value : 'a -> 'a future

end
