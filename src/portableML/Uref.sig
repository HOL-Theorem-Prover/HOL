signature Uref =
sig

  datatype t = datatype ref
  val new : 'a -> 'a t
  val := : 'a t * 'a -> unit
  val ! : 'a t -> 'a

end
