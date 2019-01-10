signature Uref =
sig

  datatype t = datatype ref
  val uref : 'a -> 'a t
  val := : 'a t * 'a -> unit
  val ! : 'a t -> 'a

end
