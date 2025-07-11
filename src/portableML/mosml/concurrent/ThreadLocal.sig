signature ThreadLocal =
sig

  type 'a t
  val new : unit -> 'a t
  val get : 'a t -> 'a option
  val set : 'a t * 'a -> unit

end
