signature Sref =
sig

  type 'a t
  val new     : 'a -> 'a t
  val update  : 'a t -> ('a -> 'a) -> unit  (* locks *)
  val gen_update : 'a t -> ('a -> 'a * 'b) -> 'b (* locks *)
  val value   : 'a t -> 'a               (* no locks *)

end
