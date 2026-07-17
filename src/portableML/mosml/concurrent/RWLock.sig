signature RWLock =
sig

  type t
  val new          : string -> t
  val read_locked  : t -> (unit -> 'a) -> 'a
  val write_locked : t -> (unit -> 'a) -> 'a

end
