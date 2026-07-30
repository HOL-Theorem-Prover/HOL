structure RWLock :> RWLock =
struct

  type t = unit
  fun new _ = ()
  fun read_locked () body = body ()
  fun write_locked () body = body ()

end
