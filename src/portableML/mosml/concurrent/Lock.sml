structure Lock :> Lock =
struct

  type t = unit
  fun new _ = ()
  fun synchronized () body = body ()

end
