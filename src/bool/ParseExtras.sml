structure ParseExtras :> ParseExtras =
struct

  open Parse

  val _ = temp_overload_on ("<=>", ``(=) : bool -> bool -> bool``)
  val _ = temp_set_fixity "<=>" (Infix(NONASSOC, 100))

end
