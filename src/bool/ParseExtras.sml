structure ParseExtras :> ParseExtras =
struct

  open Parse Unicode

  val _ = temp_overload_on ("<=>", ``(=) : bool -> bool -> bool``)
  val _ = temp_set_fixity "<=>" (Infix(NONASSOC, 100))
  val _ = temp_unicode_version {u = UChar.iff, tmnm = "<=>"}

  val _ = temp_overload_on ("<>", ``\x:'a y:'a. ~(x = y)``)
  val _ = temp_set_fixity "<>" (Infix(NONASSOC, 450))
  val _ = temp_unicode_version {u = UChar.neq, tmnm = "<>"}

  val _ = temp_overload_on ("NOTIN", ``\x:'a y:('a -> bool). ~(x IN y)``)
  val _ = temp_set_fixity "NOTIN" (Infix(NONASSOC, 425))
  val _ = temp_unicode_version {u = UChar.not_elementof, tmnm = "NOTIN"}

  val _ = temp_overload_on ("<=/=>", ``$<> : bool -> bool -> bool``)
  val _ = temp_set_fixity "<=/=>" (Infix(NONASSOC, 100))
  val _ = temp_unicode_version {u = UChar.not_iff, tmnm = "<=/=>"}

  fun tight_equality() = set_fixity "=" (Infix(NONASSOC, 450))

end
