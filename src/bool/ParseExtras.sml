structure ParseExtras :> ParseExtras =
struct

  open Parse
  open Unicode
  open TexTokenMap

  (* iff *)
  val _ = temp_overload_on ("<=>", ``(=) : bool -> bool -> bool``)
  val _ = temp_set_fixity "<=>" (Infix(NONASSOC, 100))
  val _ = temp_unicode_version {u = UChar.iff, tmnm = "<=>"}
  val _ = temp_TeX_notation {hol = "<=>", TeX = ("\\HOLTokenEquiv",2)}
  val _ = temp_TeX_notation {hol = UChar.iff, TeX = ("\\HOLTokenEquiv",2)}

  (* not equal *)
  val _ = temp_overload_on ("<>", ``\x:'a y:'a. ~(x = y)``)
  val _ = temp_set_fixity "<>" (Infix(NONASSOC, 450))
  val _ = temp_TeX_notation {hol="<>", TeX = ("\\HOLTokenNotEqual",1)}

  val _ = temp_uset_fixity UChar.neq (Infix(NONASSOC, 450))
  val _ = temp_uoverload_on (UChar.neq, ``\x:'a y:'a. ~(x = y)``)
  val _ = temp_TeX_notation {hol=UChar.neq, TeX = ("\\HOLTokenNotEqual",1)}

  (* not an element of *)
  val _ = temp_overload_on ("NOTIN", ``\x:'a y:('a -> bool). ~(x IN y)``)
  val _ = temp_set_fixity "NOTIN" (Infix(NONASSOC, 425))
  val _ = temp_unicode_version {u = UChar.not_elementof, tmnm = "NOTIN"}
  val _ = temp_TeX_notation {hol="NOTIN", TeX = ("\\HOLTokenNotIn",1)}
  val _ = temp_TeX_notation {hol=UChar.not_elementof,
                             TeX = ("\\HOLTokenNotIn",1)}

  (* not iff *)
  val _ = temp_overload_on ("<=/=>", ``$<> : bool -> bool -> bool``)
  val _ = temp_set_fixity "<=/=>" (Infix(NONASSOC, 100))
  val _ = temp_unicode_version {u = UChar.not_iff, tmnm = "<=/=>"}
  val _ = temp_TeX_notation {hol="<=/=>", TeX = ("\\HOLTokenNotEquiv",2)}
  val _ = temp_TeX_notation {hol=UChar.not_iff, TeX = ("\\HOLTokenNotEquiv",2)}

  fun tight_equality() = set_fixity "=" (Infix(NONASSOC, 450))

end
