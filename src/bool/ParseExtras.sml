structure ParseExtras :> ParseExtras =
struct

  open Parse
  open Unicode
  open TexTokenMap


  fun tight_equality() = set_fixity "=" (Infix(NONASSOC, 450))

end
