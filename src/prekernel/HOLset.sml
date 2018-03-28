structure HOLset :> HOLset =
struct
  exception NotFound = Redblackset.NotFound
  open Redblackset

  fun pp_holset dpth ipp s = HOLPP.PrettyString "<holset>"
end
