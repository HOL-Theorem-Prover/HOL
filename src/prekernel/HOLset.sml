structure HOLset :> HOLset =
struct
  exception NotFound = Redblackset.NotFound
  open Redblackset

  fun pp_holset pps s = HOLPP.add_string pps "<holset>"
end
