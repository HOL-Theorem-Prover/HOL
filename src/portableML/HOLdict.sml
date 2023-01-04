structure HOLdict :> HOLdict =
struct
  exception NotFound = Redblackmap.NotFound
  open Redblackmap
end
