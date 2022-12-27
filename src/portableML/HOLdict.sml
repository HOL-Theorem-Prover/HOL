structure HOLdict :> HOLdict =
struct
  exception NotFound = Redblackmap2.NotFound
  open Redblackmap2
end
