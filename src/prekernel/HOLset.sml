structure HOLset :> HOLset = 
struct
  exception NotFound = Redblackset.NotFound
  open Redblackset
end;
