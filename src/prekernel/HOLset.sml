structure HOLset :> HOLset = 
struct
  exception NotFound = Randomset.NotFound
  open Randomset
end;
