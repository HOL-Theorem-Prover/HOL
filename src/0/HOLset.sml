structure HOLset :> HOLset = struct
  exception NotFound = Splayset.NotFound
  open Splayset
end;
