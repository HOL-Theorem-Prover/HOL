structure HOLset :> HOLset = struct
  exception NotFound = Binaryset.NotFound
  open Binaryset
end;
