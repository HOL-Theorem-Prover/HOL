(*---------------------------------------------------------------------------
 * Provides a way to allow constructor names to be rebound.
 *---------------------------------------------------------------------------*)
structure NestedRecMask :> NestedRecMask =
struct
  datatype foo = Domain | Range;
end;
