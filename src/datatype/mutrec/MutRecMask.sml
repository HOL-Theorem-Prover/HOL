(*---------------------------------------------------------------------------
 * Provides a way to allow constructor names to be rebound.
 *---------------------------------------------------------------------------*)
structure MutRecMask :> MutRecMask =
struct
  datatype foo = Domain | Range;
end;
