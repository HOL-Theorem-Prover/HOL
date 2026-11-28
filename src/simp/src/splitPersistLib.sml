(* Explicit opt-in only: ordinary simpLib/splitLib must not depend on this
   module. Split-bearing theories must also add this ML dependency to their
   exports so registration precedes decoding and ancestry replay. *)
structure splitPersistLib :> splitPersistLib =
struct
  val _ = splitLib.enable_split_attribute ()
end
