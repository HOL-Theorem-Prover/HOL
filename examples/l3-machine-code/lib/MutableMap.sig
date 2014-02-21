(* -------------------------------------------------------------------------
   Mutable Map
   ------------------------------------------------------------------------- *)

signature MutableMap =
sig
   type 'a map
   val mkMap : int option * 'a -> 'a map
   val lookup : 'a map * int -> 'a
   val update : 'a map * int * 'a -> 'a map
   val copy : 'a map -> 'a map
end
