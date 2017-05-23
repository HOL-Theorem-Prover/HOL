(* -------------------------------------------------------------------------
   Map
   ------------------------------------------------------------------------- *)

signature Map =
sig
   type 'a map
   val mkMap : IntInf.int option * 'a -> 'a map
   val lookup : 'a map * IntInf.int -> 'a
   val update : 'a map * IntInf.int * 'a -> 'a map
   val copy : 'a map -> 'a map
end
