(* -------------------------------------------------------------------------
   Set
   ------------------------------------------------------------------------- *)

signature Set =
sig
   val diff : ''a list * ''a list -> ''a list
   val equal : ''a list * ''a list -> bool
   val insert : ''a * ''a list -> ''a list
   val intersect : ''a list * ''a list -> ''a list
   val isSubset : ''a list * ''a list -> bool
   val mem : ''a * ''a list -> bool
   val mk : ''a list -> ''a list
   val union : ''a list * ''a list -> ''a list
end
