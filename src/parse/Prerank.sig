signature Prerank =
sig

 datatype prerank
    = Zerorank
    | Sucrank of prerank
    | Maxrank of prerank * prerank
    | UVarrank of prerank option ref

val eq : prerank -> prerank -> bool
val prerank_compare : prerank * prerank -> order

val new_uvar : unit -> prerank
val uvars_of : prerank -> prerank option ref list
val ref_occurs_in : prerank option ref * prerank -> bool
val ref_equiv : prerank option ref * prerank -> bool
val has_free_uvar : prerank -> bool



(* first argument is a function which performs a binding between a
   prerank reference and another prerank, updating some sort of environment
   (the 'a), returning the new alpha and a unit option, SOME () for a
   success, and a NONE, if not.

   To further complicate things, the bind argument also gets a copy of
   gen_unify to call, if it should choose.
*)
val gen_unify :
  ((prerank -> prerank -> ('a -> 'a * unit option)) ->
   (prerank option ref -> (prerank -> ('a -> 'a * unit option)))) ->
  ((prerank -> prerank -> ('a -> 'a * unit option)) ->
   (prerank option ref -> (prerank -> ('a -> 'a * unit option)))) ->
  prerank -> prerank -> ('a -> 'a * unit option)
val unify : prerank -> prerank -> unit
val can_unify : prerank -> prerank -> bool

val unsafe_unify :
  prerank -> prerank ->
  ((prerank option ref * prerank option) list ->
   (prerank option ref * prerank option) list * unit option)

val safe_unify :
  prerank -> prerank ->
  ((prerank option ref * prerank) list ->
   (prerank option ref * prerank) list * unit option)

val apply_subst : (prerank option ref * prerank) list -> prerank -> prerank

val fromRank : int -> prerank
val remove_made_links : prerank -> prerank
val replace_null_links : prerank -> string list -> string list * unit option
val clean : prerank -> int
val toRank : prerank -> int
end
