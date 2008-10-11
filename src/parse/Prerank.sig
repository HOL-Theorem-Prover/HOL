signature Prerank =
sig

datatype prerank
    = Zerorank
    | Sucrank of prerank
    | Maxrank of prerank * prerank
    | UVarrank of (order * prerank) option ref

type oprerank = order * prerank

(* In UVarrank, if the order is EQUAL then the UVarrank is equal to the contained rank;
   if the bool is LESS then the UVarrank is less than or equal to the contained rank, or
   if the bool is GREATER then the UVarrank is greater than or equal to the contained rank. *)

val mk_Maxrank : prerank * prerank -> prerank

val eq : prerank -> prerank -> bool
val leq : prerank -> prerank -> bool
val prerank_compare : prerank * prerank -> order
val prerank_to_string : prerank -> string

val new_uvar : unit -> prerank
val uvars_of : prerank -> oprerank option ref list
val ref_occurs_in : oprerank option ref * prerank -> bool
val ref_equiv : oprerank option ref * prerank -> bool
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
   (prerank -> prerank -> ('a -> 'a * unit option)) ->
   (oprerank option ref -> (prerank -> ('a -> 'a * unit option)))) ->
  ((prerank -> prerank -> ('a -> 'a * unit option)) ->
   (oprerank option ref -> (prerank -> ('a -> 'a * unit option)))) ->
  ((prerank -> prerank -> ('a -> 'a * unit option)) ->
   (oprerank option ref -> (prerank -> ('a -> 'a * unit option)))) ->
  prerank -> prerank -> ('a -> 'a * unit option)
val gen_unify_le :
  ((prerank -> prerank -> ('a -> 'a * unit option)) ->
   (oprerank option ref -> (prerank -> ('a -> 'a * unit option)))) ->
  ((prerank -> prerank -> ('a -> 'a * unit option)) ->
   (oprerank option ref -> (prerank -> ('a -> 'a * unit option)))) ->
  prerank -> prerank -> ('a -> 'a * unit option)
val unify : prerank -> prerank -> unit
val unify_le : prerank -> prerank -> unit
val can_unify : prerank -> prerank -> bool
val can_unify_le : prerank -> prerank -> bool

val unsafe_unify :
  prerank -> prerank ->
  ((oprerank option ref * oprerank option) list ->
   (oprerank option ref * oprerank option) list * unit option)

val unsafe_unify_le :
  prerank -> prerank ->
  ((oprerank option ref * oprerank option) list ->
   (oprerank option ref * oprerank option) list * unit option)

val safe_unify :
  prerank -> prerank ->
  ((oprerank option ref * oprerank) list ->
   (oprerank option ref * oprerank) list * unit option)

val safe_unify_le :
  prerank -> prerank ->
  ((oprerank option ref * oprerank) list ->
   (oprerank option ref * oprerank) list * unit option)

(*val apply_subst : (oprerank option ref * prerank) list -> prerank -> prerank*)


val rename_rv : bool -> prerank -> prerank list -> (prerank list * prerank option)
val rename_rankvars : prerank -> prerank

val fromRank : int -> prerank
val remove_made_links : prerank -> prerank
val replace_null_links : prerank -> string list -> string list * unit option
val clean : prerank -> int
val toRank : prerank -> int
end
