signature Prerank =
sig
  type rank = Kind.rank

datatype prerank
    = Zerorank
    | Sucrank of prerank
    | Maxrank of prerank list
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
val reset_rank_uvars : prerank -> unit
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
  ((int -> prerank -> prerank -> ('a -> 'a * unit option)) ->
   (int -> prerank -> prerank -> ('a -> 'a * unit option)) ->
   (int -> oprerank option ref -> (prerank -> ('a -> 'a * unit option)))) ->
  ((int -> prerank -> prerank -> ('a -> 'a * unit option)) ->
   (int -> oprerank option ref -> (prerank -> ('a -> 'a * unit option)))) ->
  ((int -> prerank -> prerank -> ('a -> 'a * unit option)) ->
   (int -> prerank -> prerank -> ('a -> 'a * unit option)) ->
   (int -> oprerank option ref -> (prerank -> ('a -> 'a * unit option)))) ->
  int -> prerank -> prerank -> ('a -> 'a * unit option)
val gen_unify_le :
  ((int -> prerank -> prerank -> ('a -> 'a * unit option)) ->
   (int -> prerank -> prerank -> ('a -> 'a * unit option)) ->
   (int -> oprerank option ref -> (prerank -> ('a -> 'a * unit option)))) ->
  ((int -> prerank -> prerank -> ('a -> 'a * unit option)) ->
   (int -> oprerank option ref -> (prerank -> ('a -> 'a * unit option)))) ->
  ((int -> prerank -> prerank -> ('a -> 'a * unit option)) ->
   (int -> prerank -> prerank -> ('a -> 'a * unit option)) ->
   (int -> oprerank option ref -> (prerank -> ('a -> 'a * unit option)))) ->
  int -> prerank -> prerank -> ('a -> 'a * unit option)
val unify : prerank -> prerank -> unit
val unify_le : prerank -> prerank -> unit
val can_unify : prerank -> prerank -> bool
val can_unify_le : prerank -> prerank -> bool

val unsafe_unify :
  int -> prerank -> prerank ->
  ((oprerank option ref * oprerank option) list ->
   (oprerank option ref * oprerank option) list * unit option)

val unsafe_unify_le :
  int -> prerank -> prerank ->
  ((oprerank option ref * oprerank option) list ->
   (oprerank option ref * oprerank option) list * unit option)

val safe_unify :
  int -> prerank -> prerank ->
  ((oprerank option ref * oprerank) list ->
   (oprerank option ref * oprerank) list * unit option)

val safe_unify_le :
  int -> prerank -> prerank ->
  ((oprerank option ref * oprerank) list ->
   (oprerank option ref * oprerank) list * unit option)

(*val apply_subst : (oprerank option ref * prerank) list -> prerank -> prerank*)


val rename_rv : prerank -> prerank list -> (prerank list * prerank option)
val rename_rankvars : prerank -> prerank

val fromRank : rank -> prerank
val remove_made_links : prerank -> prerank
val replace_null_links     : prerank -> unit -> unit * unit option
val var_replace_null_links : prerank -> unit -> unit * unit option
val clean : prerank -> rank
val toRank : prerank -> rank
val pp_prerank : ppstream -> prerank -> unit

val termantiq_constructors : (prerank,Term.term) parse_rank.rankconstructors
val typeantiq_constructors : (prerank,Type.hol_type) parse_rank.rankconstructors
val kindantiq_constructors : (prerank,Kind.kind) parse_rank.rankconstructors
val rankantiq_constructors : (prerank,Kind.rank) parse_rank.rankconstructors

end
