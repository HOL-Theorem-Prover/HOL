signature Pretype =
sig

 datatype pretype0
    = Vartype of Type.tyvar
    | Contype of {Thy : string, Tyop : string, Kind : Type.kind, Rank : int}
    | TyApp of pretype * pretype
    | TyUniv of Type.tyvar * pretype
    | TyAbst of Type.tyvar * pretype
    | UVar of pretype option ref
 and pretype = PT of pretype0 locn.located

 val --> : pretype * pretype -> pretype

val tyvars : pretype -> Type.tyvar list
val new_uvar : unit -> pretype
val uvars_of : pretype -> pretype option ref list
val ref_occurs_in : pretype option ref * pretype -> bool
val ref_equiv : pretype option ref * pretype -> bool
val has_free_uvar : pretype -> bool



(* first argument is a function which performs a binding between a
   pretype reference and another pretype, updating some sort of environment
   (the 'a), returning the new alpha and a unit option, SOME () for a
   success, and a NONE, if not.

   To further complicate things, the bind argument also gets a copy of
   gen_unify to call, if it should choose.
*)
val gen_unify :
  ((pretype -> pretype -> ('a -> 'a * unit option)) ->
   (pretype option ref -> (pretype -> ('a -> 'a * unit option)))) ->
  pretype -> pretype -> ('a -> 'a * unit option)
val unify : pretype -> pretype -> unit
val can_unify : pretype -> pretype -> bool

val safe_unify :
  pretype -> pretype ->
  ((pretype option ref * pretype) list ->
   (pretype option ref * pretype) list * unit option)
val apply_subst : (pretype option ref * pretype) list -> pretype -> pretype

val rename_typevars : pretype -> pretype
val fromType : Type.hol_type -> pretype
val remove_made_links : pretype -> pretype
val replace_null_links : pretype -> string list -> string list * unit option
val clean : pretype -> Type.hol_type
val toType : pretype -> Type.hol_type
val chase : pretype -> pretype
end
