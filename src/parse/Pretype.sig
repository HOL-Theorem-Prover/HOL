signature Pretype =
sig
  type prekind = Prekind.prekind
  type kind = Kind.kind
  type hol_type = Type.hol_type
  type pretyvar = string * prekind * int (* rank *)
  type tyvar = Type.tyvar

 datatype pretype0
    = Vartype of pretyvar
    | Contype of {Thy : string, Tyop : string, Kind : prekind, Rank : int}
    | TyApp  of pretype * pretype
    | TyUniv of pretype * pretype
    | TyAbst of pretype * pretype
    | TyKindConstr of {Ty : pretype, Kind : prekind}
    | TyRankConstr of {Ty : pretype, Rank : int}
    | UVar of pretype option ref
 and pretype = PT of pretype0 locn.located

val eq : pretype -> pretype -> bool

val --> : pretype * pretype -> pretype
val mk_app_type : pretype * pretype -> pretype
val dest_app_type : pretype -> pretype * pretype
val mk_univ_type : pretype * pretype -> pretype
val dest_univ_type : pretype -> pretype * pretype
val mk_abs_type : pretype * pretype -> pretype
val dest_abs_type : pretype -> pretype * pretype

val kindvars : pretype -> string list
val tyvars : pretype -> string list
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
  (prekind -> prekind -> ('a -> 'a * unit option)) ->
  ((pretype -> pretype -> ('a -> 'a * unit option)) ->
   (pretype option ref -> (pretype -> ('a -> 'a * unit option)))) ->
  pretype -> pretype -> ('a -> 'a * unit option)
val unify : pretype -> pretype -> unit
val can_unify : pretype -> pretype -> bool

val safe_unify :
  pretype -> pretype ->
  ((prekind option ref * prekind) list * (pretype option ref * pretype) list ->
   ((prekind option ref * prekind) list * (pretype option ref * pretype) list) * unit option)
val apply_subst : (pretype option ref * pretype) list -> pretype -> pretype

val rename_typevars : pretype -> pretype
val fromType : hol_type -> pretype
val remove_made_links : pretype -> pretype
val replace_null_links : pretype -> string list * string list
                         -> (string list * string list) * unit option
val clean : pretype -> hol_type
val toType : pretype -> hol_type
val chase : pretype -> pretype
end
