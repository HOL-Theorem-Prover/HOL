signature Pretype =
sig
  type prekind = Prekind.prekind
  type prerank = Prerank.prerank
  type kind = Kind.kind
  type hol_type = Type.hol_type
  type pretyvar = string * prekind * prerank
  type tyvar = Type.tyvar
  type term = Term.term

 datatype pretype0
    = Vartype of pretyvar
    | Contype of {Thy : string, Tyop : string, Kind : prekind, Rank : prerank}
    | TyApp  of pretype * pretype
    | TyUniv of pretype * pretype
    | TyAbst of pretype * pretype
    | TyKindConstr of {Ty : pretype, Kind : prekind}
    | TyRankConstr of {Ty : pretype, Rank : prerank}
    | UVar of uvartype ref
 and uvartype
    = SOMEU of pretype
    | NONEU of prekind * prerank
 and pretype = PT of pretype0 locn.located

val tylocn : pretype -> locn.locn

val eq : pretype -> pretype -> bool

val --> : pretype * pretype -> pretype
val dom_rng : pretype -> pretype * pretype
val dest_var_type : pretype -> pretyvar
val mk_app_type : pretype * pretype -> pretype
val dest_app_type : pretype -> pretype * pretype
val mk_univ_type : pretype * pretype -> pretype
val dest_univ_type : pretype -> pretype * pretype
val mk_abs_type : pretype * pretype -> pretype
val dest_abs_type : pretype -> pretype * pretype

val beta_conv_ty : pretype -> pretype
val deep_beta_conv_ty : pretype -> pretype

val pkind_of : pretype -> prekind
val prank_of : pretype -> prerank
val is_atom  : pretype -> bool

val kindvars : pretype -> string list
val tyvars : pretype -> string list
val new_uvar : (prekind * prerank) -> pretype
val all_new_uvar : unit -> pretype
val uvars_of : pretype -> uvartype ref list
val ref_occurs_in : uvartype ref * pretype -> bool
val ref_equiv : uvartype ref * pretype -> bool
val has_free_uvar : pretype -> bool

val prekind_rank_compare : (prekind * prerank) * (prekind * prerank) -> order
val pretyvar_compare : pretyvar * pretyvar -> order


(* first argument is a function which performs a binding between a
   pretype reference and another pretype, updating some sort of environment
   (the 'a), returning the new alpha and a unit option, SOME () for a
   success, and a NONE, if not.

   To further complicate things, the bind argument also gets a copy of
   gen_unify to call, if it should choose.
*)
val gen_unify :
  (prekind -> prekind -> ('a -> 'a * unit option)) ->
  (prerank -> prerank -> ('a -> 'a * unit option)) ->
  ((pretype -> pretype -> ('a -> 'a * unit option)) ->
   (uvartype ref -> (pretype -> ('a -> 'a * unit option)))) ->
  pretyvar list -> pretyvar list ->
  pretype -> pretype -> ('a -> 'a * unit option)
val unify : pretype -> pretype -> unit
val can_unify : pretype -> pretype -> bool

val safe_unify :
  pretype -> pretype ->
  ((prekind option ref * prekind) list * (prerank option ref * prerank) list * (uvartype ref * pretype) list ->
   ((prekind option ref * prekind) list * (prerank option ref * prerank) list * (uvartype ref * pretype) list) * unit option)
val apply_subst : (uvartype ref * pretype) list -> pretype -> pretype
val type_subst  : {redex : pretype, residue : pretype} list -> pretype -> pretype

val rename_typevars : pretype -> pretype
val fromType : hol_type -> pretype
val pretype_to_string : pretype -> string
val remove_made_links : pretype -> pretype
val replace_null_links : pretype -> string list * string list
                         -> (string list * string list) * unit option
val clean : pretype -> hol_type
val toType : pretype -> hol_type
val chase : pretype -> pretype

val checkkind :
      ((hol_type -> string) * (kind -> string)) option
        -> pretype -> unit
val kindcheck :
      ((hol_type -> string) * (kind -> string)) option
        -> pretype -> hol_type
end
