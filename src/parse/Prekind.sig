signature Prekind =
sig

 datatype prekind0
    = Varkind of string
    | Typekind
    | Arrowkind of prekind * prekind
    | UVarkind of prekind option ref
 and prekind = PK of prekind0 locn.located

val eq : prekind -> prekind -> bool

val typ : prekind
val is_var_kind : prekind -> bool
val ==> : prekind * prekind -> prekind
val mk_arrow_kind : prekind * prekind -> prekind
val list_mk_arrow_kind : prekind list * prekind -> prekind
val mk_arity : int -> prekind
val prekind_compare : prekind * prekind -> order
val prekind_to_string : prekind -> string

val kindvars : prekind -> string list
val new_uvar : unit -> prekind
val uvars_of : prekind -> prekind option ref list
val ref_occurs_in : prekind option ref * prekind -> bool
val ref_equiv : prekind option ref * prekind -> bool
val has_free_uvar : prekind -> bool



(* first argument is a function which performs a binding between a
   prekind reference and another prekind, updating some sort of environment
   (the 'a), returning the new alpha and a unit option, SOME () for a
   success, and a NONE, if not.

   To further complicate things, the bind argument also gets a copy of
   gen_unify to call, if it should choose.
*)
val gen_unify :
  ((prekind -> prekind -> ('a -> 'a * unit option)) ->
   (prekind option ref -> (prekind -> ('a -> 'a * unit option)))) ->
  prekind -> prekind -> ('a -> 'a * unit option)
val unify : prekind -> prekind -> unit
val can_unify : prekind -> prekind -> bool

val unsafe_unify :
  prekind -> prekind ->
  ((prekind option ref * prekind option) list ->
   (prekind option ref * prekind option) list * unit option)

val safe_unify :
  prekind -> prekind ->
  ((prekind option ref * prekind) list ->
   (prekind option ref * prekind) list * unit option)

(*val apply_subst : (prekind option ref * prekind) list -> prekind -> prekind*)

val rename_kv : string list -> prekind -> (string * prekind) list
                        -> ((string * prekind) list * prekind option)
val rename_kindvars : string list -> prekind -> prekind
val fromKind : Kind.kind -> prekind
val remove_made_links : prekind -> prekind
val replace_null_links : prekind -> string list -> string list * unit option
val clean : prekind -> Kind.kind
val toKind : prekind -> Kind.kind
val chase : prekind -> prekind
val pp_prekind : ppstream -> prekind -> unit

val termantiq_constructors : (prekind,Term.term) parse_kind.kindconstructors
val typeantiq_constructors : (prekind,Type.hol_type) parse_kind.kindconstructors
val kindantiq_constructors : (prekind,Kind.kind) parse_kind.kindconstructors

end
