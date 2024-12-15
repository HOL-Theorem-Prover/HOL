signature Pretype =
sig

datatype pretype = datatype Pretype_dtype.pretype

structure Env : sig
  type t
  val lookup : t -> int -> pretype option
  val update : (int * pretype) -> t -> t
  val empty : t
  val new : t -> t * int
  val toList : t -> (int * pretype option) list
end

type error = typecheck_error.error
type 'a in_env = (Env.t,'a,error) errormonad.t

val tyvars : pretype -> string list in_env
val new_uvar : pretype in_env
val ref_occurs_in : int * pretype -> bool in_env
val ref_equiv : int * pretype -> bool in_env
val has_unbound_uvar : pretype -> bool in_env
val mk_fun_ty : pretype * pretype -> pretype

val unify : pretype -> pretype -> unit in_env
val can_unify : pretype -> pretype -> bool in_env

val apply_subst : Env.t -> pretype -> pretype

val rename_typevars : string list -> pretype -> pretype in_env
val rename_tv : string list -> pretype ->
                (Env.t * (string * pretype) list, pretype, error) errormonad.t
val fromType : Type.hol_type -> pretype
val remove_made_links : pretype -> pretype in_env
val replace_null_links :
    pretype -> (Env.t * string list, pretype, error) errormonad.t
val typecheck_listener : (pretype -> Env.t -> unit) ref
val clean : pretype -> Type.hol_type
val toTypeM : pretype -> Type.hol_type in_env
val toType : pretype -> Type.hol_type
val chase : pretype -> pretype in_env

val pp_pretype : pretype -> HOLPP.pretty

val termantiq_constructors : (pretype,Term.term) parse_type.tyconstructors
val typantiq_constructors : (pretype,Type.hol_type) parse_type.tyconstructors

end

(*
   [chase pty]  If pty is of the form (dom --> rng), once all necessary
   uvar references have been followed, returns rng.

   [rename_typvars avds pty]  Avoiding type variables with names from avds,
   renames Vartypes into uvar references.

   [has_unbound_uvar pty] Returns true if pty includes (after chasing bound
   uvars), any unbound uvars.

   [mk_fun_ty (dom,rng)] Makes the pretype corresponding to the function space
   from dom to rng.
*)
