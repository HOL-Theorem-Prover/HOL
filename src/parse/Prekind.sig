signature Prekind =
sig
  type prerank = Prerank.prerank
  type rank = Kind.rank
  type kind = Kind.kind

 datatype prekind0
    = Varkind of string * prerank
    | Typekind of prerank
    | Arrowkind of prekind * prekind
    | KdRankConstr of {Kd : prekind, Rank : prerank}
    | UVarkind of uvarkind ref
 and uvarkind
    = SOMEK of prekind
    | NONEK of prerank
 and prekind = PK of prekind0 locn.located

val eq : prekind -> prekind -> bool
val ge : prekind -> prekind -> bool
val eqr: prekind -> prekind -> bool (* disregards ranks *)

val prank_of : prekind -> prerank

val typ : prerank -> prekind
val is_type_kind: prekind -> bool
val dest_type_kind : prekind -> prerank
val is_var_kind : prekind -> bool
val dest_var_kind : prekind -> string * prerank
val ==> : prekind * prekind -> prekind
val mk_arrow_kind : prekind * prekind -> prekind
val list_mk_arrow_kind : prekind list * prekind -> prekind
val dest_arrow_kind : prekind -> prekind * prekind
val is_arrow_kind : prekind -> bool
val dom_rng : prekind -> prekind * prekind
val mk_arity : int -> prekind
val prekind_compare : prekind * prekind -> order

val kindvars : prekind -> string list
val new_uvar : prerank -> prekind
val all_new_uvar : unit -> prekind
val uvars_of : prekind -> uvarkind ref list
val reset_rank_uvars : prekind -> unit
val ref_occurs_in : uvarkind ref * prekind -> bool
val ref_equiv : uvarkind ref * prekind -> bool
val has_free_uvar : prekind -> bool



(* first argument is a function which performs a binding between a
   prekind reference and another prekind, updating some sort of environment
   (the 'a), returning the new alpha and a unit option, SOME () for a
   success, and a NONE, if not.

   To further complicate things, the bind argument also gets a copy of
   gen_unify to call, if it should choose.
*)
(*
val gen_unify :
  (int -> prerank -> prerank -> ('a -> 'a * unit option)) ->
  (int -> prerank -> prerank -> ('a -> 'a * unit option)) ->
  (int -> prerank -> prerank -> ('a -> 'a * unit option)) ->
  (int -> (prekind -> prekind -> ('a -> 'a * unit option)) ->
   (uvarkind ref -> (prekind -> ('a -> 'a * unit option)))) ->
  string -> int -> prekind -> prekind -> ('a -> 'a * unit option)
*)
val unify : prekind -> prekind -> unit
val unify_le : prekind -> prekind -> unit
val can_unify : prekind -> prekind -> bool

val unsafe_unify :
  int -> prekind -> prekind ->
  (  ((order * prerank) option ref * (order * prerank) option) list
   * (uvarkind ref * uvarkind) list ->
   (  ((order * prerank) option ref * (order * prerank) option) list
    * (uvarkind ref * uvarkind) list)
   * unit option)

val unsafe_unify_le :
  int -> prekind -> prekind ->
  (  ((order * prerank) option ref * (order * prerank) option) list
   * (uvarkind ref * uvarkind) list ->
   (  ((order * prerank) option ref * (order * prerank) option) list
    * (uvarkind ref * uvarkind) list)
   * unit option)

val unsafe_conty_unify :
  int -> prekind -> prekind ->
  (  ((order * prerank) option ref * (order * prerank) option) list
   * (uvarkind ref * uvarkind) list ->
   (  ((order * prerank) option ref * (order * prerank) option) list
    * (uvarkind ref * uvarkind) list)
   * unit option)

val safe_unify :
  int -> prekind -> prekind ->
  (  ((order * prerank) option ref * (order * prerank)) list
   * (uvarkind ref * uvarkind) list ->
   (  ((order * prerank) option ref * (order * prerank)) list
    * (uvarkind ref * uvarkind) list)
   * unit option)

val safe_unify_le :
  int -> prekind -> prekind ->
  (  ((order * prerank) option ref * (order * prerank)) list
   * (uvarkind ref * uvarkind) list ->
   (  ((order * prerank) option ref * (order * prerank)) list
    * (uvarkind ref * uvarkind) list)
   * unit option)

val safe_conty_unify :
  int -> prekind -> prekind ->
  (  ((order * prerank) option ref * (order * prerank)) list
   * (uvarkind ref * uvarkind) list ->
   (  ((order * prerank) option ref * (order * prerank)) list
    * (uvarkind ref * uvarkind) list)
   * unit option)

(*val apply_subst : (uvarkind ref * prekind) list -> prekind -> prekind*)

val rename_kv : string list -> prekind -> prerank list * (string * prekind) list
                        -> ((prerank list * (string * prekind) list) * prekind option)
val rename_kindvars : string list -> prekind -> prekind
val fromKind : kind -> prekind
val remove_made_links : prekind -> prekind
val replace_null_links : prekind -> unit * string list ->
                                   (unit * string list) * unit option
val var_replace_null_links : prekind -> unit * string list ->
                                   (unit * string list) * unit option
val clean : prekind -> kind
val toKind : prekind -> kind
val chase : prekind -> prekind
val pp_prekind : ppstream -> prekind -> unit
val prekind_to_string : prekind -> string
val print_prekind : prekind -> unit

val checkrank :
      (kind -> string) option
        -> prekind -> unit
val rankcheck :
      (kind -> string) option
        -> prekind -> kind

datatype rcheck_error =
         KdRankConstrFail of kind * rank
       | KdRankLEConstrFail of kind * rank

val last_rcerror : (rcheck_error * locn.locn) option ref

val termantiq_constructors : (prekind,Term.term) parse_kind.kindconstructors
val typeantiq_constructors : (prekind,Type.hol_type) parse_kind.kindconstructors
val kindantiq_constructors : (prekind,Kind.kind) parse_kind.kindconstructors

end
