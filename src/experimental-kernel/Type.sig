signature Type =
sig

  include FinalType where type kind = Kind.kind
                      and type rank = Rank.rank

(* The following are declarations beyond those in FinalType-sig.sml. *)

  exception Unchanged
  exception NeedToRename of tyvar

  (* The following "raw" functions expect type-beta-reduced arguments: *)
  val raw_dom_rng   : hol_type -> hol_type * hol_type  (* inverts -->  *)
  val raw_compare   : hol_type * hol_type -> order
  val raw_type_eq   : hol_type -> hol_type -> bool
  val raw_empty_tyset : hol_type  HOLset.set

  val ty_sub        : (hol_type,hol_type) Lib.subst -> hol_type -> hol_type Lib.delta
  val pure_ty_sub   : (hol_type,hol_type) Lib.subst -> hol_type -> hol_type Lib.delta (* expects kinds, ranks match *)
  val rk_kd_ty_sub  : rank -> (kind,kind) Lib.subst ->
                      (hol_type,hol_type) Lib.subst -> hol_type -> hol_type Lib.delta (* expects kinds, ranks match *)
  val vsubst_rkt    : rank -> (kind,kind) Lib.subst ->
                      (hol_type, (string HOLset.set)Susp.susp * hol_type)Binarymap.dict
                      -> hol_type -> hol_type
  val vsubst        : (hol_type, (string HOLset.set)Susp.susp * hol_type)Binarymap.dict
                      -> hol_type -> hol_type
  val ssubst        : (hol_type, hol_type)Binarymap.dict -> hol_type -> hol_type

  val compare0      : int -> (hol_type,int)Binarymap.dict * (hol_type,int)Binarymap.dict
                          -> hol_type * hol_type -> order
  val prim_compare0 : int -> (hol_type,int)Binarymap.dict * (hol_type,int)Binarymap.dict
                          -> hol_type * hol_type -> order
  val type_vars_set : hol_type HOLset.set -> hol_type HOLset.set -> hol_type list -> hol_type HOLset.set
  val free_names    : hol_type -> string HOLset.set
  val inst_rank_kind1 : rank -> (kind, kind)Lib.subst -> (tyvar, kind)Binarymap.dict
                        -> hol_type -> hol_type

  val type_pmatch : hol_type HOLset.set -> {redex : hol_type, residue : hol_type} list ->
                    hol_type -> hol_type ->
                    (hol_type,hol_type)Lib.subst *
                    ((hol_type,hol_type)Lib.subst * hol_type * hol_type) list ->
                    (hol_type,hol_type)Lib.subst *
                    ((hol_type,hol_type)Lib.subst * hol_type * hol_type) list
  val type_homatch : kind list -> hol_type HOLset.set ->
                     rank * bool -> (kind,kind)Lib.subst * kind list ->
                     (hol_type,hol_type)Lib.subst *
                     ((hol_type,hol_type)Lib.subst * hol_type * hol_type) list ->
                     (hol_type,hol_type)Lib.subst
  val separate_insts_ty : bool -> rank * bool -> kind list ->
                          ((kind,kind)Lib.subst * kind list) ->
                          (hol_type,hol_type)Lib.subst ->
                          (hol_type,hol_type)Lib.subst ->
                          (hol_type, int)Lib.subst *
                          (hol_type,hol_type)Lib.subst *
                          ((kind,kind)Lib.subst * kind list) * (rank * bool)
  val get_rank_kind_insts : kind list -> {redex : hol_type, residue : hol_type} list ->
                            {redex : hol_type, residue : hol_type} list ->
                            (rank * bool) * ({redex : kind, residue : kind} list * kind list) ->
                            (rank * bool) * ({redex : kind, residue : kind} list * kind list)

  (* accessing and manipulating theory information for types *)
  val prim_new_type : {Thy:string, Tyop:string} -> kind -> unit
  val prim_delete_type : {Thy:string, Tyop:string} -> unit
  val thy_types : string -> (string * int) list
  val thy_type_oprs : string -> (string * kind) list
  val del_segment : string -> unit
  val uptodate_type : hol_type -> bool

  val type_to_string: hol_type -> string

end
