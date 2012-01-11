signature Type =
sig

  include FinalType where type hol_type = KernelTypes.hol_type
                          and type kind = KernelTypes.kind
                          and type rank = KernelTypes.rank

  val kd_of         : hol_type -> kind list -> kind
  val rk_of         : hol_type -> kind list -> rank
  val rank_of_univ_dom : hol_type -> rank
  val rank_of_exist_dom : hol_type -> rank
  val check_kind_of : hol_type -> kind
  val is_well_kinded: hol_type -> bool

  val is_bvartype   : hol_type -> bool

  val break_type    : hol_type -> KernelTypes.tyconst * hol_type list

  val type_vars_lr  : hol_type -> hol_type list
  val mk_fun_type   : hol_type * hol_type -> kind list -> hol_type
  val raw_dom_rng   : hol_type -> hol_type * hol_type  (* inverts -->  *)

  val prim_kind_match_type : hol_type -> hol_type
                      -> ( (hol_type,hol_type) Lib.subst * hol_type list ) *
                         ( (kind,kind) Lib.subst * kind list ) * (rank * bool)
                      -> ( (hol_type,hol_type) Lib.subst * hol_type list ) *
                         ( (kind,kind) Lib.subst * kind list ) * (rank * bool)
  exception HIGHER_ORDER
  val RM            : hol_type list -> hol_type list
                      -> (hol_type,hol_type) Lib.subst * hol_type HOLset.set
                      -> (hol_type,hol_type) Lib.subst * hol_type HOLset.set

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
                            ({redex : kind, residue : kind} list * kind list) * (rank * bool) ->
                            ({redex : kind, residue : kind} list * kind list) * (rank * bool)

  val ho_match_type0 : bool -> bool -> kind list -> hol_type HOLset.set -> hol_type -> hol_type
                       -> (hol_type,hol_type)Lib.subst * (kind,kind)Lib.subst * rank
  val ho_match_type  : bool -> kind list -> hol_type HOLset.set -> hol_type -> hol_type
                       -> (hol_type,hol_type)Lib.subst * (kind,kind)Lib.subst * rank

  val unbound_ty    : hol_type -> bool
  val pp_raw_type   : HOLPP.ppstream -> hol_type -> unit
  val type_to_string: hol_type -> string
end;
