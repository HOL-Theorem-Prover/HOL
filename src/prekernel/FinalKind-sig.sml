signature FinalKind =
sig
  eqtype kind
  type rank

  val typ           : rank -> kind
  val mk_type_kind  : rank -> kind
  val dest_type_kind: kind -> rank
  val is_type_kind  : kind -> bool

  val mk_var_kind   : string * rank -> kind
  val gen_var_kind  : rank -> kind
  val dest_var_kind : kind -> string * rank
  val is_var_kind   : kind -> bool
  val is_gen_kdvar  : kind -> bool
  val kappa         : kind

  val ==>           : kind * kind -> kind   (* infixr 3 ==> *)
  val is_arrow_kind : kind -> bool
  val kind_dom_rng  : kind -> kind * kind   (* inverts ==>  *)
  val dest_arrow_kind : kind -> kind * kind (* inverts ==>  *)
  val list_mk_arrow_kind : kind list * kind -> kind
  val strip_arrow_kind : kind -> kind list * kind (* inverts list_mk_arrow_kind *)
  val mk_arity      : int -> kind
  val is_arity      : kind -> bool
  val arity_of      : kind -> int
  val rank_of       : kind -> rank
  val polymorphic   : kind -> bool

  val :=:           : kind * kind -> bool   (* infix 3 :=:  *)
  val :>=:          : kind * kind -> bool   (* infix 3 :>=: *)
  val kind_compare  : kind * kind -> order

  val kind_subst    : (kind,kind)Lib.subst -> kind -> kind
  val kind_vars     : kind -> kind list
  val kind_varsl    : kind list -> kind list
  val kind_var_in   : kind -> kind -> bool
  val exists_kdvar  : (kind -> bool) -> kind -> bool

  val inst_rank     : rank -> kind -> kind
  val inst_kind     : (kind,kind)Lib.subst -> kind -> kind (* aligns ranks of subst  *)
  val pure_inst_kind: (kind,kind)Lib.subst -> kind -> kind (* expects ranks to align *)
  val inst_rank_kind: rank -> (kind,kind)Lib.subst -> kind -> kind
  val raw_subst_rank: rank -> (kind,kind)Lib.subst -> rank
  val subst_rank    : (kind,kind)Lib.subst -> rank
  val inst_rank_subst : rank -> (kind,kind)Lib.subst -> (kind,kind)Lib.subst

  val match_kind     : kind -> kind -> rank * (kind,kind) Lib.subst
  val match_kinds    : (kind,kind)Lib.subst -> rank * (kind,kind)Lib.subst
  val raw_match_kind : kind -> kind
                       -> (rank * bool) * ((kind,kind) Lib.subst * kind list)
                       -> (rank * bool) * ((kind,kind) Lib.subst * kind list)
  val match_kind_restr : bool -> kind list -> kind -> kind ->
                         rank * (kind,kind)Lib.subst
  val match_kind_in_context : kind -> kind
                              -> rank * (kind,kind)Lib.subst
                              -> rank * (kind,kind)Lib.subst
  val align_kinds : (kind,kind) Lib.subst ->
                    rank * (kind,kind) Lib.subst

  val kind_size     : kind -> int

end
