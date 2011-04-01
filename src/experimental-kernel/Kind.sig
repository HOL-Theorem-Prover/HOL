signature Kind =
sig

  include FinalKind where type rank = Rank.rank

  exception Unchanged

  val tycon_kind_compare : kind * kind -> order

  val qcomb         : ('a * 'a -> 'a) -> ('a -> 'a) -> 'a * 'a -> 'a
  val vsubst_rk     : rank -> kind -> kind
  val vsubst_kd     : (kind,kind)Lib.subst -> kind -> kind
  val vsubst_rk_kd  : rank -> (kind,kind)Lib.subst -> kind -> kind

  val kd_sub        : rank -> (kind,kind)Lib.subst -> kind -> kind Lib.delta

  val prim_match_kind : bool -> kind -> kind
                       -> (rank * bool) * ((kind,kind) Lib.subst * kind list)
                       -> (rank * bool) * ((kind,kind) Lib.subst * kind list)
  val norm_subst    : (rank * bool) * ((kind,kind)Lib.subst * kind list) ->
                      (rank * bool) * ((kind,kind)Lib.subst * kind list)
  val pp_kind       : HOLPP.ppstream -> kind -> unit
  val pp_qkind      : HOLPP.ppstream -> kind -> unit
  val kind_to_string: kind -> string
end
