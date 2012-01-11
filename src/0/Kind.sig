signature Kind =
sig

  include FinalKind where type kind = KernelTypes.kind
                      and type rank = KernelTypes.rank

  val tycon_kind_compare : kind * kind -> order

  val prim_match_kind : bool -> kind -> kind
                       -> ((kind,kind) Lib.subst * kind list) * (rank * bool)
                       -> ((kind,kind) Lib.subst * kind list) * (rank * bool)
  val norm_subst     : ((kind,kind)Lib.subst * kind list) * (rank * bool) ->
                       ((kind,kind)Lib.subst * kind list) * (rank * bool)

  val pp_kind       : HOLPP.ppstream -> kind -> unit
  val pp_qkind      : HOLPP.ppstream -> kind -> unit
  val kind_to_string: kind -> string
end
