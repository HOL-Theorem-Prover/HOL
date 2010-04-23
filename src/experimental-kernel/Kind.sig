signature Kind =
sig

  include FinalKind

  val kd_sub        : (kind,kind)Lib.subst -> kind -> kind Lib.delta
  val pp_kind       : HOLPP.ppstream -> kind -> unit
  val pp_qkind      : HOLPP.ppstream -> kind -> unit
  val kind_to_string: kind -> string
end
