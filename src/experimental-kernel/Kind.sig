signature Kind =
sig

  include FinalKind

  val kd_sub        : (kind,kind)Lib.subst -> kind -> kind Lib.delta
end
