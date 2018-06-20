signature HM_BaseEnv =
sig

  val make_base_env : HM_Cline.t -> Holmake_types.env
  val debug_info : HM_Cline.t -> string

end
