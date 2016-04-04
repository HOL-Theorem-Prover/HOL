signature HM_BaseEnv =
sig

  val mosml_indicator : string
  val make_base_env : HM_Cline.t -> Holmake_types.env
  val print_debug_info : HM_Cline.t -> unit

end
