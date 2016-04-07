signature BuildCommand =
sig

  type File = Holmake_tools.File
  type build_command = {preincludes : string list, includes : string list} ->
                       Holmake_tools.buildcmds ->
                       File -> bool

  val make_build_command :
      HM_Cline.t Holmake_tools.buildinfo_t ->
      {build_command : build_command, extra_impl_deps : File list,
       mosml_build_command : Holmake_types.env -> bool * bool * string ->
                             File list -> OS.Process.status option}



end
