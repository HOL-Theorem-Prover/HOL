signature BuildCommand =
sig

  type File = Holmake_tools.File
  type include_info = Holmake_tools.include_info
  type build_command = include_info -> Holmake_tools.buildcmds -> File -> bool

  val make_build_command :
      HM_Cline.t Holmake_tools.buildinfo_t ->
      {build_command : build_command, extra_impl_deps : File list,
       mosml_build_command :
         Holmake_types.env ->
         {noecho : bool, ignore_error : bool, command : string} ->
         File list ->
         OS.Process.status option,
       build_graph : include_info -> HM_DepGraph.t -> OS.Process.status }

end
