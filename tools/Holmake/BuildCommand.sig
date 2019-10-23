signature BuildCommand =
sig

  include HM_GraphBuildJ1

  val make_build_command :
      HM_Cline.t buildinfo_t ->
      {extra_impl_deps : dep list,
       build_graph : HM_DepGraph.t -> OS.Process.status * HM_DepGraph.t}

end
