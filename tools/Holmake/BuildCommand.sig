signature BuildCommand =
sig

  include HM_GraphBuildJ1

  val make_build_command :
      HM_Cline.t buildinfo_t ->
      {extra_impl_deps : File list,
       build_graph : include_info -> HM_DepGraph.t -> OS.Process.status }

end
