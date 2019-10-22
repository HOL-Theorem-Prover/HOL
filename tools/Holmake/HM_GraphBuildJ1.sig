signature HM_GraphBuildJ1 =
sig

  type File = Holmake_tools.File
  type dep = Holmake_tools.dep
  type build_command = HM_DepGraph.t -> Holmake_tools.include_info ->
                       dep Holmake_tools.buildcmds -> File -> bool
  type mosml_build_command =
       Holmake_types.env ->
       {noecho : bool, ignore_error : bool, command : string} ->
       dep list ->
       OS.Process.status option

  type 'optv buildinfo_t = {
    optv : 'optv,
    actual_overlay : string option,
    envlist : string -> string list,
    hmenv : Holmake_types.env,
    quit_on_failure : bool,
    outs : Holmake_tools.output_functions,
    SIGOBJ : string
  }







  val graphbuildj1 : {build_command : build_command,
                      mosml_build_command : mosml_build_command,
                      outs : Holmake_tools.output_functions,
                      keep_going : bool,
                      quiet : bool,
                      system : string -> OS.Process.status,
                      hmenv : Holmake_types.env} ->
                     HM_DepGraph.t -> OS.Process.status * HM_DepGraph.t

end
