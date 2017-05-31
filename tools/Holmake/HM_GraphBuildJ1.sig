signature HM_GraphBuildJ1 =
sig

  type include_info = Holmake_tools.include_info
  type File = Holmake_tools.File
  type build_command = include_info -> Holmake_tools.buildcmds -> File -> bool
  type mosml_build_command =
       Holmake_types.env ->
       {noecho : bool, ignore_error : bool, command : string} ->
       File list ->
       OS.Process.status option

  type 'optv buildinfo_t = {
    optv : 'optv, hmake_options : string list,
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
                     include_info -> HM_DepGraph.t -> OS.Process.status

end
