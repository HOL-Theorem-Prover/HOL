signature Holmake_tools =
sig

  type output_functions = {warn : string -> unit, info : string -> unit,
                           tgtfatal : string -> unit,
                           diag : string -> unit}
  val output_functions : {quiet_flag: bool, debug:bool} -> output_functions

  val do_lastmade_checks: output_functions ->
                          {no_lastmakercheck : bool} ->
                          unit

end

