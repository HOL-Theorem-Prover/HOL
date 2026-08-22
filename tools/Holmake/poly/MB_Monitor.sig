signature MB_Monitor =
sig

  val new : {info : string -> unit, warn : string -> unit,
             multidir : bool,
             multitree : bool,
             keep_going : bool,
             genLogFile : {tag:string,dir:string} -> string,
             time_limit : Time.time option} ->
            ProcessMultiplexor.monitor *
            {coloured_info : string * string -> unit,
             red : string -> string, green : string -> string,
             bold : string -> string,
             dirname : string -> string,
               (* How this monitor names a directory, given its absolute
                  path: the same rendering as the directory column of
                  the per-target lines, so that anything else reporting
                  a directory alongside them agrees with it. *)
             final_report : unit -> unit}

end
