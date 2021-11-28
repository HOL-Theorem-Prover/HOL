signature MB_Monitor =
sig

  val new : {info : string -> unit, warn : string -> unit,
             multidir : bool,
             genLogFile : {tag:string,dir:string} -> string,
             time_limit : Time.time option} ->
            ProcessMultiplexor.monitor *
            {coloured_info : string * string -> unit,
             red : string -> string, green : string -> string,
             bold : string -> string}

end
