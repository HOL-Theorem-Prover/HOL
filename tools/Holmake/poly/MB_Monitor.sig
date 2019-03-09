signature MB_Monitor =
sig

  val new : {info : string -> unit,
             warn : string -> unit,
             genLogFile : {tag:string} -> string,
             time_limit : Time.time option} ->
            ProcessMultiplexor.monitor

end
