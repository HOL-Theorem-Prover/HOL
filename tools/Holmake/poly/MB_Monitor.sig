signature MB_Monitor =
sig

  val new : {info : string -> unit, warn : string -> unit,
             genLogFile : {tag:string} -> string,
             keep_going : bool} ->
            (ProcessMultiplexor.monitor_message ->
             ProcessMultiplexor.client_cmd option)

end
