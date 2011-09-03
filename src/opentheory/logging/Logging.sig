signature Logging =
sig

val start_logging : unit -> unit
val export_thm    : Thm.thm -> unit
val stop_logging  : unit -> unit

end
