signature Logging =
sig

val start_logging : unit -> unit
val export_thm    : Thm.thm -> Thm.thm
val stop_logging  : unit -> unit

end
