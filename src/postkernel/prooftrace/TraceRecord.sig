signature TraceRecord =
sig
  val activate : unit -> unit
  val is_active : unit -> bool
  val trace_step_count : unit -> int
  val escape_string : string -> string
end
