signature TraceRecord =
sig
  val is_active : unit -> bool
  val trace_step_count : unit -> int
  val escape_string : string -> string
end
