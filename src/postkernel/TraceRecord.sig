signature TraceRecord =
sig
  (* TraceRecord sets Thm.trace_hook and Thm.trace_export_hook when loaded.
     All state is internal. The only public API is for testing/diagnostics. *)

  val is_active : unit -> bool
  val trace_step_count : unit -> int
end
