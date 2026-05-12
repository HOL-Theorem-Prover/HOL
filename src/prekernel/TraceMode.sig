signature TraceMode = sig

  (* Runtime switch for proof-trace machinery. Live reference; writers are
     responsible for not switching mid-theory (intermediate thms built under
     NoTrace have their proof refs stored as deleted_prf, which would leave
     holes if referenced by later thms built under TraceOnly/TraceAndExport). *)
  datatype trace_mode = NoTrace | TraceOnly | TraceAndExport

  (* Default TraceAndExport, overridable at process start via the
     HOL_TRACE_MODE env var. Recognised values (case-sensitive):
       "none"   / "off"      → NoTrace
       "trace"  / "memory"   → TraceOnly
       "export" / "on" / ""  → TraceAndExport
     anything else is treated as TraceAndExport. *)
  val mode : trace_mode ref

end
