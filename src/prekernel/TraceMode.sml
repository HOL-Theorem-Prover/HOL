structure TraceMode :> TraceMode = struct

datatype trace_mode = NoTrace | TraceOnly | TraceAndExport

val initial =
  case OS.Process.getEnv "HOL_TRACE_MODE" of
    SOME "none"   => NoTrace
  | SOME "off"    => NoTrace
  | SOME "trace"  => TraceOnly
  | SOME "memory" => TraceOnly
  | SOME "export" => TraceAndExport
  | SOME "on"     => TraceAndExport
  | _             => TraceAndExport

val mode : trace_mode ref = ref initial

end
