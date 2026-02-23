signature TraceExport =
sig

  (* Export proof trace data to a .pftrace file.
     Called by TraceRecord.export_hook when proof tracing is active.

     This module is NOT in the trust boundary: its output is
     independently verified by replaying the trace through the
     kernel (ReplayTrace). If export has a bug, replay catches it.

     Arguments:
       thyname    - theory name
       exports    - (name, thm) pairs of exported theorems
       types      - interned type list (from kernel)
       terms      - interned term list (from kernel)
       n_steps    - number of step lines in the temp file
       steps_path - path to temp steps file (complete lines with parents)
       thm_line   - maps a thm to its line number in the temp file
  *)

  type export_args = {
    thyname    : string,
    exports    : (string * Thm.thm) list,
    types      : Type.hol_type list,
    terms      : Term.term list,
    n_steps    : int,
    steps_path : string,
    thm_line   : Thm.thm -> int
  }

  val escape_string : string -> string
  val export : export_args -> unit

end
