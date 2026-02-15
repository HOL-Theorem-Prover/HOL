signature TraceExport =
sig

  (* Export proof trace data to a compressed .pftrace file.
     Called by TraceRecord.export_hook when proof tracing is active.

     This module is NOT in the trust boundary: its output is
     independently verified by replaying the trace through the
     kernel (ReplayTrace). If export has a bug, replay catches it.

     Arguments:
       thyname     - theory name
       thy_parents - parent theory names
       exports     - (name, thm) pairs of exported theorems
       types       - interned type list (reverse order from kernel)
       terms       - interned term list (reverse order from kernel)
       counter     - current trace step counter
       ext_cache   - external thm cache (global_id -> (hyps, concl))
       steps_path  - path to temp steps file
       parents_path - path to temp parents file
       thm_id      - function to extract trace_id from a thm
  *)

  type export_args = {
    thyname      : string,
    thy_parents  : string list,
    exports      : (string * Thm.thm) list,
    types        : Type.hol_type list,
    terms        : Term.term list,
    counter      : int,
    ext_cache    : (int, Term.term list * Term.term) Redblackmap.dict,
    steps_path   : string,
    parents_path : string,
    thm_id       : Thm.thm -> int
  }

  val export : export_args -> unit

end
