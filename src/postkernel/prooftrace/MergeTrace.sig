signature MergeTrace =
sig

  (* Merge per-theory traces into a single self-contained trace.
     Arguments:
       trace_dir       - directory to search for per-theory .pftrace files
       root_theories   - theories to include (with all their ancestors)
       desired_exports - (theory, name) pairs of theorems to export
       output_path     - path for the merged trace file
  *)
  val merge : {
    trace_dir : string,
    root_theories : string list,
    desired_exports : (string * string) list,
    output_path : string
  } -> unit

end
