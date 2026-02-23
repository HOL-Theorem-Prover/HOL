signature MergeTrace =
sig
  (* Merge per-theory traces into a single self-contained trace.
     trace_paths: (theory_name, file_path) pairs
     desired_exports: (theory_name, theorem_name) pairs
     output_path: path for the merged trace file *)
  val merge : {
    trace_paths : (string * string) list,
    desired_exports : (string * string) list,
    output_path : string
  } -> unit
end
