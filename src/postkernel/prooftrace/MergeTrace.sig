signature MergeTrace =
sig
  (* Merge per-theory traces into a single self-contained trace.
     trace_paths: (theory_name, file_path) pairs for theory traces
     desired_exports: (theory_name, theorem_name) pairs
     output_path: path for the merged trace file

     Heap traces are discovered automatically by following H lines
     in the theory/heap traces. The heap path recorded in H lines
     is resolved to <heap_path>.pft (trying .pft, then uncompressed). *)
  val merge : {
    trace_paths : (string * string) list,
    desired_exports : (string * string) list,
    output_path : string
  } -> unit
end
