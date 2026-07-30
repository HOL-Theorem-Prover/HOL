signature target_times =
sig

  (* Wall-clock cost data for the parallel scheduler.  Read from and
     merged into <root>/.hol/build-logs/target-times, one line per
     entry, format "<theory-log-key> <secs>" (same key scheme as
     src/postkernel/Theory.sml's thy_log_key, same line format as the
     per-run logs under Systeml.build_log_dir).

     The file records the most-recently-observed time for each key
     across all builds that have run in this project; entries survive
     until overwritten by a later run of the same target. *)

  type map = (string, real) Binarymap.dict

  (* Read the target-times file for the project rooted at `root`, if
     any.  NONE, a missing file, or an unreadable file all yield an
     empty map. *)
  val load : {root : string option} -> map

  (* `theory_cost m fp` = the recorded time for the theory whose
     script's fully-qualified path is `fp`, or 0.0 if unknown.
     Combines `Holmake_tools.rel_to_holdir` with a map lookup. *)
  val theory_cost : map -> string -> real

  (* Merge each (key, secs) entry from `log_path` into
     <root>/.hol/build-logs/target-times, last-observed wins.
     Entries already in target-times but absent from log_path are
     preserved.  Creates <root>/.hol/build-logs/ if needed.  Malformed
     lines in log_path are silently skipped.  I/O errors are swallowed
     with a note on stdErr; a failed merge never derails the build. *)
  val merge_from_log : {root : string, log_path : string} -> unit

end
