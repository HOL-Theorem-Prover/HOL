signature target_times =
sig

  (* Cost data for the parallel scheduler, in child CPU seconds --
     what `ProcessMultiplexor' measures for each job it runs, and hands
     to that job's `update'.  Holmake records every job it runs,
     theories included; `Theory.sml' still reports and logs its own
     proof times, but nothing here reads them.

     Two sources, presented as one map:

       * <root>/.hol/build-logs/target-times, the project's own cache,
         rewritten by every parallel Holmake run in that project;
       * zero or more committed *seed* files, which a project ships so
         that a fresh checkout -- where no cache exists yet -- still
         schedules well.  `HMProject.build_times_files' finds them.

     One format for both: one line per entry, "<key> <secs>", with `#'
     comments and malformed lines skipped.  Keys are as
     `HM_DepGraph.cost_key' builds them, so they are relative to the
     governing project root and portable between checkouts.

     A cache entry always beats a seed entry for the same key: a seed
     is a floor, local measurement is the truth.  Seeds are read-only
     and are never written back into the cache.

     Only parallel builds record: `HM_GraphBuildJ1' (-j1) times
     nothing.  Holmake's default is -j4 and `bin/build' passes -j
     through, so in practice every build contributes. *)

  type map = (string, real) Binarymap.dict

  (* `load {root}` - the seeds `HMProject.build_times_files' names for
     `root`, with the project's own cache folded over the top so local
     entries win per key.  A file that is missing or unreadable
     contributes nothing, and `root = NONE` contributes no cache;
     neither is an error. *)
  val load : {root : string option} -> map

  (* As `load', over seeds named outright rather than looked up.  Only
     the tests want this: they must not depend on which seeds happen to
     be committed in the tree they run inside. *)
  val load_seeds : {seeds : string list, root : string option} -> map

  (* `cost m k` = the recorded time for key `k`, or 0.0 if unknown.
     Unknown scoring 0.0 is what makes a checkout with no data at all
     behave exactly as it did before HLFET: every cp_weight is 0.0 and
     `find_best_runnable_pred' ties on node id. *)
  val cost : map -> string -> real

  (* Merge `entries` into <root>/.hol/build-logs/target-times,
     last-observed wins, preserving entries this run did not touch.
     Creates the directory if needed.  I/O errors are swallowed with a
     note on stdErr; a failed merge never derails the build.

     Writes the cache and only the cache -- never a seed, and never
     seed values that came back through `load'. *)
  val merge_entries : {root : string,
                       entries : (string * real) list} -> unit

end
