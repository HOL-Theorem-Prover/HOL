signature hhSchedule =
sig
  include Abbrev

  datatype event =
      SliceStarted of hhProver.slice
    | SliceDone of hhProver.slice * hhProver.szs * real
    | ProofFound of hhProver.slice * string list
    (* Metis could not replay the list a prover found (the drop-one
       variants that follow are not reported). *)
    | ReplayFailed of hhProver.slice * string list
    | Verified of suggestion
    | ScheduleDone of stop_reason
  and stop_reason = MaxProofs | Timeout | Exhausted | Interrupted
  (* t_recon is the whole reconstruction time, minimisation included;
     t_replay is the CPU time the replay of stac took, on the thread
     running it (smlTimeout.thread_timeout's clock: elsewhere than Linux,
     the lesser of wall and process CPU time). *)
  withtype suggestion =
    {stac : string, tac : tactic, lemmas : string list,
     prover : hhProver.prover, slice : hhProver.slice,
     t_prover : real, t_recon : real, t_replay : real}

  type result =
    {suggestions : suggestion list,
     slices_run : (hhProver.slice * hhProver.szs * real * bool) list,
     stopped : stop_reason, t_total : real}

  (* run_in and export_problems require a root reserved for this invocation.
     with_problem_dir parent options f reserves one below parent, applies f
     to it and then deletes it, also when f raises.  If debug_dir is set in
     options, the root is reserved below debug_dir/problems and kept. *)
  val new_problem_dir : string -> string
  val with_problem_dir :
    string -> hhConfig.hh_options -> (string -> 'a) -> 'a
  val problem_path : string -> hhProver.slice -> string
  val copy_file : string -> string -> int
  (* The ordered work of one export, derived from distinct_problems:
     index, problem path, share key (filter, selected prefix length) and
     kind.  The first legacy item of a share key is exported
     (ExportLegacy); later ones copy the published file it names
     (CopyLegacy path). *)
  datatype kind =
      ExportLegacy
    | CopyLegacy of string
    | ExportGenerated of hhProblemGen.problem_options
  type work =
    {index : int, config : hhProver.prover_config, slice : hhProver.slice,
     path : string, key : string * int, kind : kind}
  val ordered_work : string -> hhConfig.hh_options ->
    (string * string list) list ->
    (hhProver.prover_config * hhProver.slice) list -> work list
  (* run_staged {window} stages works drives each item through
     prepare (caller, in order), submit (at admission; starts the
     finishing work and returns a pending item), await (at resolution, in
     order; returns the staged result) and publish (in order).  See
     hhSchedule.sml for the full contract: the successful prefix is
     published, the exception of the earliest failing index is raised, later
     work is abandoned (abandon for pending items, release for finished
     ones) and admission stops after a failure.  window > 0 exists for the
     bounded workers of a pool-backed submit/await; the inline stages are
     used with window 0.  With a window an observer sees generated events
     at prepare and copied events at publish, so copies are reported after
     later generated events. *)
  val run_staged :
    {window : int} ->
    {prepare : 'w -> 'p, submit : 'w * 'p -> 'q, await : 'q -> 'f,
     publish : 'w * 'f -> unit, abandon : 'q -> unit, release : 'f -> unit} ->
    'w list -> unit
  (* generated and copied report each exported or byte-copied problem. *)
  type export_observer =
    {generated : hhProver.slice -> unit,
     copied : hhProver.slice * int -> unit}
  (* export_problems_observed exports the problems of the schedule, with
     the observer told of each one.  The number of workers that finish the
     generated problems (the tail of the preparation, then format and
     write a private temporary) is min (export_workers, cores, generated
     problems); one means inline, and so does a caller whose context is
     pinned (Context.is_pinned () at the start of the export).  prepare,
     which draws fresh names and uses the memo, the theorem data and the
     caches, stays on the calling thread in schedule order, and the
     files are published in schedule order.  At most as many problems as
     workers wait for resolution (one more briefly), which bounds the
     HOL terms the queued tails retain.  A failure or an interrupt stops
     and waits for the workers and removes their temporaries before it
     propagates.  A worker thread that cannot be started fails the item
     it was for like any other failure of that item (there is no inline
     fallback).  Test hooks are in hhSchedule_Test (hhSchedule.sml).

     Concurrency of the tails.  A tail draws no fresh names and uses no
     shared state of HolyHammer, but it reads the live signature (new
     bound-variable names, constant types) and the TypeBase (the ??
     encoding).  An unpinned caller, which is every batch build and plain
     session, is served by workers that read the live signature as the
     caller would; HolyHammer installs no Context pin of its own.  The
     export never changes the signature, and the pool only widens the
     window in which a tail can overlap a later prepare, so a concurrent
     writer of the signature that exists outside the tree (the language
     server publishes none while a proof replays, and replay is pinned)
     could at worst make an export fail (a constant missing) or produce
     bytes that belong to a slightly different signature.  It cannot cause
     a wrong prover-cache hit, because the cache is keyed on the bytes.

     Failure path.  A failure of a tail at item i is a failure of the
     finishing of i, raised in index order with the same text as the
     caller-side failure would have (a "lambda survived" is converted on
     the calling thread).  Up to as many later items as workers may by then
     have been prepared (more generated events, more memo entries), so a
     later export in the same process differs from the serial one only in
     the fresh-name counter: different generated names, hence possible
     prover-cache misses, never wrong bytes. *)
  val export_problems_observed : export_observer -> string ->
    hhConfig.hh_options -> goal -> (string * string list) list ->
    (hhProver.prover_config * hhProver.slice) list -> unit
  val default_progress : event -> unit
  (* On failure the exception of the earliest failing problem is raised:
     the problems before it stay published, it and the later ones are
     absent and no temporary file is left. *)
  val export_problems : string -> hhConfig.hh_options -> goal ->
    (string * string list) list ->
    (hhProver.prover_config * hhProver.slice) list -> unit
  (* run_in exports the problems of the schedule as export_problems does
     (prepare on the calling thread, the tails on the pool workers), then
     prunes the cache, probes the provers and runs the schedule.  A failure
     or an interrupt before the launch (the export, the prune or the
     probes) propagates with no event and no ScheduleDone.  The lists the
     provers find are replayed on goal in context, the context of the
     proof the run is for.

     The clock.  The timeout bounds the proof search and starts at the
     launch of the provers, after the export.  At the soft deadline no
     slice is started; the slices started keep their grace period, and at
     the hard deadline (soft plus grace) the provers still running are
     killed.  The reconstruction is not bounded by either: every list a
     prover has found is reconstructed, in the order of arrival, so a call
     can return after the timeout.  MaxProofs ends the run whenever
     max_proofs proofs have verified; past the soft deadline the first
     verified proof also ends it (the provers still running are killed,
     the lists still queued dropped), including one verified before the
     deadline.  Until a proof has verified, the reconstruction goes on
     until every list has been reconstructed or has failed.  Each replay
     takes about preplay_timeout at most, with its compilation; a list
     costs about two (the list, then without its permutative equations),
     its minimisation, which stops at the soft deadline and keeps the
     shortest verified list, and the final replay (one more); the lists
     are at most as many as the slices of the schedule.  The retries of
     preplay_drop_one are not found by a prover, and each can cost two
     replays, so they are dropped at the soft deadline.  The run ends with
     MaxProofs if the verified proofs reach max_proofs; otherwise with
     Exhausted if every slice had run before the soft deadline, and with
     Timeout if not, whether or not the reconstruction finds a proof (also
     when a verified proof ended the run past the soft deadline).

     Stops.  MaxProofs and an interrupt of the caller (also during the
     launch) stop the run: the provers are killed (a replay is interrupted
     at once by the interrupt, but not by MaxProofs, which a replay itself
     triggers), and run_in returns only when every thread it forked has
     exited.  The hard deadline only kills the provers, and past the soft
     deadline a verified proof, one verified before it included, ends the
     run without a reason of its own (see the clock). *)
  val run_in : string ->
    {options : hhConfig.hh_options, max_proofs : int, goal : goal,
     context : Context.t,
     rankings : (string * string list) list,
     progress : (event -> unit) option} -> result
  (* The temporary problems of a non-debug run are private to the
     scheduler, which shares cache digests across byte copies. The returned
     path refers to a retained directory only in debug mode. *)
  val run_under : string ->
    {options : hhConfig.hh_options, max_proofs : int, goal : goal,
     context : Context.t,
     rankings : (string * string list) list,
     progress : (event -> unit) option} -> string * result
  (* run uses the default parent and discards the problem directory path. *)
  val run :
    {options : hhConfig.hh_options, max_proofs : int, goal : goal,
     context : Context.t,
     rankings : (string * string list) list,
     progress : (event -> unit) option} -> result
end
