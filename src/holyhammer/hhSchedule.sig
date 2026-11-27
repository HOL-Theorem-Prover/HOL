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

  (* run_in and export_problems require a root reserved for this
     invocation: new_problem_dir parent creates a fresh one below parent.
     with_problem_dir parent options f reserves one below parent, applies f
     to it and then deletes it, also when f raises.  If debug_dir is set in
     options, the root is reserved below debug_dir/problems and kept. *)
  val new_problem_dir : string -> string
  val with_problem_dir :
    string -> hhConfig.hh_options -> (string -> 'a) -> 'a
  (* problem_path root slice: the problem file of slice below root. *)
  val problem_path : string -> hhProver.slice -> string
  (* copy_file source destination copies source over destination as
     hhConfig.write_atomically writes, and returns the byte count. *)
  val copy_file : string -> string -> int
  (* ordered_work root options rankings schedule: the ordered work of one
     export, one item per distinct problem file in schedule order, with
     its index, problem path, share key (filter, selected prefix length)
     and kind.  The first legacy item of a share key is exported
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
  (* run_staged {window} stages works drives each item w through
       prepare w       on the caller, in order;
       submit (w, p)   at admission: starts the item's finishing work and
                       returns it as a pending item q;
       await q         at resolution, in order: waits for q and returns
                       what it staged, f;
       publish (w, f)  in order, on the caller.
     The finishing work may run inside await (window 0) or on a worker
     started by submit.  submit, await and publish each clean up what
     they were given or staged when they fail.  abandon q cancels a
     pending item (waiting for its work to stop) and removes what it
     staged; release f removes what a finished item staged; both are
     idempotent and are applied to every item that is dropped.

     Up to window admitted items wait while later ones are prepared; with
     window 0 each item is published before the next is prepared.  A
     failed stage stops admission: the items admitted before the failing
     index are resolved, the successful prefix is published and the
     exception of the earliest failing index is raised.  An interrupt
     drops all waiting work and propagates. *)
  val run_staged :
    {window : int} ->
    {prepare : 'w -> 'p, submit : 'w * 'p -> 'q, await : 'q -> 'f,
     publish : 'w * 'f -> unit, abandon : 'q -> unit, release : 'f -> unit} ->
    'w list -> unit
  (* generated and copied report each exported or byte-copied problem. *)
  type export_observer =
    {generated : hhProver.slice -> unit,
     copied : hhProver.slice * int -> unit}
  (* export_problems_observed observer root options goal rankings schedule
     writes the problems of the schedule below root, with observer told of
     each.  prepare, which draws fresh names and uses the memo, the
     theorem data and the caches, runs on the calling thread in schedule
     order, and the files are published in schedule order.  The tails of
     the generated problems (the end of their preparation, then format and
     write to a private temporary) run on min (export_workers, cores,
     generated problems) workers, inline if that is one or if the
     caller's context is pinned (Context.is_pinned () at the start of the
     export).  At most as many problems as workers wait for resolution
     (one more briefly), which bounds the HOL terms the queued tails
     retain.  The observer sees a generated event at prepare and a copied
     one at publish, so with workers copies are reported after later
     generated events.  A failure or an interrupt stops and waits for the
     workers and removes their temporaries before it propagates; a worker
     thread that cannot be started fails its item.  Test hooks are in
     hhSchedule_Test (hhSchedule.sml).

     Concurrency of the tails.  A tail draws no fresh names and uses no
     shared state of HolyHammer, but it reads the live signature (new
     bound-variable names, constant types) and the TypeBase (the ??
     encoding).  HolyHammer installs no Context pin, and the export never
     changes the signature, so only a concurrent writer of the signature
     outside HolyHammer (the language server publishes none while a proof
     replays, and replay is pinned) could make an export fail (a constant
     missing) or produce bytes of a slightly different signature.  It
     cannot cause a wrong prover-cache hit: the cache is keyed on the
     bytes.

     Failure path.  A tail's failure at item i is raised in index order
     with the text the caller-side failure would have (a "lambda survived"
     is converted on the calling thread).  By then up to as many later
     items as workers may have been prepared (more generated events and
     memo entries), so a later export in the same process differs from
     the serial one only in the fresh-name counter: different generated
     names, hence possible prover-cache misses, never wrong bytes. *)
  val export_problems_observed : export_observer -> string ->
    hhConfig.hh_options -> goal -> (string * string list) list ->
    (hhProver.prover_config * hhProver.slice) list -> unit
  (* Prints an event: the progress of a run given no progress function. *)
  val default_progress : event -> unit
  (* export_problems_observed with no observer.  On failure the exception
     of the earliest failing problem is raised: the problems before it
     stay published, it and the later ones are absent and no temporary
     file is left. *)
  val export_problems : string -> hhConfig.hh_options -> goal ->
    (string * string list) list ->
    (hhProver.prover_config * hhProver.slice) list -> unit
  (* run_in root request exports the problems of the schedule below root
     as export_problems does, then prunes the cache, probes the provers
     and runs the schedule.  A failure or an interrupt before the launch
     (the export, the prune or the probes) propagates with no event and
     no ScheduleDone.  The lists the provers find are replayed on goal in
     context, the context of the proof the run is for.

     The clock.  The timeout bounds the proof search and starts at the
     launch of the provers, after the export.  At the soft deadline no
     slice is started; the slices started keep their grace period, and at
     the hard deadline (soft plus grace) the provers still running are
     killed.  Neither deadline bounds the reconstruction: the lists the
     provers find are reconstructed in order of arrival until the run
     ends, so a call can return after the timeout.  Each replay takes
     about preplay_timeout at most, with its compilation; a list costs
     about two (the list, then without its permutative equations), its
     minimisation, which stops at the soft deadline and keeps the
     shortest verified list, and the final replay; the lists are at most
     as many as the slices.  The retries of preplay_drop_one are not
     found by a prover, and each can cost two replays, so they are
     dropped at the soft deadline.

     Stops.  The run ends when max_proofs proofs have verified
     (MaxProofs), when the caller is interrupted, also during the launch
     (Interrupted), past the soft deadline once a proof has verified (one
     verified before it included), and otherwise once the search is over
     and every list has been reconstructed or has failed.  An end kills
     the provers and drops the queued lists; an interrupt also interrupts
     a replay at once, MaxProofs (which a replay triggers) does not.  Not
     ended by MaxProofs or an interrupt, the run reports Exhausted if
     every slice had run before the soft deadline and Timeout if not,
     whether or not a proof verified.  run_in returns only when every
     thread it forked has exited. *)
  val run_in : string ->
    {options : hhConfig.hh_options, max_proofs : int, goal : goal,
     context : Context.t,
     rankings : (string * string list) list,
     progress : (event -> unit) option} -> result
  (* run_under parent request: run_in in a root that with_problem_dir
     reserves below parent, with that root.  The problems of a non-debug
     run are private to the scheduler, which then shares cache digests
     across byte copies; the root survives the call only in debug mode. *)
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
