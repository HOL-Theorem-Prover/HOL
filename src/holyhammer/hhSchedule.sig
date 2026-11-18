signature hhSchedule =
sig
  include Abbrev

  datatype event =
      SliceStarted of hhProver.slice
    | SliceDone of hhProver.slice * hhProver.szs * real
    | ProofFound of hhProver.slice * string list
    | Verified of suggestion
    | ScheduleDone of stop_reason
  and stop_reason = MaxProofs | Timeout | Exhausted | Interrupted
  (* t_recon is the whole reconstruction time, minimisation included;
     t_replay is the time the replay of stac took. *)
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
  (* export_problems_using {fork} is export_problems_observed with the
     function that starts the worker threads of the pool (the default is
     hhPool.default_fork) and a function that a worker applies to the index
     of its item before it finishes it (the default does nothing; a test
     hook).  The number of workers is min (export_workers,
     cores, generated problems); one means inline.  prepare, which draws
     fresh names and touches HOL state, stays on the calling thread in
     schedule order, workers only format and write private temporaries, and
     the files are published in schedule order.  A failure or an interrupt
     stops and waits for the workers and removes their temporaries before
     it propagates. *)
  val export_problems_using :
    {fork : hhPool.fork, before_finish : int -> unit} -> export_observer ->
    string -> hhConfig.hh_options -> goal -> (string * string list) list ->
    (hhProver.prover_config * hhProver.slice) list -> unit
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
  val run_in : string ->
    {options : hhConfig.hh_options, goal : goal,
     rankings : (string * string list) list,
     progress : (event -> unit) option} -> result
  val run :
    {options : hhConfig.hh_options, goal : goal,
     rankings : (string * string list) list,
     progress : (event -> unit) option} -> result
end
