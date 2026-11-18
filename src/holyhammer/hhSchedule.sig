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
  (* generated and copied report each exported or byte-copied problem. *)
  (* The ordered work of one export, derived from distinct_problems:
     index, problem path, share key (filter, selected prefix length) and
     kind.  The first legacy item of a share key exports; later ones copy
     the published file named in Legacy (SOME path). *)
  datatype kind =
      Legacy of string option
    | Generated of hhProblemGen.problem_options
  type work =
    {index : int, config : hhProver.prover_config, slice : hhProver.slice,
     path : string, key : string * int, kind : kind}
  val ordered_work : string -> hhConfig.hh_options ->
    (string * string list) list ->
    (hhProver.prover_config * hhProver.slice) list -> work list
  (* run_staged {window} {prepare, finish, publish, discard} works runs
     prepare in order on the caller, then finish and publish in order,
     keeping at most window prepared items waiting.  On failure it stops
     admitting work, publishes the successful prefix and raises the
     exception of the earliest failing index.  finish and publish clean up
     what they staged when they fail; discard releases dropped prepared
     items. *)
  val run_staged :
    {window : int} ->
    {prepare : 'w -> 'p, finish : 'w * 'p -> 'f, publish : 'w * 'f -> unit,
     discard : 'p -> unit} -> 'w list -> unit
  type export_observer =
    {generated : hhProver.slice -> unit,
     copied : hhProver.slice * int -> unit}
  val export_problems_observed : export_observer -> string ->
    hhConfig.hh_options -> goal -> (string * string list) list ->
    (hhProver.prover_config * hhProver.slice) list -> unit
  val default_progress : event -> unit
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
