signature hhEval =
sig
  datatype regime = Bushy | Chainy
  datatype selector =
      Deps
    | Knn of int
    | Mepo of int
    | Mash of int
    | Mesh of int
    | PerSlice
  datatype engine =
      Prover of hhProver.prover
    | Sched of {provers : hhProver.prover list, slices : int,
                cores : int, max_proofs : int,
                export_workers : int}

  (* cond_id names the condition in journals and in run.json. *)
  type condition =
    {cond_id : string, regime : regime, selector : selector,
     engine : engine, timeout : int, reconstruct : bool}

  (* What a journal cell recorded: the prover's SZS verdict, or why no
     prover verdict exists. *)
  datatype cell_status =
      Szs of hhProver.szs
    | EvalError
    | BrokenDeps
    | LoadFailure

  type journal_slice =
    {slice : hhProver.slice, szs : hhProver.szs, time : real,
     cached : bool}

  (* engine and prover are NONE for the entry of a theory that failed to
     load.  A Sched entry's prover is that of the slice it reports on, and
     NONE if no slice ran. *)
  type journal_entry =
    {run : string, thy : string, thm : string, goal_id : string,
     cond : string, regime : regime, selector : selector,
     engine : engine option, ho : bool, fresh : bool,
     prover : hhProver.prover option,
     prover_version : string option, nfacts : int,
     timeout : int, szs : cell_status, t_prover : real,
     axioms_used : string list option, recon_ok : bool option,
     recon_method : string option, t_recon : real option,
     stac : string option, error : string option, stop : string option,
     t_total : real option, winner : hhProver.slice option,
     slices : journal_slice list}

  type corpus_coverage =
    {srcfiles : string list, dat_theories : string list,
     added_from_dat : string list}

  type corpus_entry =
    {thy : string, theorem_count : int, dep_stamp : string}

  type prover_identity =
    {prover : hhProver.prover, path : string option, version : string option,
     sha256 : string option}

  type run_header =
    {expname : string, date : string, host : string, hol_commit : string,
     provers : prover_identity list, corpus : corpus_entry list,
     added_from_dat : string list, conditions : condition list, sample : int}

  type completed

  val string_of_regime : regime -> string
  val string_of_selector : selector -> string
  (* Classifiers of a goal term, beta-eta-contracted.
     is_higher_order_goal holds when it applies a bound function variable
     or has an abstraction, quantifier or connective in term position;
     is_fresh_goal thy when it mentions a constant of theory thy. *)
  val is_higher_order_goal : Term.term -> bool
  val is_fresh_goal : string -> Term.term -> bool
  (* Raises Fail for a Prover condition with PerSlice, a Sched condition
     with a MePo, MaSh or MeSh selector or without reconstruction, and
     Sched parameters out of range. *)
  val validate_condition : condition -> unit
  val encode_condition : condition -> string
  val parse_condition : string -> condition

  (* The theories that $HOLDIR/sigobj/SRCFILES lists (HOLDIR defaulting
     to that of the build), and those with a Theory.dat under $HOLDIR/src
     that it lacks (added_from_dat).  stdlib_theories is their union, and
     warns on stderr when added_from_dat is not empty. *)
  val stdlib_coverage : unit -> corpus_coverage
  val stdlib_theories : unit -> string list

  (* experiment_dir name is below the configuration key eval.dir, by
     default $HOLDIR/src/holyhammer/eval.  journal_path expdir thy is
     expdir/journal/thy.jsonl. *)
  val experiment_dir : string -> string
  val journal_path : string -> string -> string

  (* read_journal gives the entries of a journal in file order, none for a
     missing file.  A line that is not JSON (one torn by an interrupted
     worker) is skipped; a JSON line that is not an entry raises Fail. *)
  val encode_journal_line : journal_entry -> string
  val parse_journal_line : string -> journal_entry
  val append_journal : string -> journal_entry -> unit
  val read_journal : string -> journal_entry list

  (* The (goal_id, cond_id) cells a journal records, except those with
     EvalError or RunFailure status, which a resume runs again. *)
  val read_completed : string -> completed
  val cell_completed : completed -> string * string -> bool
  val journal_complete : string -> (string * string) list -> bool

  (* report expdir writes expdir/report.md and expdir/summary.json from
     the latest entry of each cell of the journals, load failures
     excluded. *)
  val report : string -> unit

  (* The rows whose name is in the pool, in their order. *)
  val restrict_features_to_pool :
    string list -> (string * 'a) list -> (string * 'a) list

  (* Query the union of ancestor facts and local facts whose oldest age is
     strictly before the given goal age.  Reuse the query within one worker. *)
  val chainy_pool_by_age :
    (string, unit) Redblackmap.dict -> (string, int) Redblackmap.dict ->
    int -> (string, unit) Redblackmap.dict

  (* new_run_header adds the date, the host, the HOL commit and the
     identities of the provers of the conditions.  validate_run_header
     expdir header raises Fail unless expdir/run.json has the schema,
     expname, conditions, sample and corpus of header, and the current
     hammer options. *)
  val loaded_corpus_entry : string -> corpus_entry
  val new_run_header :
    {expname : string, corpus : corpus_entry list,
     added_from_dat : string list, conditions : condition list,
     sample : int} -> run_header
  val write_run_header : string -> run_header -> unit
  val validate_run_header : string -> run_header -> unit

  (* sample_goal n goal_id selects about one goal in n, by a hash of
     goal_id. *)
  val sample_goal : int -> string -> bool

  (* The worker side.  write_evalscript expdir thy conditions sample writes
     the worker script of thy, at evalscript_path expdir thy in the
     theory's source directory, and returns its path; the script applies
     the current hammer options, set_worker_settings and eval_thy, which
     appends the pending cells of the loaded theory thy to its journal. *)
  val set_worker_settings : {conditions : condition list, sample : int} -> unit
  val evalscript_path : string -> string -> string
  val write_evalscript : string -> string -> condition list -> int -> string
  val eval_thy : string -> string -> unit
  (* Evaluates the pending cells of thyl in ncore worker processes, one
     per theory, largest first, sampling by eval.sample.  A Sched cell
     runs cores prover processes, so size ncore to the machine's cores
     divided by cores: the peak load is ncore * cores. *)
  val run_eval :
    {expname : string, ncore : int, thyl : string list,
     conditions : condition list} -> unit

end
